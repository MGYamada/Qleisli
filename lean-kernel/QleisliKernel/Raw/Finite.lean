import QleisliKernel.Raw.Trace

/-! VM-25 finite semantics reconstructed from actual pure raw bodies.
The general structural checker retains twelve-bit registers. Dense semantic
inspection is the existing six-bit finite profile, not a production restriction.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw
open Semantics.Exact Semantics.Finite Semantics.Raw Finite

def registerBasis := Semantics.Raw.registerBasis

def circuit (bits : Nat) (steps : List Step) : Circuit := ⟨registerBasis bits,steps⟩

def mapping (inputBits outputBits : Nat) (labels : List Nat) : WorkM Matrix := do
  guard (inputBits ≤ 6 && outputBits ≤ 6) .limit
  guard (tableValid inputBits outputBits labels true)
  let rows := 2^outputBits
  let cols := 2^inputBits
  exactWork (Exact.charge (rows * cols))
  lift (arithmetic (Exact.Matrix.make rows cols ((List.range (rows*cols)).map fun index =>
    if labels[index % cols]? == some (index / cols) then Scalar.one else Scalar.zero)))

def zeroEncoding (dataBits ancillaBits : Nat) : WorkM Encoding := do
  let map ← mapping dataBits (dataBits+ancillaBits) (List.range (2^dataBits))
  return ⟨registerBasis dataBits,registerBasis (dataBits+ancillaBits),map⟩

def computeStep := Semantics.Raw.computeStep

/-- Actual init; compute; use; inverse compute is checked against the zero
encoding. The logical circuit is independently reconstructed, not assumed.
Thus rows with any dirty auxiliary amplitude cause rejection before release. -/
def clean (dependencies : List Dependency) (sourceBits dataBits ancillaBits : Nat)
    (function : List Nat) (useSteps logicalSteps : List Step) : WorkM Matrix := do
  guard (sourceBits ≤ dataBits && dataBits+ancillaBits ≤ 6) .limit
  guard (tableValid sourceBits ancillaBits function false)
  let logical ← circuitMatrix dependencies (circuit dataBits logicalSteps)
  wholeSpace logical
  let encoding ← zeroEncoding dataBits ancillaBits
  let contract : Contract := ⟨encoding,encoding,logical⟩
  let compute := computeStep sourceBits dataBits ancillaBits function
  let actual ← check dependencies (circuit (dataBits+ancillaBits) ([compute] ++ useSteps ++ [compute])) contract contract
  wholeSpace actual
  return logical

def promote (bits : Nat) (axes : List Nat) (matrix : Matrix) : WorkM Matrix := do
  guard (bits ≤ 6 && Finite.axesValid bits axes && matrix.rows == 2^axes.length && matrix.cols == matrix.rows)
  let dimension := 2^bits
  exactWork (Exact.charge (dimension*dimension))
  lift (arithmetic (Exact.Matrix.make dimension dimension ((List.range (dimension*dimension)).map fun index =>
    let row := index / dimension
    let col := index % dimension
    if scatter col axes (gather row axes) == row then matrix.entry (gather row axes) (gather col axes) else Scalar.zero)))

def eventMatrix (dependencies : List Dependency) (event : Event) : WorkM Matrix := do
  match event with
  | .circuit bits steps =>
    guard (bits ≤ 6) .limit
    circuitMatrix dependencies (circuit bits steps)
  | .init0 bits =>
    guard (bits < 6) .limit
    mapping bits (bits+1) (List.range (2^bits))
  | .liftBasis before after inputAxes outputAxes table =>
    guard (before ≤ 6 && after ≤ 6) .limit
    mapping before after ((List.range (2^before)).map fun label =>
      scatter label outputAxes (table[gather label inputAxes]?.getD 0))
  | .reorder bits axes =>
    guard (bits ≤ 6) .limit
    mapping bits bits ((List.range (2^bits)).map fun label => gather label axes)
  | .computed bits axes sourceBits ancillaBits function useSteps logicalSteps =>
    guard (bits ≤ 6) .limit
    let logical ← clean dependencies sourceBits axes.length ancillaBits function useSteps logicalSteps
    promote bits axes logical
  | .protectedComputed bits axes sourceBits ancillaBits function uses =>
    -- Reject the finite profile before expanding the source-label/usage product.
    -- Structural prepare keeps the original uses even for twelve-bit owners.
    guard (bits ≤ 6 && sourceBits ≤ axes.length && axes.length+ancillaBits ≤ 6) .limit
    guard (tableValid sourceBits ancillaBits function false)
    let logical ← clean dependencies sourceBits axes.length ancillaBits function
      (uses.map (physicalUse sourceBits axes.length)) (uses.flatMap (logicalUse sourceBits function))
    promote bits axes logical

def evolve (dependencies : List Dependency) (actual : Matrix) (event : Event) : WorkM Matrix := do
  let next ← eventMatrix dependencies event
  exactWork (Exact.Matrix.composeWork next actual)

def rawFields (program : Program) : Nat :=
  program.inputs.length + (program.inputs.map (fun port => port.wires.length)).sum +
    program.outputs.length + program.operations.length +
    (program.operations.map fun op => match op with
      | .applyUnitary _ _ steps => steps.length
      | .certifiedCompute _ _ ancilla function useSteps logicalSteps =>
        ancilla.length + function.length + useSteps.length + logicalSteps.length
      | .computeUseUncompute _ _ targets ancilla function uses =>
        2*targets.length + ancilla.length + function.length + uses.length
      | .quantumIf _ _ _ _ zero one => zero.length + one.length
      | .liftBasis _ _ wires table => wires.length + table.length
      | _ => 0).sum

/-- No caller-supplied extracted steps, result matrix or acceptance receipt. -/
def reconstruct (dependencies : List Dependency) (program : Program) : WorkM Matrix := do
  exactWork (Exact.charge (rawFields program))
  let prepared ← lift (prepare (dependencies.map (·.signature)) program)
  guard (prepared.inputBits ≤ 6 && prepared.state.frame.length ≤ 6) .limit
  let initial ← lift (arithmetic (Exact.Matrix.identity (2^prepared.inputBits)))
  let actual ← prepared.events.foldlM (evolve dependencies) initial
  let isometry ← exactWork (Exact.Matrix.isometryWork actual)
  guard isometry .notIsometric
  return actual

def unary (signature : Basis) (program : Program) : Bool :=
  Finite.basisValid signature && program.effect == .unitary && program.inputs.length == 1 &&
  program.outputs.length == 1 &&
  ((program.inputs[0]?).map (fun port => port.bits == width signature)).getD false

structure Cache where
  dependencies : List Dependency := []
  heights : List Nat := []
  deriving Repr

def programReferences (program : Program) : List Nat := program.operations.flatMap fun op =>
  let steps := match op with
    | .applyUnitary _ _ steps => steps
    | .certifiedCompute _ _ _ _ useSteps logicalSteps => useSteps ++ logicalSteps
    | _ => []
  steps.filterMap fun step => match step.action with | .contract _ index _ => some index | _ => none

/-- Dependencies are only the freshly checked prefix of original raw bodies.
Forward/cyclic references cannot be found in the signatures or matrix cache. -/
def evidenceEntry (cache : Cache) (evidence : Semantics.Raw.Evidence) : WorkM Cache := do
  guard (unary evidence.signature evidence.implementation && unary evidence.signature evidence.specification)
  let actual ← reconstruct cache.dependencies evidence.implementation
  let specified ← reconstruct cache.dependencies evidence.specification
  guard (actual == specified) .equation
  wholeSpace actual
  let refs := programReferences evidence.implementation ++ programReferences evidence.specification
  let height := 1 + (refs.map (fun index => cache.heights[index]?.getD 0)).foldl max 0
  guard (height ≤ 32) .limit
  return ⟨cache.dependencies ++ [⟨evidence.signature,actual⟩],cache.heights ++ [height]⟩

/-- Standalone VM-25 inspection with an independent required matrix. Ordinary
validity checking uses reconstruct and does not acquire an algorithm request. -/
def inspect (evidence : List Semantics.Raw.Evidence) (program : Program) (required : Matrix) : WorkM Matrix := do
  guard (evidence.length ≤ 65536) .limit
  let cache ← evidence.foldlM evidenceEntry {}
  let required ← matrixRead required
  let actual ← reconstruct cache.dependencies program
  guard (actual == required) .request
  return actual

theorem clean_conditions (dependencies : List Dependency) (sourceBits dataBits ancillaBits : Nat)
    (function : List Nat) (useSteps logicalSteps : List Step) (logical : Matrix) (work left : Nat)
    (ok : (clean dependencies sourceBits dataBits ancillaBits function useSteps logicalSteps).run work = (.ok logical,left)) :
    ∃ encoding physical w₁ w₂ w₃ w₄ w₅ w₆,
      (circuitMatrix dependencies (circuit dataBits logicalSteps)).run w₁ = (.ok logical,w₂) ∧
      (zeroEncoding dataBits ancillaBits).run w₃ = (.ok encoding,w₄) ∧
      (check dependencies (circuit (dataBits+ancillaBits)
        ([computeStep sourceBits dataBits ancillaBits function] ++ useSteps ++
          [computeStep sourceBits dataBits ancillaBits function]))
        ⟨encoding,encoding,logical⟩ ⟨encoding,encoding,logical⟩).run w₅ = (.ok physical,w₆) := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨logical,w₃,hl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨encoding,w₅,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨physical,w₆,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst_vars
  exact ⟨encoding,physical,w₂,w₃,w₄,w₅,w₅,w₆,hl,he,hp⟩

theorem mapping_value (inputBits outputBits : Nat) (labels : List Nat) (actual : Matrix) (work left : Nat)
    (ok : (mapping inputBits outputBits labels).run work = (.ok actual,left)) :
    actual = ⟨2^outputBits,2^inputBits,((List.range (2^outputBits * 2^inputBits)).map fun index =>
      if labels[index % 2^inputBits]? == some (index / 2^inputBits) then Scalar.one else Scalar.zero)⟩ := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  exact (Exact.matrix_make_value _ _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ h).1)).1

/-- Embedding a local map keeps every spectator coordinate and the original
ordered local axes, including the empty-axis scalar case. -/
theorem promote_value (bits : Nat) (axes : List Nat) (logical actual : Matrix) (work left : Nat)
    (ok : (promote bits axes logical).run work = (.ok actual,left)) :
    actual = ⟨2^bits,2^bits,((List.range (2^bits * 2^bits)).map fun index =>
      if scatter (index % 2^bits) axes (gather (index / 2^bits) axes) == index / 2^bits then
        logical.entry (gather (index / 2^bits) axes) (gather (index % 2^bits) axes)
      else Scalar.zero)⟩ := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  exact (Exact.matrix_make_value _ _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ h).1)).1

theorem evolve_conditions (dependencies : List Dependency) (input output : Matrix) (event : Event) (work left : Nat)
    (ok : (evolve dependencies input event).run work = (.ok output,left)) :
    ∃ actual middle, (eventMatrix dependencies event).run work = (.ok actual,middle) ∧
      Exact.Matrix.compose actual input middle = (.ok output,left) := by
  obtain ⟨actual,middle,ha,h⟩ := bind_success _ _ _ _ _ ok
  exact ⟨actual,middle,ha,exactWork_success _ _ _ _ h⟩

theorem zeroEncoding_value (dataBits ancillaBits : Nat) (encoding : Encoding) (work left : Nat)
    (ok : (zeroEncoding dataBits ancillaBits).run work = (.ok encoding,left)) :
    encoding.logical = registerBasis dataBits ∧ encoding.physical = registerBasis (dataBits+ancillaBits) ∧
    ∃ before after, (mapping dataBits (dataBits+ancillaBits) (List.range (2^dataBits))).run before = (.ok encoding.map,after) := by
  obtain ⟨map,middle,hm,h⟩ := bind_success _ _ _ _ _ ok
  have same := (pure_success _ _ _ _ h).1
  subst encoding
  exact ⟨rfl,rfl,work,middle,hm⟩

theorem evidenceEntry_conditions (cache result : Cache) (evidence : Semantics.Raw.Evidence) (work left : Nat)
    (ok : (evidenceEntry cache evidence).run work = (.ok result,left)) :
    ∃ actual a b c d,
      (reconstruct cache.dependencies evidence.implementation).run a = (.ok actual,b) ∧
      (reconstruct cache.dependencies evidence.specification).run c = (.ok actual,d) ∧
      result.dependencies = cache.dependencies ++ [⟨evidence.signature,actual⟩] := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨actual,w₂,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨specified,w₃,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  have equal := beq_iff_eq.mp (guard_success _ _ _ _ he).1
  subst_vars
  exact ⟨specified,w₁,w₂,w₂,w₃,hi,hs,rfl⟩

theorem reconstruct_conditions (dependencies : List Dependency) (program : Program)
    (actual : Matrix) (work left : Nat)
    (ok : (reconstruct dependencies program).run work = (.ok actual,left)) :
    ∃ prepared initial w₁ w₂ w₃ w₄,
      prepare (dependencies.map (·.signature)) program = .ok prepared ∧
      Exact.Matrix.identity (2^prepared.inputBits) = .ok initial ∧
      (prepared.events.foldlM (evolve dependencies) initial).run w₁ = (.ok actual,w₂) ∧
      Exact.Matrix.isometry actual w₃ = (.ok true,w₄) := by
  obtain ⟨_,w₀,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨prepared,w₁,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,w₃,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₄,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨iso,w₅,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  have good := (guard_success _ _ _ _ hg).1
  subst_vars
  exact ⟨prepared,initial,w₃,w₄,w₄,w₅,(lift_success _ _ _ _ hp).1,
    arithmetic_success _ _ (lift_success _ _ _ _ hi).1,ha,exactWork_success _ _ _ _ hs⟩

/-- Bounded evaluation consumes exactly the independently read original trace.
The event list and final axis order are justified by every constructor proof,
not assumed from a producer or from the executable preparation alone. -/
theorem reconstruct_original (dependencies : List Dependency) (program : Program)
    (actual : Matrix) (work left : Nat)
    (ok : (reconstruct dependencies program).run work = (.ok actual,left)) :
    ∃ (trace : Semantics.RawTrace.Prepared) (initial : Matrix) (w₁ w₂ w₃ w₄ : Nat),
      Semantics.RawTrace.run program = some trace ∧
      Exact.Matrix.identity (2^trace.inputBits) = .ok initial ∧
      (trace.events.foldlM (evolve dependencies) initial).run w₁ = (.ok actual,w₂) ∧
      Exact.Matrix.isometry actual w₃ = (.ok true,w₄) := by
  rcases reconstruct_conditions _ _ _ _ _ ok with ⟨prepared,initial,w₁,w₂,w₃,w₄,hp,hi,he,hs⟩
  exact ⟨prepared.reference,initial,w₁,w₂,w₃,w₄,prepare_reference _ _ _ hp,hi,he,hs⟩

theorem events_input_dimension (dependencies : List Dependency) (events : List Event)
    (initial actual : Matrix) (work left : Nat)
    (ok : (events.foldlM (evolve dependencies) initial).run work = (.ok actual,left)) :
    actual.cols = initial.cols := by
  induction events generalizing initial work with
  | nil =>
    simp only [List.foldlM_nil] at ok
    rw [(pure_success _ _ _ _ ok).1]
  | cons event events ih =>
    simp only [List.foldlM_cons] at ok
    rcases bind_success _ _ _ _ _ ok with ⟨next,middle,hn,he⟩
    rcases evolve_conditions _ _ _ _ _ _ hn with ⟨action,before,_,hc⟩
    exact (ih next middle he).trans (Exact.compose_shape _ _ _ _ _ hc).2

/-- Composition cannot change the original input space while processing the
independently read raw trace. This includes zero-width quantum owners. -/
theorem reconstruct_input_dimension (dependencies : List Dependency) (program : Program)
    (actual : Matrix) (work left : Nat)
    (ok : (reconstruct dependencies program).run work = (.ok actual,left)) :
    ∃ trace, Semantics.RawTrace.run program = some trace ∧ actual.cols = 2^trace.inputBits := by
  rcases reconstruct_original _ _ _ _ _ ok with ⟨trace,initial,w₁,w₂,w₃,w₄,hr,hi,he,_⟩
  have initial_cols : initial.cols = 2^trace.inputBits := by
    unfold Exact.Matrix.identity at hi
    split at hi
    · cases hi
    · exact congrArg Matrix.cols (Exact.matrix_make_value _ _ _ _ hi).1
  refine ⟨trace,hr,?_⟩
  exact (events_input_dimension _ _ _ _ _ _ he).trans initial_cols

/-- The original output interface fixes the final matrix space; the explicit
last permutation cannot silently drop axes or replace an empty output owner. -/
theorem reconstruct_output_dimension (dependencies : List Dependency) (program : Program)
    (actual : Matrix) (work left : Nat)
    (ok : (reconstruct dependencies program).run work = (.ok actual,left)) :
    ∃ trace, Semantics.RawTrace.run program = some trace ∧ actual.rows = 2^trace.state.frame.length := by
  rcases reconstruct_original _ _ _ _ _ ok with ⟨trace,initial,w₁,w₂,w₃,w₄,hr,_,he,_⟩
  obtain ⟨body,hb⟩ : ∃ body, trace = Semantics.RawTrace.finish program body := by
    unfold Semantics.RawTrace.run at hr
    cases h : program.operations.foldlM Semantics.RawTrace.advance
        ⟨Semantics.RawTrace.initial program.inputs,[],(Semantics.RawTrace.initial program.inputs).frame.length⟩ with
    | none => simp [h] at hr
    | some body =>
      simp [h] at hr
      exact ⟨body,hr.symm⟩
  subst trace
  simp only [Semantics.RawTrace.finish,List.foldlM_append] at he
  rcases bind_success _ _ _ _ _ he with ⟨before,middle,_,he⟩
  simp only [List.foldlM_cons,List.foldlM_nil] at he
  rcases bind_success _ _ _ _ _ he with ⟨output,beforeReorder,hreorder,houtput⟩
  have same := (pure_success _ _ _ _ houtput).1
  subst output
  rcases evolve_conditions _ _ _ _ _ _ hreorder with ⟨reorder,afterGuard,hm,hc⟩
  rcases bind_success _ _ _ _ _ hm with ⟨_,beforeMapping,_,hm⟩
  have rows := congrArg Matrix.rows (mapping_value _ _ _ _ _ _ hm)
  exact ⟨_,hr,(Exact.compose_shape _ _ _ _ _ hc).1.trans rows⟩

theorem inspect_conditions (evidence : List Semantics.Raw.Evidence) (program : Program) (required actual : Matrix)
    (work left : Nat) (ok : (inspect evidence program required).run work = (.ok actual,left)) :
    actual = required ∧ ∃ (cache : Cache) (before after : Nat),
      (reconstruct cache.dependencies program).run before = (.ok actual,after) := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨cache,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨required,w₃,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₄,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  have req := (matrixRead_value _ _ _ _ hr).1
  have eq := beq_iff_eq.mp (guard_success _ _ _ _ hg).1
  subst_vars
  exact ⟨rfl,cache,w₃,w₄,ha⟩

/-- Expose the complete fresh body-checking pass, not just a cached dependency
matrix. This is the integration entry point's actual acceptance hypothesis. -/
theorem inspect_fresh (evidence : List Semantics.Raw.Evidence) (program : Program) (required actual : Matrix)
    (work left : Nat) (ok : (inspect evidence program required).run work = (.ok actual,left)) :
    actual = required ∧ ∃ (cache : Cache) (w₁ w₂ w₃ w₄ : Nat),
      (evidence.foldlM evidenceEntry {}).run w₁ = (.ok cache,w₂) ∧
      (reconstruct cache.dependencies program).run w₃ = (.ok actual,w₄) := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨cache,w₂,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨read,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₄,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  exact ⟨(inspect_conditions _ _ _ _ _ _ ok).1,cache,w₁,w₂,w₃,w₄,hc,ha⟩

end QleisliKernel.Raw
