import Qleisli.Semantics.RawLegacy.Ownership
import Qleisli.Semantics.RawLegacy.ClassicalScope
import Qleisli.FiniteBasisTransport
import Mathlib.Data.List.Basic

/-! Checked embedding of the pre-Unit-opcode operation representation.
All literal operands and both branch arms survive. Stable owner/scope states
are shared; their independent historical identity remains a separate gate.
No acceptance, source preservation or constitutional admission is inferred.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RawRepresentationTransport
open QleisliKernel.Semantics

def encodeRawOp : Qleisli.Semantics.RawLegacy.Raw.Op → Raw.Op
  | .init0 output wire => .init0 output wire
  | .gate gate input output => .gate gate input output
  | .cnot control target controlOut targetOut => .cnot control target controlOut targetOut
  | .toffoli a b target aOut bOut targetOut => .toffoli a b target aOut bOut targetOut
  | .quantumIf control target controlOut targetOut zero one =>
    .quantumIf control target controlOut targetOut zero one
  | .split input left right leftBits => .split input left right leftBits
  | .join left right output => .join left right output
  | .liftBasis input output wires table => .liftBasis input output wires table
  | .applyUnitary input output steps => .applyUnitary input output steps
  | .certifiedCompute input output ancilla function physical logical =>
    .certifiedCompute input output ancilla function physical logical
  | .computeUseUncompute input output targets ancilla function uses =>
    .computeUseUncompute input output targets ancilla function uses

theorem encodeRawOp_injective : Function.Injective encodeRawOp := by
  intro left right same
  cases left <;> cases right <;> simp_all [encodeRawOp]

def encodeRawEvent : Qleisli.Semantics.RawLegacy.Raw.Event → Raw.Event
  | .circuit bits steps => .circuit bits steps
  | .init0 bits => .init0 bits
  | .liftBasis inputBits outputBits inputAxes outputAxes table =>
    .liftBasis inputBits outputBits inputAxes outputAxes table
  | .reorder bits axes => .reorder bits axes
  | .computed bits axes sourceBits ancillaBits function physical logical =>
    .computed bits axes sourceBits ancillaBits function physical logical
  | .protectedComputed bits axes sourceBits ancillaBits function uses =>
    .protectedComputed bits axes sourceBits ancillaBits function uses

def encodeRawPrepared (prepared : Qleisli.Semantics.RawLegacy.RawTrace.Prepared) : RawTrace.Prepared :=
  ⟨prepared.state,prepared.events.map encodeRawEvent,prepared.inputBits⟩

theorem rawTrace_preserved (state : RawTrace.Interface) (op : Qleisli.Semantics.RawLegacy.Raw.Op) :
    RawTrace.step state (encodeRawOp op) =
      (Qleisli.Semantics.RawLegacy.RawTrace.step state op).map (Prod.map id (List.map encodeRawEvent)) := by
  cases op <;> simp [encodeRawOp,RawTrace.step,Qleisli.Semantics.RawLegacy.RawTrace.step,encodeRawEvent,Function.comp_def]

def encodeRawProgram (program : Qleisli.Semantics.RawLegacy.Raw.Program) : Raw.Program :=
  ⟨program.inputs,program.operations.map encodeRawOp,program.outputs,program.effect⟩

theorem rawAdvance_preserved (state : Qleisli.Semantics.RawLegacy.RawTrace.Prepared) (op : Qleisli.Semantics.RawLegacy.Raw.Op) :
    RawTrace.advance (encodeRawPrepared state) (encodeRawOp op) =
      (Qleisli.Semantics.RawLegacy.RawTrace.advance state op).map encodeRawPrepared := by
  simp only [RawTrace.advance,Qleisli.Semantics.RawLegacy.RawTrace.advance,encodeRawPrepared,rawTrace_preserved]
  cases Qleisli.Semantics.RawLegacy.RawTrace.step state.state op with
  | none => rfl
  | some value =>
    obtain ⟨next,events⟩ := value
    simp [encodeRawPrepared]

private theorem foldOption_transport {Elt Old New : Type} (elements : List Elt)
    (lift : Old → New) (old : Old → Elt → Option Old) (new : New → Elt → Option New)
    (step : ∀ state elem, new (lift state) elem = (old state elem).map lift)
    (initial : Old) :
    elements.foldlM new (lift initial) = (elements.foldlM old initial).map lift := by
  induction elements generalizing initial with
  | nil => rfl
  | cons elem elements ih =>
    simp only [List.foldlM_cons,step]
    cases old initial elem with
    | none => rfl
    | some next => exact ih next

theorem rawWholeTrace_preserved (program : Qleisli.Semantics.RawLegacy.Raw.Program) :
    RawTrace.run (encodeRawProgram program) =
      (Qleisli.Semantics.RawLegacy.RawTrace.run program).map encodeRawPrepared := by
  simp only [RawTrace.run,Qleisli.Semantics.RawLegacy.RawTrace.run,encodeRawProgram,List.foldlM_map]
  let initial := RawTrace.initial program.inputs
  have h := foldOption_transport program.operations encodeRawPrepared
    Qleisli.Semantics.RawLegacy.RawTrace.advance (fun state op => RawTrace.advance state (encodeRawOp op))
    rawAdvance_preserved ⟨initial,[],initial.frame.length⟩
  rw [show (⟨initial,[],initial.frame.length⟩ : RawTrace.Prepared) =
    encodeRawPrepared ⟨initial,[],initial.frame.length⟩ from rfl, h]
  cases program.operations.foldlM Qleisli.Semantics.RawLegacy.RawTrace.advance
      ⟨initial,[],initial.frame.length⟩ with
  | none => rfl
  | some result =>
    simp [RawTrace.finish,Qleisli.Semantics.RawLegacy.RawTrace.finish,encodeRawPrepared,encodeRawEvent,
      Option.map,List.map_append]

theorem outputs_preserved (op : Qleisli.Semantics.RawLegacy.Raw.Op) :
    Ownership.outputs (encodeRawOp op) = Qleisli.Semantics.RawLegacy.Ownership.outputs op := by
  cases op <;> rfl

theorem allocated_preserved (state : Ownership.State)
    (op : Qleisli.Semantics.RawLegacy.Raw.Op) :
    Ownership.allocated state (encodeRawOp op) =
      Qleisli.Semantics.RawLegacy.Ownership.allocated state op := by
  cases op <;> rfl

theorem access_preserved (state : Ownership.State)
    (op : Qleisli.Semantics.RawLegacy.Raw.Op) :
    Ownership.Access state (encodeRawOp op) ↔
      Qleisli.Semantics.RawLegacy.Ownership.Access state op := by
  cases op <;> exact Iff.rfl

theorem pure_preserved (before after : Ownership.State)
    (op : Qleisli.Semantics.RawLegacy.Raw.Op) :
    Ownership.Pure before (encodeRawOp op) after ↔
      Qleisli.Semantics.RawLegacy.Ownership.Pure before op after := by
  constructor
  · intro step
    exact ⟨(access_preserved _ _).mp step.access,
      by
        obtain ⟨events, trace⟩ := step.action
        cases read : Qleisli.Semantics.RawLegacy.RawTrace.step before.interface op with
        | none => simp [rawTrace_preserved,read] at trace
        | some result =>
          have same : result.1 = after.interface := by
            have actual := Option.some.inj (by simpa [rawTrace_preserved,read] using trace)
            exact congrArg Prod.fst actual
          exact ⟨result.2,congrArg some (Prod.ext same rfl)⟩,
      by simpa only [outputs_preserved] using step.tokens,
      by simpa only [allocated_preserved] using step.wires⟩
  · intro step
    exact ⟨(access_preserved _ _).mpr step.access,
      by
        obtain ⟨events, trace⟩ := step.action
        exact ⟨events.map encodeRawEvent,by simp [rawTrace_preserved,trace]⟩,
      by simpa only [outputs_preserved] using step.tokens,
      by simpa only [allocated_preserved] using step.wires⟩

def encodeOp : Qleisli.Semantics.RawLegacy.Observation.Op → Observation.Op
  | .pure op => .pure (encodeRawOp op)
  | .measure input output => .measure input output
  | .reset input output wire => .reset input output wire
  | .discard input => .discard input
  | .constant value output => .constant value output
  | .not input output => .not input output
  | .xor left right output => .xor left right output
  | .and left right output => .and left right output
  | .branch condition left right quantum classical =>
    .branch condition (left.map encodeOp) (right.map encodeOp) quantum classical

theorem encodeOp_injective : Function.Injective encodeOp := by
  intro left
  induction left using Qleisli.Semantics.RawLegacy.Observation.Op.rec
      (motive_2 := fun ops => ∀ other, ops.map encodeOp = other.map encodeOp → ops = other) with
  | pure op =>
    intro other same
    cases other <;> simp_all [encodeOp,encodeRawOp_injective.eq_iff]
  | measure input output =>
    intro other same
    cases other <;> simp_all [encodeOp]
  | reset input output wire =>
    intro other same
    cases other <;> simp_all [encodeOp]
  | discard input =>
    intro other same
    cases other <;> simp_all [encodeOp]
  | constant value output =>
    intro other same
    cases other <;> simp_all [encodeOp]
  | not input output =>
    intro other same
    cases other <;> simp_all [encodeOp]
  | xor a b output =>
    intro other same
    cases other <;> simp_all [encodeOp]
  | and a b output =>
    intro other same
    cases other <;> simp_all [encodeOp]
  | branch condition left right quantum classical ihLeft ihRight =>
    intro other same
    cases other <;> simp_all [encodeOp]
    exact ⟨ihLeft _ rfl,ihRight _ rfl⟩
  | nil other same =>
    cases other <;> simp_all
  | cons op ops ihOp ihOps other same =>
    cases other <;> simp_all
    exact ⟨ihOp rfl,ihOps _ rfl⟩

def encodeProgram (program : Qleisli.Semantics.RawLegacy.Observation.Program) : Observation.Program :=
  ⟨program.inputs,program.classicalInputs,program.operations.map encodeOp,
    program.outputs,program.classicalOutputs,program.effect⟩

theorem encodeProgram_injective : Function.Injective encodeProgram := by
  intro left right same
  cases left
  cases right
  simp only [encodeProgram,Observation.Program.mk.injEq] at same
  obtain ⟨rfl,rfl,operations,rfl,rfl,rfl⟩ := same
  have sameOps := (List.map_injective_iff.mpr encodeOp_injective) operations
  cases sameOps
  rfl

def encodeObservationEvent : Qleisli.Semantics.RawLegacy.Observation.Event → Observation.Event
  | .pure operation => .pure (encodeRawEvent operation)
  | .erase bits axes output => .erase bits axes output
  | .classical expression output => .classical expression output
  | .branch condition left right classical =>
    .branch condition (left.map encodeObservationEvent) (right.map encodeObservationEvent) classical

def encodeObservationPrepared (prepared : Qleisli.Semantics.RawLegacy.Observation.Prepared) :
    Observation.Prepared :=
  ⟨prepared.state,prepared.events.map encodeObservationEvent,prepared.inputBits⟩

/-- Complete literal event data, including both arms and each phi permutation,
are preserved at every existing reader fuel. -/
theorem observingTrace_preserved (fuel : Nat) (state : RawTrace.Interface)
    (ops : List Qleisli.Semantics.RawLegacy.Observation.Op) :
    Observation.readOps fuel state (ops.map encodeOp) =
      (Qleisli.Semantics.RawLegacy.Observation.readOps fuel state ops).map
        (Prod.map id (List.map encodeObservationEvent)) := by
  induction fuel generalizing state ops with
  | zero => rfl
  | succ fuel ih =>
    simp only [Observation.readOps,Qleisli.Semantics.RawLegacy.Observation.readOps,
      List.foldlM_map]
    simp only [Observation.readOps,Qleisli.Semantics.RawLegacy.Observation.readOps] at ih
    refine foldOption_transport ops
      (Prod.map id (List.map encodeObservationEvent)) _ _ ?_ (state,[])
    intro pair op
    obtain ⟨state,events⟩ := pair
    cases op with
    | branch condition left right quantum classical =>
      simp only [encodeOp]
      rw [ih, ih]
      simp [encodeObservationEvent,encodeRawEvent,Option.bind_map,Function.comp_def]
    | _ =>
      simp [encodeOp,rawTrace_preserved,encodeObservationEvent,encodeRawEvent,
        Option.bind_map,List.map_map,Function.comp_def]

theorem wholeTrace_preserved (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    Observation.read (encodeProgram program) =
      (Qleisli.Semantics.RawLegacy.Observation.read program).map encodeObservationPrepared := by
  simp [Observation.read,Qleisli.Semantics.RawLegacy.Observation.read,encodeProgram,
    observingTrace_preserved,encodeObservationPrepared,encodeObservationEvent,encodeRawEvent,
    Option.bind_map,Function.comp_def]

mutual
  theorem ownershipStep_forward {before after : Ownership.State}
      {op : Qleisli.Semantics.RawLegacy.Observation.Op}
      (step : Qleisli.Semantics.RawLegacy.Ownership.Step before op after) :
      Ownership.Step before (encodeOp op) after := by
    cases step with
    | pure before op after body =>
      simp only [encodeOp]
      exact .pure _ _ _ ((pure_preserved _ _ _).mpr body)
    | measure before input output port after body bit =>
      simp only [encodeOp]
      exact .measure _ _ _ _ _ body bit
    | reset before input output wire port middle after body bit fresh =>
      simp only [encodeOp]
      exact .reset _ _ _ _ _ _ _ body bit fresh
    | discard before input port after body =>
      simp only [encodeOp]
      exact .discard _ _ _ _ body
    | constant state value output =>
      simp only [encodeOp]
      exact .constant _ _ _
    | not state input output =>
      simp only [encodeOp]
      exact .not _ _ _
    | xor state left right output =>
      simp only [encodeOp]
      exact .xor _ _ _ _
    | and state left right output =>
      simp only [encodeOp]
      exact .and _ _ _ _
    | branch before condition thenOps elseOps quantum classical left right after a b coverage merge =>
      simp only [encodeOp]
      exact .branch _ _ _ _ _ _ _ _ _ (ownershipRun_forward a) (ownershipRun_forward b) coverage merge
  theorem ownershipRun_forward {before after : Ownership.State}
      {ops : List Qleisli.Semantics.RawLegacy.Observation.Op}
      (run : Qleisli.Semantics.RawLegacy.Ownership.Run before ops after) :
      Ownership.Run before (ops.map encodeOp) after := by
    cases run with
    | nil state valid =>
      simp only [List.map_nil]
      exact .nil _ valid
    | cons before op middle ops after valid head tail =>
      simp only [List.map_cons]
      exact .cons _ _ _ _ _ valid (ownershipStep_forward head) (ownershipRun_forward tail)
end

mutual
  theorem scopeStep_forward {before after : ClassicalScope.State}
      {op : Qleisli.Semantics.RawLegacy.Observation.Op}
      (step : Qleisli.Semantics.RawLegacy.ClassicalScope.Step before op after) :
      ClassicalScope.Step before (encodeOp op) after := by
    cases step with
    | pure state op =>
      simp only [encodeOp]
      exact .pure _ _
    | measure before input output after fresh =>
      simp only [encodeOp]
      exact .measure _ _ _ _ fresh
    | reset state input output wire =>
      simp only [encodeOp]
      exact .reset _ _ _ _
    | discard state input =>
      simp only [encodeOp]
      exact .discard _ _
    | constant before value output after fresh =>
      simp only [encodeOp]
      exact .constant _ _ _ _ fresh
    | not before input output after access fresh =>
      simp only [encodeOp]
      exact .not _ _ _ _ access fresh
    | xor before left right output after a b fresh =>
      simp only [encodeOp]
      exact .xor _ _ _ _ _ a b fresh
    | and before left right output after a b fresh =>
      simp only [encodeOp]
      exact .and _ _ _ _ _ a b fresh
    | branch before condition thenOps elseOps quantum classical left right after access a b operands destinations =>
      simp only [encodeOp]
      exact .branch _ _ _ _ _ _ _ _ _ access (scopeRun_forward a) (scopeRun_forward b) operands destinations
  theorem scopeRun_forward {before after : ClassicalScope.State}
      {ops : List Qleisli.Semantics.RawLegacy.Observation.Op}
      (run : Qleisli.Semantics.RawLegacy.ClassicalScope.Run before ops after) :
      ClassicalScope.Run before (ops.map encodeOp) after := by
    cases run with
    | nil state =>
      simp only [List.map_nil]
      exact .nil _
    | cons before op middle ops after head tail =>
      simp only [List.map_cons]
      exact .cons _ _ _ _ _ (scopeStep_forward head) (scopeRun_forward tail)
end

theorem ownership_forward (program : Qleisli.Semantics.RawLegacy.Observation.Program)
    (safe : Qleisli.Semantics.RawLegacy.Ownership.OwnershipSafe program) :
    Ownership.OwnershipSafe (encodeProgram program) := by
  obtain ⟨initial,final,inputs,run,outputs⟩ := safe
  exact ⟨initial,final,inputs,ownershipRun_forward run,outputs⟩

theorem scope_forward (program : Qleisli.Semantics.RawLegacy.Observation.Program)
    (safe : Qleisli.Semantics.RawLegacy.ClassicalScope.ScopeSafe program) :
    ClassicalScope.ScopeSafe (encodeProgram program) := by
  obtain ⟨initial,final,inputs,run,outputs⟩ := safe
  exact ⟨initial,final,inputs,scopeRun_forward run,outputs⟩

mutual
  theorem ownershipStep_backward (op : Qleisli.Semantics.RawLegacy.Observation.Op)
      {before after : Ownership.State}
      (step : Ownership.Step before (encodeOp op) after) :
      Qleisli.Semantics.RawLegacy.Ownership.Step before op after := by
    cases op with
    | pure op =>
      simp only [encodeOp] at step
      cases step with
      | pure before op after body => exact .pure _ _ _ ((pure_preserved _ _ _).mp body)
    | measure input output =>
      simp only [encodeOp] at step
      cases step with
      | measure before input output port after body bit => exact .measure _ _ _ _ _ body bit
    | reset input output wire =>
      simp only [encodeOp] at step
      cases step with
      | reset before input output wire port middle after body bit fresh => exact .reset _ _ _ _ _ _ _ body bit fresh
    | discard input =>
      simp only [encodeOp] at step
      cases step with
      | discard before input port after body => exact .discard _ _ _ _ body
    | constant value output =>
      simp only [encodeOp] at step
      cases step with
      | constant state value output => exact .constant _ _ _
    | not input output =>
      simp only [encodeOp] at step
      cases step with
      | not state input output => exact .not _ _ _
    | xor left right output =>
      simp only [encodeOp] at step
      cases step with
      | xor state left right output => exact .xor _ _ _ _
    | and left right output =>
      simp only [encodeOp] at step
      cases step with
      | and state left right output => exact .and _ _ _ _
    | branch condition left right quantum classical =>
      simp only [encodeOp] at step
      cases step with
      | branch before condition thenOps elseOps quantum classical left right after a b coverage merge =>
        exact .branch _ _ _ _ _ _ _ _ _ (ownershipRun_backward _ a) (ownershipRun_backward _ b) coverage merge
  theorem ownershipRun_backward (ops : List Qleisli.Semantics.RawLegacy.Observation.Op)
      {before after : Ownership.State}
      (run : Ownership.Run before (ops.map encodeOp) after) :
      Qleisli.Semantics.RawLegacy.Ownership.Run before ops after := by
    cases ops with
    | nil =>
      simp only [List.map_nil] at run
      cases run with
      | nil state valid => exact .nil _ valid
    | cons op ops =>
      simp only [List.map_cons] at run
      cases run with
      | cons before op middle ops after valid head tail =>
        exact .cons _ _ _ _ _ valid (ownershipStep_backward _ head) (ownershipRun_backward _ tail)
end

mutual
  theorem scopeStep_backward (op : Qleisli.Semantics.RawLegacy.Observation.Op)
      {before after : ClassicalScope.State}
      (step : ClassicalScope.Step before (encodeOp op) after) :
      Qleisli.Semantics.RawLegacy.ClassicalScope.Step before op after := by
    cases op with
    | pure op =>
      simp only [encodeOp] at step
      cases step with
      | pure state op => exact .pure _ _
    | measure input output =>
      simp only [encodeOp] at step
      cases step with
      | measure before input output after fresh => exact .measure _ _ _ _ fresh
    | reset input output wire =>
      simp only [encodeOp] at step
      cases step with
      | reset state input output wire => exact .reset _ _ _ _
    | discard input =>
      simp only [encodeOp] at step
      cases step with
      | discard state input => exact .discard _ _
    | constant value output =>
      simp only [encodeOp] at step
      cases step with
      | constant before value output after fresh => exact .constant _ _ _ _ fresh
    | not input output =>
      simp only [encodeOp] at step
      cases step with
      | not before input output after access fresh => exact .not _ _ _ _ access fresh
    | xor left right output =>
      simp only [encodeOp] at step
      cases step with
      | xor before left right output after a b fresh => exact .xor _ _ _ _ _ a b fresh
    | and left right output =>
      simp only [encodeOp] at step
      cases step with
      | and before left right output after a b fresh => exact .and _ _ _ _ _ a b fresh
    | branch condition left right quantum classical =>
      simp only [encodeOp] at step
      cases step with
      | branch before condition thenOps elseOps quantum classical left right after access a b operands destinations =>
        exact .branch _ _ _ _ _ _ _ _ _ access (scopeRun_backward _ a) (scopeRun_backward _ b) operands destinations
  theorem scopeRun_backward (ops : List Qleisli.Semantics.RawLegacy.Observation.Op)
      {before after : ClassicalScope.State}
      (run : ClassicalScope.Run before (ops.map encodeOp) after) :
      Qleisli.Semantics.RawLegacy.ClassicalScope.Run before ops after := by
    cases ops with
    | nil =>
      simp only [List.map_nil] at run
      cases run with
      | nil state => exact .nil _
    | cons op ops =>
      simp only [List.map_cons] at run
      cases run with
      | cons before op middle ops after head tail =>
        exact .cons _ _ _ _ _ (scopeStep_backward _ head) (scopeRun_backward _ tail)
end

theorem ownership_preserved (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    Ownership.OwnershipSafe (encodeProgram program) ↔
      Qleisli.Semantics.RawLegacy.Ownership.OwnershipSafe program := by
  constructor
  · intro safe
    obtain ⟨initial,final,inputs,run,outputs⟩ := safe
    exact ⟨initial,final,inputs,ownershipRun_backward _ run,outputs⟩
  · exact ownership_forward program

theorem scope_preserved (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    ClassicalScope.ScopeSafe (encodeProgram program) ↔
      Qleisli.Semantics.RawLegacy.ClassicalScope.ScopeSafe program := by
  constructor
  · intro safe
    obtain ⟨initial,final,inputs,run,outputs⟩ := safe
    exact ⟨initial,final,inputs,scopeRun_backward _ run,outputs⟩
  · exact scope_forward program

/-- Original artifact shape, combining the previous checked basis embedding
with the pre-Unit operation representation. No accepted handle is a field. -/
structure LegacyArtifact where
  programs : Array Qleisli.Semantics.RawLegacy.Observation.Program
  entries : Array Qleisli.FiniteBasisTransport.LegacyEntry
  sources : Array (String × String)
  root : Nat
  rootInterface : Option (List Qleisli.FiniteBasisTransport.LegacyAtom ×
    List Qleisli.FiniteBasisTransport.LegacyAtom)

def encodeArtifact (artifact : LegacyArtifact) : QleisliKernel.Qirf.Artifact :=
  ⟨artifact.programs.map encodeProgram,
    artifact.entries.map Qleisli.FiniteBasisTransport.encodeEntry,
    artifact.sources,artifact.root,
    artifact.rootInterface.map fun (input,output) =>
      (Qleisli.FiniteBasisTransport.encodeBasis input,Qleisli.FiniteBasisTransport.encodeBasis output)⟩

/-- Preserve selection of the literal original root at the original index.
This does not infer byte-decoder or native-compiler correspondence. -/
theorem originalRoot_preserved (artifact : LegacyArtifact) :
    (encodeArtifact artifact).programs[(encodeArtifact artifact).root]? =
      artifact.programs[artifact.root]?.map encodeProgram := by
  exact Array.getElem?_map

theorem originalRoot_ownership (artifact : LegacyArtifact)
    (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    ((encodeArtifact artifact).programs[(encodeArtifact artifact).root]? = some (encodeProgram program) ∧
      Ownership.OwnershipSafe (encodeProgram program)) ↔
    (artifact.programs[artifact.root]? = some program ∧
      Qleisli.Semantics.RawLegacy.Ownership.OwnershipSafe program) := by
  rw [originalRoot_preserved,ownership_preserved]
  cases found : artifact.programs[artifact.root]? with
  | none => simp
  | some selected => simp [encodeProgram_injective.eq_iff]

theorem originalRoot_scope (artifact : LegacyArtifact)
    (program : Qleisli.Semantics.RawLegacy.Observation.Program) :
    ((encodeArtifact artifact).programs[(encodeArtifact artifact).root]? = some (encodeProgram program) ∧
      ClassicalScope.ScopeSafe (encodeProgram program)) ↔
    (artifact.programs[artifact.root]? = some program ∧
      Qleisli.Semantics.RawLegacy.ClassicalScope.ScopeSafe program) := by
  rw [originalRoot_preserved,scope_preserved]
  cases found : artifact.programs[artifact.root]? with
  | none => simp
  | some selected => simp [encodeProgram_injective.eq_iff]

end Qleisli.RawRepresentationTransport
