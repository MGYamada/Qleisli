import QleisliKernel.Semantics.Raw
import QleisliKernel.Semantics.RawTrace
import QleisliKernel.Finite

/-! VM-25 straight-line pure ownership/typing and actual-body extraction.
This checker receives original operations. Its dependency argument consists of
signatures only; semantic callers are reconstructed separately from raw bodies.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw
open Semantics.Raw Semantics.Finite

abbrev Check := Except Finite.Error

def require (condition : Bool) : Check Unit :=
  if condition then .ok () else .error .invalid

def unique {α : Type} [BEq α] (values : List α) : Bool :=
  values.eraseDups.length == values.length

structure State where
  live : List Port := []
  seenTokens : List Nat := []
  seenWires : List Nat := []
  frame : List Nat := []
  iso : Bool := false
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for State

/-- Complete coverage includes zero-width owners: their tokens are not erased.
Frame wires are the persistent ordered axes, not a new identity for each move. -/
def stateValid (state : State) : Bool :=
  unique (state.live.map (·.token)) && unique state.seenTokens && unique state.seenWires &&
  unique state.frame && unique (state.live.flatMap (·.wires)) &&
  state.live.all (fun port => port.bits == port.wires.length && port.bits ≤ 12 &&
    state.seenTokens.contains port.token) &&
  state.frame.all state.seenWires.contains &&
  (state.live.flatMap (·.wires)).length == state.frame.length &&
  (state.live.flatMap (·.wires)).all state.frame.contains

def reserve (state : State) (wires : List Nat) : Check State := do
  require (unique wires && wires.all (fun wire => wire ≤ 4294967295 && !state.seenWires.contains wire))
  return {state with seenWires := state.seenWires ++ wires}

def insert (state : State) (token : Nat) (wires : List Nat) : Check State := do
  require (token ≤ 4294967295 && !state.seenTokens.contains token && wires.length ≤ 12 &&
    unique wires && wires.all (fun wire => !(state.live.flatMap (·.wires)).contains wire))
  return {state with
    live := state.live ++ [⟨token,wires,wires.length⟩]
    seenTokens := state.seenTokens ++ [token]}

def take (state : State) (token : Nat) : Check (Port × State) := do
  let port ← Finite.readOption (state.live.find? (fun port => port.token == token))
  return (port,{state with live := state.live.filter (fun port => port.token != token)})

def axes (state : State) (wires : List Nat) : List Nat := wires.map state.frame.idxOf

def tableValid (input output : Nat) (table : List Nat) (injective : Bool) : Bool :=
  table.length == 2^input && table.all (· < 2^output) && (!injective || unique table)

def circuitStepsValid (dependencies : List Basis) (bits : Nat) (steps : List Step) : Bool :=
  steps.all fun step =>
    Finite.axesValid bits (step.controls.map (·.index) ++ Finite.targets step.action) &&
    match step.action with
    | .hadamard _ => true
    | .monomial indices permutation phases =>
      tableValid indices.length indices.length permutation true &&
      phases.length == permutation.length && phases.all (· < 8)
    | .contract indices index _ =>
      ((dependencies[index]?).map (fun basis => Finite.basisValid basis && indices.length == width basis)).getD false

def phaseExponent : Phase → Nat | .minusOne => 4 | .eighthTurn => 1

def gateStep (gate : Gate) (target : Nat) : Step :=
  ⟨[],match gate with
    | .h => .hadamard target
    | .x => .monomial [target] [1,0] [0,0]
    | .z => .monomial [target] [0,1] [0,4]
    | .t => .monomial [target] [0,1] [0,1]⟩

def unitaryStep : UnitaryStep → Step
  | .gate gate target => gateStep gate target
  | .cnot control target => {gateStep .x target with controls := [⟨control,true⟩]}
  | .toffoli a b target => {gateStep .x target with controls := [⟨a,true⟩,⟨b,true⟩]}
  | .phase phase => ⟨[],.monomial [] [0] [phaseExponent phase]⟩

def remap (indices : List Nat) (step : Step) : Step :=
  let axis := fun index => indices[index]?.getD 0
  ⟨step.controls.map (fun c => ⟨axis c.index,c.whenOne⟩),match step.action with
    | .hadamard target => .hadamard (axis target)
    | .monomial targets permutation phases => .monomial (targets.map axis) permutation phases
    | .contract targets index adjoint => .contract (targets.map axis) index adjoint⟩

def protectedAxis (dataBits : Nat) (bit : ProtectedBit) : Nat :=
  match bit.region with | .source => bit.index | .ancilla => dataBits + bit.index

def protectedValid (sourceBits ancillaBits : Nat) (bit : ProtectedBit) : Bool :=
  bit.index < match bit.region with | .source => sourceBits | .ancilla => ancillaBits

def protectedControlsValid (sourceBits ancillaBits : Nat) (controls : List ProtectedControl) : Bool :=
  controls.all (fun c => protectedValid sourceBits ancillaBits c.bit) && unique (controls.map (·.bit))

def usesValid (sourceBits ancillaBits targets : Nat) (uses : List Use) : Bool :=
  uses.all fun use => match use with
  | .protectedGate bit gate => protectedValid sourceBits ancillaBits bit && (gate == .z || gate == .t)
  | .targetGate controls target _ => target < targets && protectedControlsValid sourceBits ancillaBits controls
  | .phase controls _ => protectedControlsValid sourceBits ancillaBits controls

def physicalUse (sourceBits dataBits : Nat) : Use → Step
  | .protectedGate bit gate => gateStep gate (protectedAxis dataBits bit)
  | .targetGate controls target gate => {gateStep gate (sourceBits+target) with
      controls := controls.map fun c => ⟨protectedAxis dataBits c.bit,c.whenOne⟩}
  | .phase controls phase => ⟨controls.map (fun c => ⟨protectedAxis dataBits c.bit,c.whenOne⟩),
      .monomial [] [0] [phaseExponent phase]⟩

def protectedValue (source computed : Nat) (bit : ProtectedBit) : Bool :=
    Semantics.Finite.bit (match bit.region with | .source => source | .ancilla => computed) bit.index == 1

def protectedEnabled (source computed : Nat) (controls : List ProtectedControl) : Bool :=
  controls.all fun c => protectedValue source computed c.bit == c.whenOne

/-- The collapsed logical use is derived from every original protected operation
and every source label. Scalar phases on Unit targets are retained. -/
def logicalUse (sourceBits : Nat) (function : List Nat) (use : Use) : List Step :=
  let sourceAxes := List.range sourceBits
  match use with
  | .protectedGate bit gate => [⟨[],.monomial sourceAxes (List.range function.length)
      ((function.zipIdx).map fun (computed,source) =>
        if protectedValue source computed bit then (if gate == .z then 4 else 1) else 0)⟩]
  | .phase controls phase => [⟨[],.monomial sourceAxes (List.range function.length)
      ((function.zipIdx).map fun (computed,source) =>
        if protectedEnabled source computed controls then phaseExponent phase else 0)⟩]
  | .targetGate controls target gate => (function.zipIdx).filterMap fun (computed,source) =>
      if protectedEnabled source computed controls then
        some {gateStep gate (sourceBits+target) with controls := sourceAxes.map fun axis =>
          ⟨axis,Semantics.Finite.bit source axis == 1⟩}
      else none

structure Transition where
  state : State
  events : List Event := []
  deriving Repr

private def one (port : Port) : Check Unit := require (port.bits == 1)

/-- Constructor dispatch over the original raw operation; no Rust validation or
extracted circuit is an input. Every output insertion uses global freshness. -/
def dispatch (dependencies : List Basis) (state : State) (op : Op) : Check Transition := do
  let bits := state.frame.length
  match op with
  | .init0 output wire =>
    let next ← reserve state [wire]
    let next ← insert next output [wire]
    return ⟨{next with frame := state.frame ++ [wire],iso := true},
      [.init0 bits]⟩
  | .gate gate input output =>
    let (port,next) ← take state input
    one port
    let next ← insert next output port.wires
    return ⟨next,[.circuit bits [gateStep gate (state.frame.idxOf (port.wires[0]?.getD 0))]]⟩
  | .cnot control target controlOut targetOut =>
    let (c,next) ← take state control
    let (t,next) ← take next target
    one c; one t
    let next ← insert next controlOut c.wires
    let next ← insert next targetOut t.wires
    let step := {gateStep .x (state.frame.idxOf (t.wires[0]?.getD 0)) with
      controls := [⟨state.frame.idxOf (c.wires[0]?.getD 0),true⟩]}
    return ⟨next,[.circuit bits [step]]⟩
  | .toffoli a b target aOut bOut targetOut =>
    let (a,next) ← take state a
    let (b,next) ← take next b
    let (t,next) ← take next target
    one a; one b; one t
    let next ← insert next aOut a.wires
    let next ← insert next bOut b.wires
    let next ← insert next targetOut t.wires
    let step := {gateStep .x (state.frame.idxOf (t.wires[0]?.getD 0)) with
      controls := [⟨state.frame.idxOf (a.wires[0]?.getD 0),true⟩,⟨state.frame.idxOf (b.wires[0]?.getD 0),true⟩]}
    return ⟨next,[.circuit bits [step]]⟩
  | .quantumIf control target controlOut targetOut zero oneSteps =>
    let (c,next) ← take state control
    let (t,next) ← take next target
    one c
    require (circuitStepsValid [] t.bits (zero.map unitaryStep) &&
      circuitStepsValid [] t.bits (oneSteps.map unitaryStep))
    let next ← insert next controlOut c.wires
    let next ← insert next targetOut t.wires
    let arm (polarity : Bool) (steps : List UnitaryStep) : List Step := steps.map fun step =>
      let step := remap (axes state t.wires) (unitaryStep step)
      {step with controls := step.controls ++ [⟨state.frame.idxOf (c.wires[0]?.getD 0),polarity⟩]}
    return ⟨next,[.circuit bits (arm false zero ++ arm true oneSteps)]⟩
  | .split input left right leftBits =>
    let (port,next) ← take state input
    require (leftBits ≤ port.bits)
    let next ← insert next left (port.wires.take leftBits)
    let next ← insert next right (port.wires.drop leftBits)
    return ⟨next,[]⟩
  | .join left right output =>
    let (l,next) ← take state left
    let (r,next) ← take next right
    return ⟨← insert next output (l.wires ++ r.wires),[]⟩
  | .liftBasis input output wires table =>
    let (port,next) ← take state input
    require (wires.length ≤ 12 && port.bits ≤ wires.length && wires.take port.bits == port.wires &&
      tableValid port.bits wires.length table true)
    let fresh := wires.drop port.bits
    let next ← reserve next fresh
    let next ← insert next output wires
    let frame := state.frame ++ fresh
    let inAxes := axes state port.wires
    let outAxes := wires.map frame.idxOf
    return ⟨{next with frame,iso := state.iso || !fresh.isEmpty},
      [.liftBasis bits frame.length inAxes outAxes table]⟩
  | .applyUnitary input output steps =>
    let (port,next) ← take state input
    require (circuitStepsValid dependencies port.bits steps)
    return ⟨← insert next output port.wires,[.circuit bits (steps.map (remap (axes state port.wires))) ]⟩
  | .certifiedCompute input output ancilla function useSteps logicalSteps =>
    let (port,next) ← take state input
    require (ancilla.length == 1 && tableValid port.bits 1 function false &&
      circuitStepsValid dependencies (port.bits+1) useSteps &&
      circuitStepsValid dependencies port.bits logicalSteps)
    let next ← reserve next ancilla
    return ⟨← insert next output port.wires,
      [.computed bits (axes state port.wires) port.bits 1 function useSteps logicalSteps]⟩
  | .computeUseUncompute input output targets ancilla function uses =>
    let (source,next) ← take state input
    let (targetPorts,next) ← targets.foldlM (fun (ports,next) target => do
      let (port,next) ← take next target.input
      one port
      pure (ports ++ [port],next)) ([],next)
    require (ancilla.length ≤ 12 && tableValid source.bits ancilla.length function false &&
      usesValid source.bits ancilla.length targets.length uses)
    let next ← reserve next ancilla
    let next ← insert next output source.wires
    let next ← (targets.zip targetPorts).foldlM (fun next (target,port) =>
      insert next target.output port.wires) next
    return ⟨next,[.protectedComputed bits (axes state (source.wires ++ targetPorts.flatMap (·.wires)))
      source.bits ancilla.length function uses]⟩

def step (dependencies : List Basis) (state : State) (op : Op) : Check Transition := do
  require (stateValid state)
  let result ← dispatch dependencies state op
  require (stateValid result.state)
  return result

structure Prepared where
  state : State
  events : List Event
  inputBits : Nat
  deriving Repr

def input (state : State) (port : Port) : Check State := do
  require (port.bits == port.wires.length && port.bits ≤ 12)
  let next ← reserve state port.wires
  let next ← insert next port.token port.wires
  let next := {next with frame := state.frame ++ port.wires}
  require (stateValid next)
  return next

def advance (dependencies : List Basis) (prepared : Prepared) (op : Op) : Check Prepared := do
  let next ← step dependencies prepared.state op
  return {prepared with state := next.state,events := prepared.events ++ next.events}

def outputValid (program : Program) (state : State) : Bool :=
  unique program.outputs && program.outputs.length == state.live.length &&
  program.outputs.all (fun token => state.live.any (fun port => port.token == token)) &&
  state.live.all (fun port => program.outputs.contains port.token) &&
  (!state.iso || program.effect != .unitary)

/-- Final output order becomes an explicit permutation, including an otherwise
empty split/join function. The live-owner check precedes this extraction. -/
def prepare (dependencies : List Basis) (program : Program) : Check Prepared := do
  let initial ← program.inputs.foldlM input {}
  let result ← program.operations.foldlM (advance dependencies) ⟨initial,[],initial.frame.length⟩
  require (outputValid program result.state)
  let wires := program.outputs.flatMap fun token =>
    ((result.state.live.find? (fun port => port.token == token)).map (·.wires)).getD []
  let ordered := axes result.state wires
  return {result with events := result.events ++ [.reorder result.state.frame.length ordered]}

theorem require_success (condition : Bool) (ok : require condition = .ok ()) : condition = true := by
  cases condition <;> simp_all [require]

/-- No live owner, including Unit, can be omitted from an accepted interface. -/
theorem output_coverage (program : Program) (state : State) (ok : outputValid program state = true) :
    (∀ port, port ∈ state.live → port.token ∈ program.outputs) ∧
    (∀ token, token ∈ program.outputs → ∃ port, port ∈ state.live ∧ port.token = token) ∧
    (state.iso = true → program.effect ≠ .unitary) := by
  simp only [outputValid,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,
    List.contains_iff_mem,beq_iff_eq,Bool.or_eq_true] at ok
  refine ⟨ok.1.2,ok.1.1.2,?_⟩
  intro iso
  rcases ok.2 with h | h
  · rw [iso] at h; cases h
  · simpa using h

/-- Insertion preserves the issued identities of consumed owners; a previously
seen token can never be revived, even for a zero-width register. -/
theorem insert_fresh (state : State) (token : Nat) (wires : List Nat) (result : State)
    (ok : insert state token wires = .ok result) :
    token ∉ state.seenTokens ∧ token ∈ result.seenTokens ∧
    ∃ port, port ∈ result.live ∧ port.token = token ∧ port.wires = wires := by
  obtain ⟨_,hc,h⟩ := Finite.except_bind_success _ _ _ ok
  have good := require_success _ hc
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  simp only [Bool.and_eq_true] at good
  exact ⟨by simpa using good.1.1.1.2,by simp,⟨⟨token,wires,wires.length⟩,by simp,rfl,rfl⟩⟩

theorem step_conditions (dependencies : List Basis) (state : State) (op : Op) (result : Transition)
    (ok : step dependencies state op = .ok result) :
    stateValid state = true ∧ dispatch dependencies state op = .ok result ∧ stateValid result.state = true := by
  obtain ⟨_,hi,h⟩ := Finite.except_bind_success _ _ _ ok
  obtain ⟨next,hn,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,ho,h⟩ := Finite.except_bind_success _ _ _ h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  exact ⟨require_success _ hi,hn,require_success _ ho⟩

/-- Every accepted constructor is related to its actual executable dispatch.
The trace includes all intermediates and persistent seen IDs. -/
inductive Trace (dependencies : List Basis) : State → List Op → State → Prop
  | nil (state) : Trace dependencies state [] state
  | cons (state op next ops final) (checked : step dependencies state op = .ok next)
      (rest : Trace dependencies next.state ops final) : Trace dependencies state (op::ops) final

theorem operations_trace (dependencies : List Basis) (operations : List Op) (initial result : Prepared)
    (ok : operations.foldlM (advance dependencies) initial = .ok result) :
    Trace dependencies initial.state operations result.state := by
  induction operations generalizing initial with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst result
    exact .nil _
  | cons op ops ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,hrest⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨transition,ht,h⟩ := Finite.except_bind_success _ _ _ hn
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst next
    exact .cons _ _ _ _ _ ht (ih _ hrest)

theorem input_valid (state : State) (port : Port) (result : State)
    (ok : input state port = .ok result) : stateValid result = true := by
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ ok
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,hg,h⟩ := Finite.except_bind_success _ _ _ h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  exact require_success _ hg

theorem inputs_valid (ports : List Port) (initial result : State) (valid : stateValid initial = true)
    (ok : ports.foldlM input initial = .ok result) : stateValid result = true := by
  induction ports generalizing initial with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst result
    exact valid
  | cons port ports ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,hn,h⟩ := Finite.except_bind_success _ _ _ ok
    exact ih next (input_valid _ _ _ hn) h

theorem Trace.valid (dependencies : List Basis) (initial final : State) (operations : List Op)
    (trace : Trace dependencies initial operations final) (valid : stateValid initial = true) :
    stateValid final = true := by
  induction trace with
  | nil => exact valid
  | cons state op next ops final checked rest ih =>
    exact ih (step_conditions _ _ _ _ checked).2.2

theorem prepare_conditions (dependencies : List Basis) (program : Program) (result : Prepared)
    (ok : prepare dependencies program = .ok result) :
    ∃ initial body, program.inputs.foldlM input {} = .ok initial ∧
      program.operations.foldlM (advance dependencies) ⟨initial,[],initial.frame.length⟩ = .ok body ∧
      outputValid program body.state = true ∧ result.state = body.state ∧
      Trace dependencies initial program.operations result.state := by
  obtain ⟨initial,hi,h⟩ := Finite.except_bind_success _ _ _ ok
  obtain ⟨body,hb,h⟩ := Finite.except_bind_success _ _ _ h
  obtain ⟨_,ho,h⟩ := Finite.except_bind_success _ _ _ h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst result
  exact ⟨initial,body,hi,hb,require_success _ ho,rfl,operations_trace _ _ _ _ hb⟩

/-- Complete ownership/effect safety for every constructor in this pure profile.
The proof follows the actual input reader and every actual dispatch; it neither
assumes Rust verification nor omits zero-width owners from output coverage. -/
theorem prepare_safety (dependencies : List Basis) (program : Program) (result : Prepared)
    (ok : prepare dependencies program = .ok result) :
    stateValid result.state = true ∧
    (∀ port, port ∈ result.state.live → port.token ∈ program.outputs) ∧
    (∀ token, token ∈ program.outputs → ∃ port, port ∈ result.state.live ∧ port.token = token) ∧
    (result.state.iso = true → program.effect ≠ .unitary) := by
  rcases prepare_conditions _ _ _ ok with ⟨initial,body,hi,_,ho,same,trace⟩
  have valid := inputs_valid _ _ _ (by decide) hi
  have finalValid := Trace.valid _ _ _ _ trace valid
  rw [← same] at ho
  exact ⟨finalValid,output_coverage _ _ ho⟩

end QleisliKernel.Raw
