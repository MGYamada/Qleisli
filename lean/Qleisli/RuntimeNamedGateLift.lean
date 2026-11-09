import Qleisli.RawActionLocality
import Qleisli.RuntimeIntervalRawFold
import QleisliKernel.Qirf.RuntimeNamedFrameAxes
import QleisliKernel.Qirf.RuntimeNamedOrdinaryLocal
import QleisliKernel.Qirf.RuntimePrimitiveSource

/-! One-owner pure literals in genuine named call frames. The parent and local
Raw checks retain the same original instruction, ordered port and axis data.
Their derived action law allows arbitrary joint-reference amplitudes and keeps
all ordered spectator ports, including Unit. Mixed scopes use the same proof
only for an actual pure slice; no enclosing effect or history is sharpened.
The local fragment theorem retains its explicit final output permutation.
Source-body/code substitution and whole-caller finish remain distinct duties.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedGateLift
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open QleisliKernel.Finite QleisliKernel.Semantics.Finite

/-- Two original Raw spellings. This is proof indexing, not a validator or a
rewrite of an accepted instruction into a different native operation. -/
inductive Form where
  | applyUnitary (steps : List Step)
  | gate (value : Semantics.Raw.Gate)

def Form.operation : Form → Nat → Nat → Semantics.Raw.Op
  | .applyUnitary steps,input,output => .applyUnitary input output steps
  | .gate value,input,output => .gate value input output

def Form.tape : Form → List Step
  | .applyUnitary steps => steps
  | .gate value => [Semantics.RawTrace.gate value 0]

private def Form.Width : Form → Nat → Prop
  | .applyUnitary _,_ => True
  | .gate _,bits => bits = 1

/-- The ordered physical axes of this complete selected port. -/
def portAxes (before : Raw.State) (port : Semantics.Raw.Port) : List Nat :=
  port.wires.map before.frame.idxOf

private theorem map_fixed {α : Type} (f : α → α) (xs : List α)
    (fixed : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons,fixed x (List.mem_cons_self)]
    exact congrArg (List.cons x) (ih (fun y member => fixed y (List.mem_cons_of_mem _ member)))

/-- The local entry is the one the existing named reader actually checked.
No new initial-state checker run or successful semantic outcome is supplied. -/
private theorem local_interface {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs) :
    scope.localEntry.quantum.reference =
      ⟨scope.selected,scope.selected.flatMap (·.wires)⟩ := by
  obtain ⟨work,left,ran⟩ := scope.entryRead
  unfold PureInterval.initial at ran
  obtain ⟨quantum,middle,opened,rest⟩ := bind_success _ _ _ _ _ ran
  have actual : scope.selected.foldlM Raw.input {} = .ok quantum :=
    (lift_success _ _ _ _ opened).1
  have same : scope.localEntry = ({quantum} : Raw.Observation.State) :=
    (Except.ok.inj (lift_success _ _ _ _ rest).1).symm
  rw [same]
  simpa only [List.nil_append] using Raw.inputs_reference scope.selected {} quantum actual

private theorem singleton_lookup (live : List Semantics.Raw.Port) (port : Semantics.Raw.Port)
    (read : PureInterval.portsOf live [port.token] = some [port]) :
    live.find? (fun p => p.token == port.token) = some port := by
  cases found : live.find? (fun p => p.token == port.token) with
  | none => simp [PureInterval.portsOf,List.mapM_cons,found] at read
  | some value =>
    have same : value = port := by
      simpa [PureInterval.portsOf,List.mapM_cons,found] using read
    simp only [same]

private theorem singleton_step (signatures : List Basis) (operation : Semantics.Raw.Op)
    (before after : Raw.State) (events : List Semantics.Raw.Event)
    (ran : [operation].foldlM (Raw.advance signatures) ⟨before,[],before.frame.length⟩ =
      .ok ⟨after,events,before.frame.length⟩) :
    Raw.step signatures before operation = .ok ⟨after,events⟩ := by
  have advanced : Raw.advance signatures ⟨before,[],before.frame.length⟩ operation =
      .ok ⟨after,events,before.frame.length⟩ := by
    simpa only [List.foldlM_cons,List.foldlM_nil,bind_pure] using ran
  unfold Raw.advance at advanced
  obtain ⟨transition,step,returned⟩ := except_bind_success _ _ _ advanced
  have same := Except.ok.inj returned
  have state := congrArg Raw.Prepared.state same
  have emitted := congrArg Raw.Prepared.events same
  simp only [List.nil_append] at emitted
  have equal : transition = (⟨after,events⟩ : Raw.Transition) := by
    cases transition
    simp_all
  simpa only [equal] using step

private theorem apply_dispatch (signatures : List Basis) (before : Raw.State)
    (input output : Nat) (steps : List Step) (result : Raw.Transition)
    (read : Raw.dispatch signatures before (.applyUnitary input output steps) = .ok result) :
    ∃ port rest, Raw.take before input = .ok (port,rest) ∧
      Raw.circuitStepsValid signatures port.bits steps = true ∧
      Raw.insert rest output port.wires = .ok result.state := by
  simp only [Raw.dispatch] at read
  obtain ⟨⟨port,rest⟩,taken,h⟩ := except_bind_success _ _ _ read
  obtain ⟨_,valid,h⟩ := except_bind_success _ _ _ h
  obtain ⟨inserted,insertRead,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  exact ⟨port,rest,taken,Raw.require_success _ valid,insertRead⟩

private theorem tape_bounds (signatures : List Basis) (bits : Nat) (steps : List Step)
    (valid : Raw.circuitStepsValid signatures bits steps = true) (operation : Step)
    (member : operation ∈ steps) :
    (∀ control ∈ operation.controls, control.index < bits) ∧
      (∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < bits) := by
  have checked := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp valid) operation member)).1
  simp only [QleisliKernel.Finite.axesValid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at checked
  have inside := checked.1.2
  exact ⟨fun control present => inside control.index
    (List.mem_append.mpr (Or.inl (List.mem_map_of_mem present))),
    fun axis present => inside axis (List.mem_append.mpr (Or.inr present))⟩

private theorem self_axis (wires : List Nat) (unique : wires.Nodup)
    (index : Nat) (bound : index < wires.length) :
    (wires.map wires.idxOf)[index]?.getD 0 = index := by
  simp only [List.getElem?_map,List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some]
  exact unique.idxOf_getElem index bound

private theorem localize_self (wires : List Nat) (unique : wires.Nodup) (operation : Step)
    (controls : ∀ control ∈ operation.controls, control.index < wires.length)
    (targets : ∀ axis ∈ QleisliKernel.Finite.targets operation.action, axis < wires.length) :
    Semantics.RawTrace.localize (wires.map wires.idxOf) operation = operation := by
  rcases operation with ⟨written,action⟩
  have controlMap : written.map (fun c =>
      (⟨(wires.map wires.idxOf)[c.index]?.getD 0,c.whenOne⟩ : Control)) = written :=
    map_fixed _ _ (fun c member => by rw [self_axis wires unique c.index (controls c member)])
  cases action with
  | hadamard axis =>
    simp only [Semantics.RawTrace.localize,controlMap,
      self_axis wires unique axis (targets axis (List.mem_singleton_self axis))]
  | monomial axes permutation phases =>
    have targetMap := map_fixed (fun axis => (wires.map wires.idxOf)[axis]?.getD 0) axes
      (fun axis member => self_axis wires unique axis (targets axis member))
    simp only [Semantics.RawTrace.localize,controlMap,targetMap]
  | contract axes dependency adjoint =>
    have targetMap := map_fixed (fun axis => (wires.map wires.idxOf)[axis]?.getD 0) axes
      (fun axis member => self_axis wires unique axis (targets axis member))
    simp only [Semantics.RawTrace.localize,controlMap,targetMap]

private theorem dispatch_tape (signatures : List Basis) (before : Raw.State)
    (input output : Nat) (form : Form) (result : Raw.Transition)
    (read : Raw.dispatch signatures before (form.operation input output) = .ok result) :
    ∃ port rest, Raw.take before input = .ok (port,rest) ∧
      Raw.circuitStepsValid signatures port.bits form.tape = true ∧ form.Width port.bits := by
  cases form with
  | applyUnitary steps =>
    obtain ⟨port,rest,taken,valid,_inserted⟩ := apply_dispatch signatures before input output steps result read
    exact ⟨port,rest,taken,valid,True.intro⟩
  | gate value =>
    simp only [Form.operation,Raw.dispatch] at read
    obtain ⟨⟨port,rest⟩,taken,h⟩ := except_bind_success _ _ _ read
    obtain ⟨_,one,_later⟩ := except_bind_success _ _ _ h
    have bits : port.bits = 1 := beq_iff_eq.mp (Raw.require_success _ one)
    have valid : Raw.circuitStepsValid signatures port.bits (Form.tape (.gate value)) = true := by
      cases value <;> rw [bits] <;> rfl
    exact ⟨port,rest,taken,valid,bits⟩

private theorem literal_step (before : Semantics.RawTrace.Interface) (port : Semantics.Raw.Port)
    (output : Nat) (form : Form)
    (found : before.live.find? (fun p => p.token == port.token) = some port)
    (width : form.Width port.wires.length) :
    Semantics.RawTrace.step before (form.operation port.token output) =
      some (Semantics.RawTrace.insert
        {before with live := before.live.filter (fun p => p.token != port.token)} output port.wires,
        [.circuit before.frame.length
          (form.tape.map (Semantics.RawTrace.localize (port.wires.map before.frame.idxOf)))]) := by
  cases form with
  | applyUnitary steps =>
    simp only [Form.operation,Form.tape,Semantics.RawTrace.step,Semantics.RawTrace.take,found,bind,Option.bind,pure]
    rfl
  | gate value =>
    have one : port.wires.length = 1 := width
    obtain ⟨wire,wires⟩ := List.length_eq_one_iff.mp one
    simp only [Form.operation,Form.tape,Semantics.RawTrace.step,Semantics.RawTrace.take,found,bind,Option.bind,pure]
    rw [wires]
    cases value <;> rfl

/-- Both actual folds and traces, their complete ordered interfaces, and the
local/ambient action on every joint-reference slice. No final output reorder
or ordinary effect/history is removed by these facts. -/
structure Facts (dependencies : List Dependency) (operations : List Semantics.Raw.Op)
    (before after localBefore localAfter : Raw.State) (axes : List Nat)
    (port : Semantics.Raw.Port) (output : Nat) (form : Form)
    (parentEvents childEvents : List Semantics.Raw.Event) : Prop where
  original : operations = [form.operation port.token output]
  parentFold : operations.foldlM (Raw.advance (dependencies.map (·.signature)))
    ⟨before,[],before.frame.length⟩ = .ok ⟨after,parentEvents,before.frame.length⟩
  childFold : operations.foldlM (Raw.advance (dependencies.map (·.signature)))
    ⟨localBefore,[],localBefore.frame.length⟩ = .ok ⟨localAfter,childEvents,localBefore.frame.length⟩
  parentTrace : RuntimeLocalEvents.trace before.reference operations =
    some ⟨after.reference,parentEvents,before.frame.length⟩
  childTrace : RuntimeLocalEvents.trace localBefore.reference operations =
    some ⟨localAfter.reference,childEvents,localBefore.frame.length⟩
  childEntry : localBefore.reference = ⟨[port],port.wires⟩
  parentCircuit : parentEvents = [.circuit before.frame.length
    (form.tape.map (Semantics.RawTrace.localize axes))]
  childCircuit : childEvents = [.circuit port.wires.length form.tape]
  parentInterface : after.reference = Semantics.RawTrace.insert
    {before.reference with live := before.live.filter (fun p => p.token != port.token)} output port.wires
  childInterface : localAfter.reference = ⟨[⟨output,port.wires,port.wires.length⟩],port.wires⟩
  action : ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (reference : Reference) (base value : Nat),
    Qleisli.Semantics.RawAction.events dependencies parentEvents (fun i => joint i reference)
      (scatter base axes value) =
    Qleisli.Semantics.RawAction.events dependencies childEvents
      (Qleisli.Semantics.RawAction.Locality.pull base axes (fun i => joint i reference)) value

def Lift (dependencies : List Dependency) (operations : List Semantics.Raw.Op)
    (before after localBefore localAfter : Raw.State) (axes : List Nat)
    (port : Semantics.Raw.Port) (output : Nat) (form : Form) : Prop :=
  ∃ parentEvents childEvents, Facts dependencies operations before after localBefore localAfter axes
    port output form parentEvents childEvents

private structure LocalTapeFacts (form : Form) (port : Semantics.Raw.Port) : Prop where
  width : form.Width port.wires.length
  controls : ∀ op ∈ form.tape, ∀ control ∈ op.controls, control.index < port.wires.length
  targets : ∀ op ∈ form.tape, ∀ axis ∈ QleisliKernel.Finite.targets op.action, axis < port.wires.length
  selfTape : form.tape.map (Semantics.RawTrace.localize (port.wires.map port.wires.idxOf)) = form.tape

private theorem local_tape_facts (signatures : List Basis) (localBefore localAfter : Raw.State)
    (port : Semantics.Raw.Port) (output : Nat) (form : Form) (childEvents : List Semantics.Raw.Event)
    (childEntry : localBefore.reference = ⟨[port],port.wires⟩)
    (childStep : Raw.step signatures localBefore (form.operation port.token output) = .ok ⟨localAfter,childEvents⟩) :
    LocalTapeFacts form port := by
  have localLive : localBefore.live = [port] := congrArg Semantics.RawTrace.Interface.live childEntry
  have localFrame : localBefore.frame = port.wires := congrArg Semantics.RawTrace.Interface.frame childEntry
  have localLookup : localBefore.live.find? (fun p => p.token == port.token) = some port := by
    rw [localLive]
    simp
  have valid := Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ childStep).1
  obtain ⟨takenPort,rest,taken,tapeValid,nativeWidth⟩ :=
    dispatch_tape signatures localBefore port.token output form
      ⟨localAfter,childEvents⟩ (Raw.step_conditions _ _ _ _ childStep).2.1
  have samePort : takenPort = port := Option.some.inj
    ((Raw.Ownership.take_state _ _ _ _ taken).1.symm.trans localLookup)
  subst takenPort
  have portPresent : port ∈ localBefore.live := by rw [localLive]; simp
  have shape : port.bits = port.wires.length := (valid.ports port portPresent).1
  have unique : port.wires.Nodup := by
    have localUnique := valid.frame
    change localBefore.frame.Nodup at localUnique
    simpa only [localFrame] using localUnique
  have width : form.Width port.wires.length := by simpa only [shape] using nativeWidth
  have controls : ∀ operation ∈ form.tape, ∀ control ∈ operation.controls,
      control.index < port.wires.length := by
    intro operation member control present
    simpa only [shape] using (tape_bounds _ _ _ tapeValid operation member).1 control present
  have targets : ∀ operation ∈ form.tape, ∀ axis ∈ QleisliKernel.Finite.targets operation.action,
      axis < port.wires.length := by
    intro operation member axis present
    simpa only [shape] using (tape_bounds _ _ _ tapeValid operation member).2 axis present
  have selfTape : form.tape.map (Semantics.RawTrace.localize (port.wires.map port.wires.idxOf)) = form.tape :=
    map_fixed _ _ (fun operation member => localize_self port.wires unique operation
      (controls operation member) (targets operation member))
  exact ⟨width,controls,targets,selfTape⟩

private theorem literal_result (signatures : List Basis) (before after : Raw.State)
    (port : Semantics.Raw.Port) (output : Nat) (form : Form) (events : List Semantics.Raw.Event)
    (ran : Raw.step signatures before (form.operation port.token output) = .ok ⟨after,events⟩)
    (lookup : before.live.find? (fun p => p.token == port.token) = some port)
    (width : form.Width port.wires.length) :
    after.reference = Semantics.RawTrace.insert
        {before.reference with live := before.reference.live.filter (fun p => p.token != port.token)}
        output port.wires ∧
      events = [.circuit before.frame.length (form.tape.map (Semantics.RawTrace.localize (portAxes before port)))] := by
  have actual := Raw.step_reference signatures before (form.operation port.token output) ⟨after,events⟩ ran
  have literal := literal_step before.reference port output form lookup width
  exact Prod.mk.inj (Option.some.inj (actual.symm.trans literal))

private theorem local_literal_result (signatures : List Basis) (before after : Raw.State)
    (port : Semantics.Raw.Port) (output : Nat) (form : Form) (events : List Semantics.Raw.Event)
    (ran : Raw.step signatures before (form.operation port.token output) = .ok ⟨after,events⟩)
    (entry : before.reference = ⟨[port],port.wires⟩) (tape : LocalTapeFacts form port) :
    after.reference = ⟨[⟨output,port.wires,port.wires.length⟩],port.wires⟩ ∧
      events = [.circuit port.wires.length form.tape] := by
  have live : before.live = [port] := congrArg Semantics.RawTrace.Interface.live entry
  have frame : before.frame = port.wires := congrArg Semantics.RawTrace.Interface.frame entry
  have lookup : before.live.find? (fun p => p.token == port.token) = some port := by simp [live]
  have data := literal_result signatures before after port output form events ran lookup tape.width
  constructor
  · simpa [entry,Semantics.RawTrace.insert] using data.1
  · simpa only [portAxes,frame,tape.selfTape] using data.2

private theorem literal_action (dependencies : List Dependency) (before : Raw.State)
    (port : Semantics.Raw.Port) (form : Form) (parent child : List Semantics.Raw.Event)
    (parentCircuit : parent = [.circuit before.frame.length
      (form.tape.map (Semantics.RawTrace.localize (portAxes before port)))])
    (childCircuit : child = [.circuit port.wires.length form.tape])
    (unique : (portAxes before port).Nodup) (tape : LocalTapeFacts form port)
    (values : Nat → ℂ) (base value : Nat) :
    Qleisli.Semantics.RawAction.events dependencies parent values (scatter base (portAxes before port) value) =
      Qleisli.Semantics.RawAction.events dependencies child
        (Qleisli.Semantics.RawAction.Locality.pull base (portAxes before port) values) value := by
  have lengthAxes : (portAxes before port).length = port.wires.length := List.length_map ..
  have selected := Qleisli.Semantics.RawAction.Locality.circuit_selected dependencies base
    (portAxes before port) unique form.tape
    (fun op member control held => lengthAxes.symm ▸ tape.controls op member control held)
    (fun op member axis held => lengthAxes.symm ▸ tape.targets op member axis held) values
  rw [parentCircuit,childCircuit]
  exact congrFun selected value

/-- Shared proof over the actual two native traces. Scope adapters below
supply lookup, entry and axis facts from their existing checked receipts. -/
private theorem one_owner_lift (dependencies : List Dependency) (operations : List Semantics.Raw.Op)
    (before after localBefore localAfter : Raw.State) (port : Semantics.Raw.Port) (output : Nat) (form : Form)
    (parent : RuntimeIntervalRawFold.Traced (dependencies.map (·.signature)) operations before after)
    (child : RuntimeIntervalRawFold.Traced (dependencies.map (·.signature)) operations localBefore localAfter)
    (parentLookup : before.live.find? (fun p => p.token == port.token) = some port)
    (childEntry : localBefore.reference = ⟨[port],port.wires⟩)
    (uniqueAxes : (portAxes before port).Nodup)
    (original : operations = [form.operation port.token output]) :
    Lift dependencies operations before after localBefore localAfter (portAxes before port) port output form := by
  subst operations
  obtain ⟨parentEvents,parentFold,parentTrace⟩ := parent
  obtain ⟨childEvents,childFold,childTrace⟩ := child
  let signatures := dependencies.map Dependency.signature
  have parentStep := singleton_step signatures (form.operation port.token output) before after parentEvents parentFold
  have childStep := singleton_step signatures (form.operation port.token output) localBefore localAfter childEvents childFold
  have tape := local_tape_facts signatures localBefore localAfter port output form childEvents childEntry childStep
  have parentResult := literal_result signatures before after port output form parentEvents parentStep parentLookup tape.width
  have childResult := local_literal_result signatures localBefore localAfter port output form childEvents childStep childEntry tape
  exact ⟨parentEvents,childEvents,{
    original := rfl
    parentFold := parentFold
    childFold := childFold
    parentTrace := parentTrace
    childTrace := childTrace
    childEntry := childEntry
    parentCircuit := parentResult.2
    childCircuit := childResult.2
    parentInterface := parentResult.1
    childInterface := childResult.1
    action := fun joint reference base value => literal_action dependencies before port form
      parentEvents childEvents parentResult.2 childResult.2 uniqueAxes tape (fun i => joint i reference) base value }⟩

/-- Use the same one-owner law directly on an original pure interval. Both
folds come from the actual interval and its retained pure-fragment read. -/
theorem interval_single_owner_lift {dependencies program block start count output role}
    (port : Semantics.Raw.Port)
    (frame : @RuntimePureInterval.Checked dependencies program block 1 start count [port.token] [output] [role])
    (form : Form) (selected : frame.selected = [port])
    (original : frame.operations = [form.operation port.token output]) :
    ∃ localEntry : Raw.State,
      (portAxes frame.interval.before.quantum port).Nodup ∧
      Lift dependencies frame.operations frame.interval.before.quantum frame.interval.after.quantum
        localEntry frame.pureBody.state (portAxes frame.interval.before.quantum port) port output form := by
  obtain ⟨parent,entry,entryRead,localValid,child⟩ := RuntimeIntervalRawFold.pure_interval_traces frame
  rw [selected] at entryRead
  let before := frame.interval.before.quantum
  have lookup : before.live.find? (fun p => p.token == port.token) = some port := by
    apply singleton_lookup
    simpa only [before,PureInterval.ports,selected] using frame.atEntry
  obtain ⟨work,left,read⟩ := frame.interval.prefixRead
  have valid := Raw.Ownership.valid before (Raw.Observation.checkOps_invariants _ _ _ _ _ work left read).1
  have within : port.wires ⊆ before.frame := by
    intro wire member
    exact valid.covered wire (List.mem_flatMap.mpr ⟨port,List.mem_of_find?_eq_some lookup,member⟩)
  have unique := (Raw.Ownership.valid _ localValid).frame
  change entry.frame.Nodup at unique
  have entryFrame := congrArg Semantics.RawTrace.Interface.frame entryRead
  change entry.frame = [port].flatMap (·.wires) at entryFrame
  rw [entryFrame,List.flatMap_singleton] at unique
  have axesUnique : (portAxes before port).Nodup := by
    apply List.Nodup.map_on _ unique
    intro a aMember b bMember same
    have one := RuntimeNamedFrameAxes.wireLookup before.frame (within aMember)
    have two := RuntimeNamedFrameAxes.wireLookup before.frame (within bMember)
    rw [same] at one
    exact Option.some.inj (one.symm.trans two)
  exact ⟨entry,axesUnique,one_owner_lift dependencies frame.operations before frame.interval.after.quantum entry frame.pureBody.state
    port output form parent child lookup (by simpa only [List.flatMap_singleton] using entryRead) axesUnique original⟩

/-- Pure named scopes keep their original native interface. Both literal
spellings use the same one-owner proof and actual source-relative axis order. -/
theorem pure_single_owner_lift {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    (port : Semantics.Raw.Port) (output : Nat) (form : Form)
    (selected : scope.selected = [port])
    (original : scope.operations = [form.operation port.token output]) :
    Lift dependencies scope.operations scope.interval.before.quantum scope.interval.after.quantum
      scope.localEntry.quantum scope.localAfter.quantum (RuntimeNamedFrameAxes.axes scope) port output form := by
  have axisRead : RuntimeNamedFrameAxes.axes scope = portAxes scope.interval.before.quantum port := by
    simp [RuntimeNamedFrameAxes.axes,RuntimeForestCode.portAxes,portAxes,selected]
  have inputIds : inputs = [port.token] := by
    simpa only [selected,List.map_cons,List.map_nil] using (RuntimeNamedFrameAxes.source_tokens scope).symm
  have parentLookup : scope.interval.before.quantum.live.find? (fun p => p.token == port.token) = some port := by
    apply singleton_lookup
    simpa only [PureInterval.ports,inputIds,selected] using scope.atEntry
  have childEntry : scope.localEntry.quantum.reference = ⟨[port],port.wires⟩ := by
    rw [local_interface scope,selected]
    simp only [List.flatMap_singleton]
  have traces := RuntimeIntervalRawFold.named_call_traces scope
  rw [axisRead]
  exact one_owner_lift dependencies scope.operations scope.interval.before.quantum scope.interval.after.quantum
    scope.localEntry.quantum scope.localAfter.quantum port output form traces.1 traces.2 parentLookup childEntry
    (by simpa only [axisRead] using RuntimeNamedFrameAxes.distinct scope) original

/-- A genuine mixed named step supplies the original ordered owner bindings.
Only its actual one-pure-instruction slice is used here; all surrounding
ordinary values, observation histories, effects and spectators remain in scope
and boundary. No source-read, native checker or action reconstruction reruns. -/
theorem mixed_single_owner_lift {dependencies program block start count inputs ordinary effect
    sources caller before child retired childValue}
    {event : SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired childValue)
    (binding : RuntimeOwnerMap.Binding) (oneInput : boundary.input.ordered = [binding])
    (form : Form) (output : Nat)
    (literal : (block.operations.drop start).take count =
      [Semantics.Observation.Op.pure (form.operation binding.port.token output)]) :
    Lift dependencies [form.operation binding.port.token output] scope.interval.before.quantum scope.interval.after.quantum
      scope.localEntry.quantum scope.localAfter.quantum (RuntimeNamedFrameAxes.mixedAxes scope) binding.port output form := by
  have selected : scope.selected = [binding.port] := by
    rw [RuntimeNamedFrameAxes.mixed_bound_ports scope boundary,oneInput]
    rfl
  have axisRead : RuntimeNamedFrameAxes.mixedAxes scope = portAxes scope.interval.before.quantum binding.port := by
    simp [RuntimeNamedFrameAxes.mixedAxes,RuntimeForestCode.portAxes,portAxes,selected]
  have initial := RuntimeNamedFrameAxes.mixedAxes_input scope
  have inputIds : inputs = [binding.port.token] := by
    simpa only [selected,List.map_cons,List.map_nil] using initial.1.symm
  have parentLookup : scope.interval.before.quantum.live.find?
      (fun p => p.token == binding.port.token) = some binding.port := by
    apply singleton_lookup
    simpa only [PureInterval.ports,inputIds,selected] using scope.atEntry
  have childEntry : scope.localEntry.quantum.reference = ⟨[binding.port],binding.port.wires⟩ := by
    simpa only [selected,List.flatMap_singleton] using initial.2.1
  have traces := RuntimeIntervalRawFold.mixed_call_traces scope [form.operation binding.port.token output] literal
  rw [axisRead]
  exact one_owner_lift dependencies [form.operation binding.port.token output]
    scope.interval.before.quantum scope.interval.after.quantum scope.localEntry.quantum scope.localAfter.quantum
    binding.port output form traces.1 traces.2 parentLookup childEntry
    (by simpa only [axisRead] using (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1) rfl

/-- The complete native local output set determines this exact token list.
This is not a width-based owner or return-order inference. -/
theorem Facts.returned_tokens {dependencies operations before after localBefore localAfter axes port output form parentEvents childEvents}
    (facts : Facts dependencies operations before after localBefore localAfter axes port output form parentEvents childEvents)
    (returned : List Semantics.Raw.Port) (complete : returned = localAfter.live) : returned.map (·.token) = [output] := by
  have exit := congrArg Semantics.RawTrace.Interface.live facts.childInterface
  change localAfter.live = [⟨output,port.wires,port.wires.length⟩] at exit
  rw [complete,exit]
  rfl

/-- Exact action of the real local quantum fragment. The final `.reorder`
remains present, even for a canonical one-owner output; dropping it on all Nat
amplitudes would be false outside the finite carrier. -/
theorem Facts.fragment_action {dependencies operations before after localBefore localAfter axes port output form parentEvents childEvents}
    (facts : Facts dependencies operations before after localBefore localAfter axes port output form parentEvents childEvents)
    (values : Nat → ℂ) :
    Qleisli.Semantics.RawAction.program dependencies (RuntimePureInterval.fragment [port] operations [output]) values =
      some (Qleisli.Semantics.RawAction.event dependencies
        (.reorder port.wires.length (port.wires.map port.wires.idxOf))
        (Qleisli.Semantics.RawAction.circuit dependencies form.tape values)) := by
  have frame := congrArg Semantics.RawTrace.Interface.frame facts.childEntry
  change localBefore.frame = port.wires at frame
  have actual : RuntimeLocalEvents.trace ⟨[port],port.wires⟩ operations =
      some ⟨⟨[⟨output,port.wires,port.wires.length⟩],port.wires⟩,
        [.circuit port.wires.length form.tape],port.wires.length⟩ := by
    simpa only [facts.childEntry,facts.childInterface,facts.childCircuit,frame] using facts.childTrace
  change operations.foldlM Semantics.RawTrace.advance
    ⟨⟨[port],port.wires⟩,[],port.wires.length⟩ = _ at actual
  unfold Qleisli.Semantics.RawAction.program Semantics.RawTrace.run
  have initial : Semantics.RawTrace.initial [port] = ⟨[port],port.wires⟩ := by
    simp only [Semantics.RawTrace.initial,List.flatMap_singleton]
  simp only [RuntimePureInterval.fragment,initial,actual,bind,Option.bind,pure]
  simp [Semantics.RawTrace.finish,Semantics.RawTrace.axes,Qleisli.Semantics.RawAction.events]
  rfl

/-- The pure scope's actual returned tokens, not a supplied output ordering,
close the local fragment statement. Full caller `finish` is still separate. -/
theorem pure_fragment_action {dependencies program block start count inputs}
    (scope : @RuntimeCallInterval.Checked dependencies program block start count inputs)
    {port output form} (selected : scope.selected = [port])
    (lifted : Lift dependencies scope.operations scope.interval.before.quantum scope.interval.after.quantum
      scope.localEntry.quantum scope.localAfter.quantum (RuntimeNamedFrameAxes.axes scope) port output form)
    (values : Nat → ℂ) :
    Qleisli.Semantics.RawAction.program dependencies
      (RuntimePureInterval.fragment scope.selected scope.operations (scope.returned.map (·.token))) values =
      some (Qleisli.Semantics.RawAction.event dependencies
        (.reorder port.wires.length (port.wires.map port.wires.idxOf))
        (Qleisli.Semantics.RawAction.circuit dependencies form.tape values)) := by
  obtain ⟨parentEvents,childEvents,facts⟩ := lifted
  rw [selected,facts.returned_tokens scope.returned scope.complete]
  exact facts.fragment_action values

/-- The same local quantum-slice conclusion applies to the actual mixed
scope. This does not replace its ordinary outputs or complete hidden history
by a pure program and does not sharpen the original event's public effect. -/
theorem mixed_fragment_action {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    {operations port output form} (selected : scope.selected = [port])
    (lifted : Lift dependencies operations scope.interval.before.quantum scope.interval.after.quantum
      scope.localEntry.quantum scope.localAfter.quantum (RuntimeNamedFrameAxes.mixedAxes scope) port output form)
    (values : Nat → ℂ) :
    Qleisli.Semantics.RawAction.program dependencies
      (RuntimePureInterval.fragment scope.selected operations (scope.returned.map (·.token))) values =
      some (Qleisli.Semantics.RawAction.event dependencies
        (.reorder port.wires.length (port.wires.map port.wires.idxOf))
        (Qleisli.Semantics.RawAction.circuit dependencies form.tape values)) := by
  obtain ⟨parentEvents,childEvents,facts⟩ := lifted
  rw [selected,facts.returned_tokens scope.returned scope.complete]
  exact facts.fragment_action values

/-- A source-indexed pure child: the actual common traversal emitted precisely
this primitive node, with the true event, owner transition, source-kind and
checker receipt. Local source owners need not have the caller's ordinals. -/
structure BoundSinglePrimitive {artifact owner name arguments source event position}
    {ordinary : @RuntimeNamedCallsSource.Ordinary artifact owner name arguments source event position}
    {root : Validity.Root} {program : Semantics.Observation.Program}
    {block : RuntimeInterval.Block root.dependencies program} {before : RuntimeStructuralAction.SourceState}
    (checked : RuntimeNamedOrdinaryLocal.Checked ordinary root block before) where
  input : RuntimeOwnerMap.Binding
  oneInput : checked.frame.inputs = [input]
  output : Nat
  form : Form
  literal : checked.frame.scope.operations = [form.operation input.port.token output]
  role : Semantics.SourceOwners.Owner
  kind : RuntimePrimitiveAction.Kind
  action : RuntimePrimitiveAction.Checked checked.frame.scope.prepared.block 0 1 input.port.token output role kind
  original : RuntimePrimitiveSource.Checked action
  emitted : checked.nested.actions = [.primitive action original]

/-- The original event's PrimitiveOperator meaning and CodeSpace equation are
retained by `bound.original`/`bound.action`; this theorem lifts its actual
literal tape without replacing them by an arbitrary caller matrix. -/
theorem bound_single_primitive_lift {artifact owner name arguments source event position ordinary root program block before}
    (checked : @RuntimeNamedOrdinaryLocal.Checked artifact owner name arguments source event position
      ordinary root program block before) (bound : BoundSinglePrimitive checked) :
    Lift root.dependencies checked.frame.scope.operations checked.frame.scope.interval.before.quantum
      checked.frame.scope.interval.after.quantum checked.frame.scope.localEntry.quantum
      checked.frame.scope.localAfter.quantum (RuntimeNamedFrameAxes.axes checked.frame.scope)
      bound.input.port bound.output bound.form := by
  apply pure_single_owner_lift checked.frame.scope bound.input.port bound.output bound.form
  · rw [RuntimeNamedFrameAxes.bound_ports checked.frame,bound.oneInput]
    rfl
  · exact bound.literal

#print axioms pure_single_owner_lift
#print axioms mixed_single_owner_lift
#print axioms Facts.fragment_action
#print axioms bound_single_primitive_lift

end Qleisli.RuntimeNamedGateLift
