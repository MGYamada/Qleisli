import QleisliKernel.Qirf.RuntimeStructuralAction

/-! Bind the original register index to the literal Raw owner repartition.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeRegisterAction
open QleisliKernel Finite SourceTypes
open RuntimeStructuralAction (SourceState widths)

private def outputTokens (kind : CallName.Primitive) (index : Nat)
    (inputs : List Semantics.Raw.Port) (operations : List Semantics.Raw.Op) : WorkM (List Nat) := do
  match kind,inputs,operations with
  | .takeBit,[port],[.split input front tail leftBits,
      .split next selected suffix selectedBits,.join left right rest] =>
    guard (input == port.token && leftBits == index && next == tail &&
      selectedBits == 1 && left == front && right == suffix) .request
    return [selected,rest]
  | .putBit,[bit,rest],[.split input front suffix leftBits,
      .join left selected head,.join next right output] =>
    guard (input == rest.token && leftBits == index && left == front &&
      selected == bit.token && next == head && right == suffix) .request
    return [output]
  | _,_,_ => throw .request

private def outputWires (kind : CallName.Primitive) (index : Nat)
    (inputs : List Semantics.Raw.Port) : List (List Nat) :=
  match kind,inputs with
  | .takeBit,[port] =>
    [(port.wires.drop index).take 1,port.wires.take index ++ port.wires.drop (index+1)]
  | .putBit,[bit,rest] =>
    [rest.wires.take index ++ bit.wires ++ rest.wires.drop index]
  | _,_ => []

private def repartitions : Semantics.Raw.Op → Prop
  | .split .. | .join .. => True
  | _ => False

private theorem outputTokens_repartitions {kind index inputs operations result}
    (read : RuntimeInterval.Computed (outputTokens kind index inputs operations) result) :
    ∀ operation ∈ operations, repartitions operation := by
  obtain ⟨work,left,checked⟩ := read
  unfold outputTokens at checked
  split at checked
  · simp [repartitions]
  · simp [repartitions]
  · cases checked

private theorem repartition_step {operation before after events} (shape : repartitions operation)
    (read : Semantics.RawTrace.step before operation = some (after,events)) :
    after.frame = before.frame ∧ events = [] := by
  cases operation <;> try cases shape
  case split input left right leftBits =>
    cases found : before.live.find? (fun port => port.token == input) <;>
      simp_all [Semantics.RawTrace.step, Semantics.RawTrace.take, Semantics.RawTrace.insert, bind, Option.bind, pure]
    exact (congrArg Semantics.RawTrace.Interface.frame read.1).symm
  case join left right output =>
    let remaining := before.live.filter (fun port => port.token != left)
    cases first : before.live.find? (fun port => port.token == left)
    · simp [Semantics.RawTrace.step, Semantics.RawTrace.take, first, bind, Option.bind] at read
    · cases second : remaining.find? (fun port => port.token == right) <;>
        simp_all [Semantics.RawTrace.step, Semantics.RawTrace.take, Semantics.RawTrace.insert, bind, Option.bind, pure, remaining]
      exact (congrArg Semantics.RawTrace.Interface.frame read.1).symm

private theorem repartition_trace {operations : List Semantics.Raw.Op}
    (shape : ∀ operation ∈ operations, repartitions operation)
    {before after : Semantics.RawTrace.Prepared}
    (read : operations.foldlM Semantics.RawTrace.advance before = some after) :
    after.state.frame = before.state.frame ∧ after.events = before.events := by
  induction operations generalizing before with
  | nil =>
    have same : before = after := Option.some.inj read
    subst after
    exact ⟨rfl,rfl⟩
  | cons operation rest ih =>
    simp only [List.foldlM_cons, Semantics.RawTrace.advance] at read
    cases split : Semantics.RawTrace.step before.state operation with
    | none => simp [split, bind, Option.bind] at read
    | some result =>
      obtain ⟨state, events⟩ := result
      have step := repartition_step (shape operation List.mem_cons_self) split
      have tail : rest.foldlM Semantics.RawTrace.advance
          {before with state := state,events := before.events ++ events} = some after := by
        simpa only [split, bind, Option.bind, pure] using read
      have kept := ih (fun next held => shape next (List.mem_cons_of_mem _ held)) tail
      exact ⟨kept.1.trans step.1,kept.2.trans (by rw [step.2,List.append_nil])⟩

structure Checked {dependencies program sources caller}
    (block : RuntimeInterval.Block dependencies program) (start count : Nat)
    (event : SourceRuntimeContext.RegisterEvent sources caller) (before : SourceState) where
  interval : RuntimeInterval.Checked block start count
  operations : List Semantics.Raw.Op
  literal : (block.operations.drop start).take count = operations.map Semantics.Observation.Op.pure
  beforeFrame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before
  sameBefore : beforeFrame.bindings = before.bindings
  inputs : List Semantics.Raw.Port
  inputsRead : RuntimeInterval.Computed
    ((RuntimeOwnerMap.order event.consumed before.bindings).map (·.map (·.port))) inputs
  outputs : List Semantics.Raw.Port
  outputsRead : PureInterval.ports interval.after (outputs.map (·.token)) = some outputs
  index : Nat
  originalIndex : (event.application.arguments.map (·.value))[1]? = some index
  tokenOrder : RuntimeInterval.Computed (outputTokens event.kind index inputs operations) (outputs.map (·.token))
  wireOrder : outputs.map (·.wires) = outputWires event.kind index inputs
  inputWidths : widths inputs event.consumed = true
  outputWidths : widths outputs event.allocated = true
  spectators : PureInterval.spectators interval.before (inputs.map (·.token)) =
    PureInterval.spectators interval.after (outputs.map (·.token))
  after : SourceState
  bindings : after.bindings = before.bindings.filter (fun binding => !event.consumed.contains binding.owner) ++
    (event.allocated.zip outputs).map (fun (owner,port) => ⟨owner,port⟩)
  issued : after.issued = before.issued ++ event.allocated
  ordinal : after.nextOrdinal = event.afterOrdinal
  afterFrame : RuntimeOwnerMap.Checked (after.bindings.map (·.owner)) interval.after
  sameFrame : afterFrame.bindings = after.bindings

/-- A successful literal token read identifies which original register
operation supplied the consumed and allocated owner lists. -/
theorem Checked.register_owners {dependencies program sources caller block start count event before}
    (action : @Checked dependencies program sources caller block start count event before) :
    (event.consumed.map (·.ordinal)).Nodup ∧
      ∀ owner ∈ event.allocated ++ event.consumed,
        owner.basis = [.bit] ∨ ∃ width, owner.basis = [.bits width] := by
  obtain ⟨work,left,checked⟩ := action.tokenOrder
  have kind : event.kind = .takeBit ∨ event.kind = .putBit := by
    unfold outputTokens at checked
    split at checked
    · exact .inl (by assumption)
    · exact .inr (by assumption)
    · cases checked
  exact SourceRegisterApplication.apply_register_owners kind event.applied

theorem Checked.take_wires {dependencies program sources caller block start count event before}
    (action : @Checked dependencies program sources caller block start count event before)
    {port : Semantics.Raw.Port} (kind : event.kind = .takeBit) (inputs : action.inputs = [port]) :
    action.outputs.map (·.wires) =
      [(port.wires.drop action.index).take 1,port.wires.take action.index ++ port.wires.drop (action.index+1)] := by
  rw [action.wireOrder,kind,inputs]
  rfl

theorem Checked.put_wires {dependencies program sources caller block start count event before}
    (action : @Checked dependencies program sources caller block start count event before)
    {bit rest : Semantics.Raw.Port} (kind : event.kind = .putBit) (inputs : action.inputs = [bit,rest]) :
    action.outputs.map (·.wires) =
      [rest.wires.take action.index ++ bit.wires ++ rest.wires.drop action.index] := by
  rw [action.wireOrder,kind,inputs]
  rfl

/-- The literal three-operation repartition changes only logical ownership.
It keeps the physical frame and emits no quantum event. -/
theorem Checked.trace_frame {dependencies program sources caller block start count event before}
    (action : @Checked dependencies program sources caller block start count event before)
    {after : Semantics.RawTrace.Prepared}
    (traced : Semantics.RawTrace.interval action.interval.before.quantum.reference action.operations = some after) :
    after.state.frame = action.interval.before.quantum.frame ∧ after.events = [] :=
  repartition_trace (outputTokens_repartitions action.tokenOrder) traced

/-- The extracted bit and retained register partition the same physical wires,
with the extracted axis first in source result order. Insertion preserves the
order on either side of the bit and restores the same wire set. -/
theorem Checked.wires_permute {dependencies program sources caller block start count event before}
    (action : @Checked dependencies program sources caller block start count event before) :
    (action.outputs.flatMap (·.wires)).Perm (action.inputs.flatMap (·.wires)) := by
  obtain ⟨work,left,checked⟩ := action.tokenOrder
  have literal := action.wireOrder
  unfold outputTokens at checked
  unfold List.flatMap
  rw [literal]
  split at checked
  case h_1 _ _ port _ _ _ _ _ _ _ _ _ _ _ kindEq inputsEq _ =>
    simp only [kindEq, inputsEq, outputWires, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil]
    have pieces := List.take_append_drop 1 (port.wires.drop action.index)
    rw [List.drop_drop] at pieces
    calc
      List.Perm _ (port.wires.take action.index ++ ((port.wires.drop action.index).take 1 ++
          port.wires.drop (action.index + 1))) := by
        rw [← List.append_assoc, ← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm
      List.Perm _ port.wires := by rw [pieces, List.take_append_drop]
  case h_2 _ _ _ bit rest _ _ _ _ _ _ _ _ _ _ kindEq inputsEq _ =>
    simp only [kindEq, inputsEq, outputWires, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil]
    calc
      List.Perm _ (bit.wires ++ (rest.wires.take action.index ++ rest.wires.drop action.index)) := by
        rw [← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm
      List.Perm _ _ := by rw [List.take_append_drop]
  case h_3 => cases checked

def read {dependencies program sources caller} {block : RuntimeInterval.Block dependencies program} {start count}
    (interval : RuntimeInterval.Checked block start count)
    (event : SourceRuntimeContext.RegisterEvent sources caller) (before : SourceState) :
    WorkM (Checked block start count event before) := do
  exactWork (Exact.charge (64*(SourceRuntimeValues.valueFields event.value+
    (event.arguments.map SourceRuntimeValues.valueFields).sum+
    Raw.OwnerFlow.fields before.issued+Raw.OwnerFlow.fields (before.bindings.map (·.owner))+
    block.operations.length+before.issued.length*event.allocated.length+1)))
  guard (before.nextOrdinal == event.nextOrdinal &&
    event.allocated.all (fun owner => !before.issued.any (fun previous => previous.ordinal == owner.ordinal))) .request
  let incoming ← RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.before before.bindings
  let inputs ← NaturalAffine.witness ((RuntimeOwnerMap.order event.consumed before.bindings).map (·.map (·.port)))
  match originalIndex : (event.application.arguments.map (·.value))[1]? with
  | none => throw .request
  | some axis =>
    match literal : Sector.pureOps ((block.operations.drop start).take count) with
    | none => throw .request
    | some operations =>
      let tokens ← NaturalAffine.witness (outputTokens event.kind axis inputs.val operations)
      let some outputs := PureInterval.ports interval.after tokens.val | throw .request
      if returned : PureInterval.ports interval.after (outputs.map (·.token)) = some outputs ∧
          outputs.map (·.token) = tokens.val ∧ outputs.map (·.wires) = outputWires event.kind axis inputs.val ∧
          widths inputs.val event.consumed = true ∧ widths outputs event.allocated = true ∧
          PureInterval.spectators interval.before (inputs.val.map (·.token)) =
            PureInterval.spectators interval.after (outputs.map (·.token)) then
        let after : SourceState :=
          ⟨before.bindings.filter (fun binding => !event.consumed.contains binding.owner) ++
              (event.allocated.zip outputs).map (fun (owner,port) => ⟨owner,port⟩),
            before.issued ++ event.allocated,event.afterOrdinal⟩
        let frame ← RuntimeOwnerMap.checkBindings (after.bindings.map (·.owner)) interval.after after.bindings
        return ⟨interval,operations,Sector.pureOps_bound _ _ literal,incoming.val,incoming.property,inputs.val,
          by with_reducible exact inputs.property,outputs,returned.1,axis,originalIndex,
          by rw [returned.2.1]; with_reducible exact tokens.property,
          returned.2.2.1,returned.2.2.2.1,returned.2.2.2.2.1,returned.2.2.2.2.2,
          after,rfl,rfl,rfl,frame.val,frame.property⟩
      else throw .request

#print axioms Checked.trace_frame
#print axioms Checked.wires_permute

end QleisliKernel.Qirf.RuntimeRegisterAction
