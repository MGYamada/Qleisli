import QleisliKernel.Qirf.RuntimeNamedCallFrame
import QleisliKernel.Qirf.RuntimeCallScope
import QleisliKernel.Qirf.RuntimeSelectionPartition
import QleisliKernel.Qirf.RuntimeForestCode
import QleisliKernel.Raw.Trace

/-! Identify each local input wire of an actual named call with its position
in the enclosing Raw frame. Port order includes zero-width arguments and the
parent frame includes spectators. These facts concern entry layouts.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedFrameAxes
open QleisliKernel Finite SourceTypes
open QleisliKernel.Semantics.Raw (Port)

private theorem selectedPorts (live : List Port) (tokens : List Nat)
    -- The selected port list may contain Unit ports, so token order is kept.
    (ports : List Port) (found : PureInterval.portsOf live tokens = some ports) :
    ports ⊆ live ∧ ports.map (·.token) = tokens := by
  induction tokens generalizing ports with
  | nil =>
    have same : ports = [] := (Option.some.inj found).symm
    subst ports
    simp
  | cons token rest ih =>
    cases first : live.find? (fun port => port.token == token) with
    | none => simp [PureInterval.portsOf,List.mapM_cons,first] at found
    | some port =>
      cases tail : rest.mapM (fun token => live.find? (fun port => port.token == token)) with
      | none => simp [PureInterval.portsOf,List.mapM_cons,first,tail] at found
      | some later =>
        have same : port :: later = ports := by simpa [PureInterval.portsOf,List.mapM_cons,first,tail] using found
        subst ports
        obtain ⟨inside,order⟩ := ih later tail
        have tokenEq : port.token = token :=
          beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == token) first)
        exact ⟨List.cons_subset.mpr ⟨List.mem_of_find?_eq_some first,inside⟩,by simp [tokenEq,order]⟩

private theorem classicalInputs (ids : List Nat) (state result : Raw.Observation.State)
    (ok : ids.foldlM Raw.Observation.insertClassical state = .ok result) :
    result.quantum = state.quantum ∧ result.classical = state.classical ++ ids.map (fun i => (i,state.scope)) := by
  induction ids generalizing state with
  | nil =>
    have same := Except.ok.inj ok
    subst result
    simp
  | cons id rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨middle,first,tail⟩ := Finite.except_bind_success _ _ _ ok
    obtain ⟨_,_,returned⟩ := Finite.except_bind_success _ _ _ first
    have same : middle = {state with classical := state.classical ++ [(id,state.scope)]} := (Except.ok.inj returned).symm
    subst middle
    obtain ⟨quantum,table⟩ := ih _ tail
    exact ⟨quantum,by simpa [List.append_assoc] using table⟩

theorem initialized {program state}
    (read : RuntimeInterval.Computed (PureInterval.initial program) state) :
    state.quantum.reference = ⟨program.inputs,program.inputs.flatMap (·.wires)⟩ ∧ Raw.stateValid state.quantum = true ∧
      state.classical = program.classicalInputs.map (fun i => (i,0)) := by
  obtain ⟨_,_,ran⟩ := read
  unfold PureInterval.initial at ran
  obtain ⟨quantum,_,opened,rest⟩ := Finite.bind_success _ _ _ _ _ ran
  have actual : program.inputs.foldlM Raw.input {} = .ok quantum := (Finite.lift_success _ _ _ _ opened).1
  have ⟨same,table⟩ := classicalInputs program.classicalInputs {quantum} state (Finite.lift_success _ _ _ _ rest).1
  rw [same]
  exact ⟨by simpa only [List.nil_append] using Raw.inputs_reference program.inputs {} quantum actual,
    Raw.inputs_valid program.inputs {} quantum (by decide) actual,table⟩

variable {dependencies : List Semantics.Finite.Dependency} {program : Semantics.Observation.Program}
  {block : RuntimeInterval.Block dependencies program} {start count : Nat} {inputs : List Nat}

/-- The axes of the call use the same wire lookup as RawTrace.localize. -/
def axes (scope : RuntimeCallInterval.Checked block start count inputs) : List Nat :=
  RuntimeForestCode.portAxes scope.interval.before.quantum.frame scope.selected

theorem source_tokens (scope : RuntimeCallInterval.Checked block start count inputs) :
    scope.selected.map (·.token) = inputs :=
  (selectedPorts _ inputs scope.selected scope.atEntry).2

theorem local_frame (scope : RuntimeCallInterval.Checked block start count inputs) :
    scope.localEntry.quantum.frame = scope.selected.flatMap (·.wires) :=
  congrArg Semantics.RawTrace.Interface.frame (initialized scope.entryRead).1

/-- This is the entry used by the child block in the common body walk. -/
theorem child_interface (scope : RuntimeCallInterval.Checked block start count inputs) :
    scope.prepared.block.entry.quantum.reference = ⟨scope.selected,scope.selected.flatMap (·.wires)⟩ :=
  (initialized scope.prepared.inputRead).1

private theorem before_valid (interval : RuntimeInterval.Checked block start count) :
    Raw.stateValid interval.before.quantum = true := by
  obtain ⟨w,left,ran⟩ := interval.prefixRead
  exact (Raw.Observation.checkOps_invariants _ _ _ _ _ w left ran).1

private theorem selected_subset (interval : RuntimeInterval.Checked block start count) (ports : List Port)
    (read : PureInterval.ports interval.before inputs = some ports) :
    ports.flatMap (·.wires) ⊆ interval.before.quantum.frame := by
  intro wire member
  obtain ⟨port,portIn,onPort⟩ := List.mem_flatMap.mp member
  have live := (selectedPorts _ inputs ports read).1 portIn
  exact (Raw.Ownership.valid _ (before_valid interval)).covered wire (List.mem_flatMap.mpr ⟨port,live,onPort⟩)

theorem wires_in_frame (scope : RuntimeCallInterval.Checked block start count inputs) :
    scope.selected.flatMap (·.wires) ⊆ scope.interval.before.quantum.frame :=
  selected_subset scope.interval scope.selected scope.atEntry

theorem wireLookup (frame : List Nat) {wire : Nat} (member : wire ∈ frame) :
    frame[frame.idxOf wire]? = some wire := by
  induction frame with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : first = wire
    · subst first; simp
    · have inRest : wire ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      simp only [List.idxOf_cons,cond_eq_ite,beq_iff_eq,if_neg same,List.getElem?_cons_succ,ih inRest]

/-- Every position of the local frame recovers the very same physical wire
from the parent. A wire's numeric identifier need not equal its frame index. -/
theorem selected_at (scope : RuntimeCallInterval.Checked block start count inputs) {localAxis wire : Nat}
    (atLocal : scope.prepared.block.entry.quantum.frame[localAxis]? = some wire) :
    (axes scope)[localAxis]? = some (scope.interval.before.quantum.frame.idxOf wire) ∧
      scope.interval.before.quantum.frame[scope.interval.before.quantum.frame.idxOf wire]? = some wire := by
  have frame := congrArg Semantics.RawTrace.Interface.frame (child_interface scope)
  change scope.prepared.block.entry.quantum.frame = scope.selected.flatMap (·.wires) at frame
  rw [frame] at atLocal
  exact ⟨by rw [axes,RuntimeForestCode.portAxes,List.getElem?_map,atLocal] <;> rfl,
    wireLookup _ (wires_in_frame scope (List.mem_of_getElem? atLocal))⟩

theorem bounded (scope : RuntimeCallInterval.Checked block start count inputs) :
    ∀ axis ∈ axes scope, axis < scope.interval.before.quantum.frame.length := by
  intro axis member
  obtain ⟨wire,inside,rfl⟩ := List.mem_map.mp member
  exact List.idxOf_lt_length_of_mem (wires_in_frame scope inside)

private theorem distinctLookup (frame wires : List Nat) (nodup : wires.Nodup) (inside : wires ⊆ frame) :
    (wires.map frame.idxOf).Nodup := by
  induction wires with
  | nil => simp
  | cons w rest ih =>
    obtain ⟨first,others⟩ := List.nodup_cons.mp nodup
    obtain ⟨present,subset⟩ := List.cons_subset.mp inside
    apply List.nodup_cons.mpr
    refine ⟨?_,ih others subset⟩
    intro found
    obtain ⟨v,member,same⟩ := List.mem_map.mp found
    have vRead := wireLookup frame (subset member)
    rw [same] at vRead
    have equal := Option.some.inj (vRead.symm.trans (wireLookup frame present))
    exact first (equal ▸ member)

theorem distinct (scope : RuntimeCallInterval.Checked block start count inputs) : (axes scope).Nodup := by
  have localValid := (Raw.Ownership.valid _ (initialized scope.entryRead).2.1).frame
  change scope.localEntry.quantum.frame.Nodup at localValid
  rw [local_frame scope] at localValid
  exact distinctLookup _ _ localValid (wires_in_frame scope)

/-- Only the concrete entry interface and literal token lookup are needed
to specialize the generic axis list for an original named receipt. -/
theorem axes_of_layout (scope : RuntimeCallInterval.Checked block start count inputs)
    (layout : Semantics.RawTrace.Interface) (ports : List Port)
    (entry : scope.interval.before.quantum.reference = layout)
    (selection : PureInterval.portsOf layout.live inputs = some ports) :
    axes scope = RuntimeForestCode.portAxes layout.frame ports := by
  have live := congrArg Semantics.RawTrace.Interface.live entry
  have frame := congrArg Semantics.RawTrace.Interface.frame entry
  change scope.interval.before.quantum.live = layout.live at live
  change scope.interval.before.quantum.frame = layout.frame at frame
  have actual := scope.atEntry
  change PureInterval.portsOf scope.interval.before.quantum.live inputs = some scope.selected at actual
  rw [live,selection] at actual
  rw [axes,frame,← Option.some.inj actual]

theorem bound_input_order {sources caller event callee position before}
    (frame : @RuntimeNamedCallFrame.Checked sources caller dependencies program event callee block position before) :
    frame.inputs ⊆ before.bindings ∧ frame.inputs.map (·.owner) = event.inputOwners ∧
      frame.scope.selected.map (·.token) = frame.inputs.map (·.port.token) := by
  obtain ⟨contained,ordered⟩ := RuntimeSelectionPartition.order_values _ _ _ frame.inputRead
  exact ⟨contained,ordered,source_tokens frame.scope⟩

theorem tokenLookup (live : List Port) (p : Port) (unique : (live.map (·.token)).Nodup)
    (member : p ∈ live) : live.find? (fun port => port.token == p.token) = some p := by
  induction live with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | later
    · simp
    · have different : first.token ≠ p.token := by
        intro same
        apply fresh
        change first.token ∈ rest.map Port.token
        rw [same]
        exact List.mem_map_of_mem later
      simp [different,ih tail later]

private theorem lookupPorts (live ports : List Port) (unique : (live.map (·.token)).Nodup) (inside : ports ⊆ live) :
    PureInterval.portsOf live (ports.map (·.token)) = some ports := by
  induction ports with
  | nil => rfl
  | cons p rest ih =>
    have ⟨member,tail⟩ := List.cons_subset.mp inside
    have later := ih tail
    unfold PureInterval.portsOf at later ⊢
    simp [List.mapM_cons,tokenLookup live p unique member,later]

/-- The complete selected ports, including every ordered wire and Unit token,
are the source input bindings validated on the same caller interval. -/
theorem bound_ports {sources caller event callee position before}
    (frame : @RuntimeNamedCallFrame.Checked sources caller dependencies program event callee block position before) :
    frame.scope.selected = frame.inputs.map (·.port) := by
  have contained := (bound_input_order frame).1
  have complete := frame.callerFrame.complete
  rw [frame.sameCaller] at complete
  have subset : frame.inputs.map (·.port) ⊆ frame.scope.interval.before.quantum.live := by
    rw [frame.sameInterval]
    intro p member
    obtain ⟨binding,found,rfl⟩ := List.mem_map.mp member
    exact complete.mem_iff.mp (List.mem_map_of_mem (f := RuntimeOwnerMap.Binding.port) (contained found))
  have unique := (Raw.Ownership.valid _ (before_valid frame.scope.interval)).owners
  have selected := lookupPorts _ _ unique subset
  have genuine := frame.scope.atEntry
  exact Option.some.inj (genuine.symm.trans (by simpa only [List.map_map,Function.comp_def] using selected))

theorem mixedAxes_input {ordinary effect}
    (scope : RuntimeCallScope.Checked block start count inputs ordinary effect) :
    scope.selected.map (·.token) = inputs ∧
    scope.localEntry.quantum.reference = ⟨scope.selected,scope.selected.flatMap (·.wires)⟩ ∧
    scope.prepared.block.entry.quantum.reference = ⟨scope.selected,scope.selected.flatMap (·.wires)⟩ ∧
    scope.prepared.block.entry.classical = (RuntimeOrdinaryBody.visibleIds scope.interval.before).map (fun i => (i,0)) := by
  have opening := initialized scope.entryRead
  have child := initialized scope.prepared.inputRead
  refine ⟨(selectedPorts _ _ _ scope.atEntry).2,opening.1,child.1,?_⟩
  change scope.prepared.entry.classical = _
  have ids : scope.prepared.entry.classical = (scope.visible.table.map Prod.fst).map (fun i => (i,0)) := child.2.2
  rw [ids,scope.visible.complete]

def mixedAxes {ordinary effect} (scope : RuntimeCallScope.Checked block start count inputs ordinary effect) : List Nat :=
  RuntimeForestCode.portAxes scope.interval.before.quantum.frame scope.selected

theorem mixedAxes_bounds {ordinary effect} (scope : RuntimeCallScope.Checked block start count inputs ordinary effect) :
    (mixedAxes scope).Nodup ∧ ∀ axis ∈ mixedAxes scope, axis < scope.interval.before.quantum.frame.length := by
  have valid := (Raw.Ownership.valid _ (initialized scope.entryRead).2.1).frame
  change scope.localEntry.quantum.frame.Nodup at valid
  have same := congrArg Semantics.RawTrace.Interface.frame (mixedAxes_input scope).2.1
  change scope.localEntry.quantum.frame = scope.selected.flatMap (·.wires) at same
  rw [same] at valid
  have subset := selected_subset scope.interval scope.selected scope.atEntry
  refine ⟨distinctLookup _ _ valid subset,?_⟩
  intro axis member
  obtain ⟨wire,inside,rfl⟩ := List.mem_map.mp member
  exact List.idxOf_lt_length_of_mem (subset inside)

theorem mixed_bound_ports {sources caller ordinary effect before child retired childValue}
    {event : SourceRuntimeContext.NamedEvent sources caller}
    (scope : RuntimeCallScope.Checked block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired childValue) :
    scope.selected = boundary.input.ordered.map (·.port) :=
  Option.some.inj (scope.atEntry.symm.trans boundary.input.atEntry)

theorem mixed_bound_axes {sources caller ordinary effect before child retired childValue}
    {event : SourceRuntimeContext.NamedEvent sources caller}
    (scope : RuntimeCallScope.Checked block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired childValue) :
    boundary.input.ordered.map (·.owner) = event.inputOwners ∧
      scope.selected = boundary.input.ordered.map (·.port) ∧
      mixedAxes scope = RuntimeForestCode.forestAxes scope.interval.before.quantum.frame boundary.input.ordered := by
  have ports := mixed_bound_ports scope boundary
  refine ⟨(RuntimeSelectionPartition.order_values _ _ _ boundary.input.orderRead).2,ports,?_⟩
  simp only [mixedAxes,ports,RuntimeForestCode.portAxes,RuntimeForestCode.forestAxes,List.flatMap_map]

/-- In the common result itself the original named event, child scope and
boundary determine the same ordered ports and caller-coordinate projection. -/
def StepInputOrder : RuntimePureBody.Step dependencies program block → Prop
  | .named event scope _ _ boundary _ _ =>
    boundary.input.ordered.map (·.owner) = event.inputOwners ∧
      scope.selected = boundary.input.ordered.map (·.port) ∧
      mixedAxes scope = RuntimeForestCode.forestAxes scope.interval.before.quantum.frame boundary.input.ordered
  | _ => True

theorem step_input_order (step : RuntimePureBody.Step dependencies program block) : StepInputOrder step :=
  match step with
  | .named _ scope _ _ boundary _ _ => mixed_bound_axes scope boundary
  | .pure .. | .gap .. | .observation .. | .conditional .. => True.intro

end QleisliKernel.Qirf.RuntimeNamedFrameAxes
