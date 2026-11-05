import QleisliKernel.Qirf.RuntimeLocalEvents
import QleisliKernel.Raw.Ownership

/-! Coordinate bounds of the actual circuit emitted by an original Raw step.
The original operand membership, one-wire shapes and written tape bounds come
from successful native step/dispatch checks. These proof lemmas add no checker,
runtime restriction or producer-supplied coordinate premise. Empty circuit tapes
remain single circuit chunks.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeTraceBounds
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.Finite

private def StepBound (bits : Nat) (step : Step) : Prop :=
  (∀ control ∈ step.controls, control.index < bits) ∧
    (∀ axis ∈ Finite.targets step.action, axis < bits)

private theorem chunks_bound (bits : Nat) (steps : List Step)
    (bounded : ∀ step ∈ steps, StepBound bits step) :
    Qirf.RuntimeLocalEvents.bounds bits [steps] = true := by
  apply List.all_eq_true.mpr
  intro chunk present
  have same : chunk = steps := by simpa only [List.mem_singleton] using present
  subst chunk
  apply List.all_eq_true.mpr
  intro step member
  exact Bool.and_eq_true_iff.mpr
    ⟨List.all_eq_true.mpr (fun control held => decide_eq_true ((bounded step member).1 control held)),
      List.all_eq_true.mpr (fun axis held => decide_eq_true ((bounded step member).2 axis held))⟩

private theorem gate_bound (bits axis : Nat) (value : Semantics.Raw.Gate) (inside : axis < bits) :
    StepBound bits (Semantics.RawTrace.gate value axis) := by
  cases value <;> simp [StepBound,Semantics.RawTrace.gate,Finite.targets,inside]

private theorem control_bound (bits : Nat) (step : Step) (axis : Nat) (polarity : Bool)
    (bounded : StepBound bits step) (inside : axis < bits) :
    StepBound bits {step with controls := step.controls ++ [⟨axis,polarity⟩]} := by
  refine ⟨?_,bounded.2⟩
  intro control member
  rcases List.mem_append.mp member with old | added
  · exact bounded.1 control old
  · have same : control = ⟨axis,polarity⟩ := by simpa only [List.mem_singleton] using added
    subst control
    exact inside

private theorem lookup_bound (bits : Nat) (axes : List Nat) (index : Nat)
    (bounded : ∀ axis ∈ axes, axis < bits) (inside : index < axes.length) :
    axes[index]?.getD 0 < bits := by
  rw [List.getElem?_eq_getElem inside,Option.getD_some]
  exact bounded _ (List.getElem_mem inside)

private theorem localized_bound (bits : Nat) (axes : List Nat) (step : Step)
    (bounded : ∀ axis ∈ axes, axis < bits) (original : StepBound axes.length step) :
    StepBound bits (Semantics.RawTrace.localize axes step) := by
  constructor
  · intro control present
    obtain ⟨written,member,same⟩ := List.mem_map.mp present
    subst control
    exact lookup_bound bits axes written.index bounded (original.1 written member)
  · intro axis present
    have targets : Finite.targets (Semantics.RawTrace.localize axes step).action =
        (Finite.targets step.action).map (fun index => axes[index]?.getD 0) := by
      rcases step with ⟨controls,action⟩
      cases action <;> rfl
    rw [targets] at present
    obtain ⟨written,member,same⟩ := List.mem_map.mp present
    subst axis
    exact lookup_bound bits axes written bounded (original.2 written member)

private theorem tape_bound (dependencies : List Basis) (bits : Nat) (steps : List Step)
    (valid : Raw.circuitStepsValid dependencies bits steps = true) :
    ∀ step ∈ steps, StepBound bits step := by
  intro step member
  have checked := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp valid) step member)).1
  simp only [Finite.axesValid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at checked
  have inside := checked.1.2
  exact ⟨fun control present => inside control.index
      (List.mem_append.mpr (Or.inl (List.mem_map_of_mem present))),
    fun axis present => inside axis (List.mem_append.mpr (Or.inr present))⟩

private theorem take_fields (before after : Raw.State) (token : Nat) (port : Semantics.Raw.Port)
    (read : Raw.take before token = .ok (port,after)) :
    port ∈ before.live ∧ after.live ⊆ before.live := by
  have fields := Raw.Ownership.take_state _ _ _ _ read
  refine ⟨List.mem_of_find?_eq_some fields.1,?_⟩
  rw [fields.2]
  exact fun _ member => (List.mem_filter.mp member).1

private theorem port_axes (before : Raw.State) (port : Semantics.Raw.Port)
    (valid : Semantics.Ownership.Valid (Raw.Ownership.view before)) (present : port ∈ before.live) :
    (Raw.axes before port.wires).length = port.bits ∧
      (∀ axis ∈ Raw.axes before port.wires, axis < before.frame.length) := by
  refine ⟨?_,?_⟩
  · simpa only [Raw.axes,List.length_map] using (valid.ports port present).1.symm
  · intro axis member
    obtain ⟨wire,held,same⟩ := List.mem_map.mp member
    subst axis
    exact List.idxOf_lt_length_of_mem
      (valid.covered wire (List.mem_flatMap.mpr ⟨port,present,held⟩))

private theorem port_axis (before : Raw.State) (port : Semantics.Raw.Port)
    (valid : Semantics.Ownership.Valid (Raw.Ownership.view before)) (present : port ∈ before.live)
    (one : port.bits = 1) : before.frame.idxOf (port.wires[0]?.getD 0) < before.frame.length := by
  obtain ⟨wire,wires⟩ := List.length_eq_one_iff.mp ((valid.ports port present).1.symm.trans one)
  have covered := valid.covered wire
    (List.mem_flatMap.mpr ⟨port,present,by simp only [wires,List.mem_singleton]⟩)
  simpa only [wires,List.getElem?_cons_zero,Option.getD_some] using List.idxOf_lt_length_of_mem covered

/-- A checked original gate's actual emitted circuit is inside its own frame. -/
theorem gate_bounds (dependencies : List Basis) (before : Raw.State) (value : Semantics.Raw.Gate)
    (input output : Nat) (result : Raw.Transition) (steps : List Step)
    (read : Raw.step dependencies before (.gate value input output) = .ok result)
    (events : result.events = [.circuit before.frame.length steps]) :
    Qirf.RuntimeLocalEvents.bounds before.frame.length [steps] = true := by
  have conditions := Raw.step_conditions _ _ _ _ read
  have valid := Raw.Ownership.valid _ conditions.1
  have dispatch := conditions.2.1
  simp only [Raw.dispatch] at dispatch
  obtain ⟨⟨port,rest⟩,taken,h⟩ := except_bind_success _ _ _ dispatch
  obtain ⟨_,one,h⟩ := except_bind_success _ _ _ h
  obtain ⟨next,_,h⟩ := except_bind_success _ _ _ h
  have same := Except.ok.inj h
  subst result
  have written : [Raw.gateStep value (before.frame.idxOf (port.wires[0]?.getD 0))] = steps := by
    simpa only [List.cons.injEq,Semantics.Raw.Event.circuit.injEq,true_and,and_true] using events
  rw [← written]
  apply chunks_bound
  intro step member
  have same : step = Raw.gateStep value (before.frame.idxOf (port.wires[0]?.getD 0)) := by
    simpa only [List.mem_singleton] using member
  subst step
  exact gate_bound _ _ value (port_axis before port valid (take_fields _ _ _ _ taken).1
    (beq_iff_eq.mp (Raw.require_success _ one)))

/-- Both checked one-wire operands bound the original cnot's emitted axes. -/
theorem cnot_bounds (dependencies : List Basis) (before : Raw.State) (control target controlOut targetOut : Nat)
    (result : Raw.Transition) (steps : List Step)
    (read : Raw.step dependencies before (.cnot control target controlOut targetOut) = .ok result)
    (events : result.events = [.circuit before.frame.length steps]) :
    Qirf.RuntimeLocalEvents.bounds before.frame.length [steps] = true := by
  have conditions := Raw.step_conditions _ _ _ _ read
  have valid := Raw.Ownership.valid _ conditions.1
  have dispatch := conditions.2.1
  simp only [Raw.dispatch] at dispatch
  obtain ⟨⟨c,afterControl⟩,takeControl,h⟩ := except_bind_success _ _ _ dispatch
  obtain ⟨⟨t,rest⟩,takeTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneControl,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨next,_,h⟩ := except_bind_success _ _ _ h
  obtain ⟨last,_,h⟩ := except_bind_success _ _ _ h
  have controlFields := take_fields _ _ _ _ takeControl
  have targetFields := take_fields _ _ _ _ takeTarget
  have controlBound := port_axis before c valid controlFields.1
    (beq_iff_eq.mp (Raw.require_success _ oneControl))
  have targetBound := port_axis before t valid (controlFields.2 targetFields.1)
    (beq_iff_eq.mp (Raw.require_success _ oneTarget))
  have bounded := control_bound before.frame.length
    (Semantics.RawTrace.gate .x (before.frame.idxOf (t.wires[0]?.getD 0)))
    (before.frame.idxOf (c.wires[0]?.getD 0)) true (gate_bound _ _ .x targetBound) controlBound
  have same := Except.ok.inj h
  subst result
  have written : [{Raw.gateStep .x (before.frame.idxOf (t.wires[0]?.getD 0)) with
      controls := [⟨before.frame.idxOf (c.wires[0]?.getD 0),true⟩]}] = steps := by
    simpa only [List.cons.injEq,Semantics.Raw.Event.circuit.injEq,true_and,and_true] using events
  rw [← written]
  apply chunks_bound
  intro step member
  have same := List.mem_singleton.mp member
  subst step
  exact bounded

/-- All three actual one-wire operands bound the original toffoli's axes. -/
theorem toffoli_bounds (dependencies : List Basis) (before : Raw.State) (a b target aOut bOut targetOut : Nat)
    (result : Raw.Transition) (steps : List Step)
    (read : Raw.step dependencies before (.toffoli a b target aOut bOut targetOut) = .ok result)
    (events : result.events = [.circuit before.frame.length steps]) :
    Qirf.RuntimeLocalEvents.bounds before.frame.length [steps] = true := by
  have conditions := Raw.step_conditions _ _ _ _ read
  have valid := Raw.Ownership.valid _ conditions.1
  have dispatch := conditions.2.1
  simp only [Raw.dispatch] at dispatch
  obtain ⟨⟨pa,afterA⟩,takeA,h⟩ := except_bind_success _ _ _ dispatch
  obtain ⟨⟨pb,afterB⟩,takeB,h⟩ := except_bind_success _ _ _ h
  obtain ⟨⟨t,rest⟩,takeTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneA,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneB,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨next,_,h⟩ := except_bind_success _ _ _ h
  obtain ⟨last,_,h⟩ := except_bind_success _ _ _ h
  obtain ⟨final,_,h⟩ := except_bind_success _ _ _ h
  have aFields := take_fields _ _ _ _ takeA
  have bFields := take_fields _ _ _ _ takeB
  have targetFields := take_fields _ _ _ _ takeTarget
  have aBound := port_axis before pa valid aFields.1 (beq_iff_eq.mp (Raw.require_success _ oneA))
  have bBound := port_axis before pb valid (aFields.2 bFields.1) (beq_iff_eq.mp (Raw.require_success _ oneB))
  have targetBound := port_axis before t valid (aFields.2 (bFields.2 targetFields.1))
    (beq_iff_eq.mp (Raw.require_success _ oneTarget))
  have first := control_bound before.frame.length
    (Semantics.RawTrace.gate .x (before.frame.idxOf (t.wires[0]?.getD 0)))
    (before.frame.idxOf (pa.wires[0]?.getD 0)) true (gate_bound _ _ .x targetBound) aBound
  have bounded := control_bound before.frame.length _ (before.frame.idxOf (pb.wires[0]?.getD 0)) true first bBound
  have same := Except.ok.inj h
  subst result
  have written : [{Raw.gateStep .x (before.frame.idxOf (t.wires[0]?.getD 0)) with
      controls := [⟨before.frame.idxOf (pa.wires[0]?.getD 0),true⟩,
        ⟨before.frame.idxOf (pb.wires[0]?.getD 0),true⟩]}] = steps := by
    simpa only [List.cons.injEq,Semantics.Raw.Event.circuit.injEq,true_and,and_true] using events
  rw [← written]
  apply chunks_bound
  intro step member
  have same := List.mem_singleton.mp member
  subst step
  exact bounded

/-- The original applyUnitary validation and actual operand wires bound every
original tape step after localization, including all contract targets. -/
theorem apply_bounds (dependencies : List Basis) (before : Raw.State) (input output : Nat)
    (written : List Step) (result : Raw.Transition) (steps : List Step)
    (read : Raw.step dependencies before (.applyUnitary input output written) = .ok result)
    (events : result.events = [.circuit before.frame.length steps]) :
    Qirf.RuntimeLocalEvents.bounds before.frame.length [steps] = true := by
  have conditions := Raw.step_conditions _ _ _ _ read
  have valid := Raw.Ownership.valid _ conditions.1
  have dispatch := conditions.2.1
  simp only [Raw.dispatch] at dispatch
  obtain ⟨⟨port,rest⟩,taken,h⟩ := except_bind_success _ _ _ dispatch
  obtain ⟨_,checked,h⟩ := except_bind_success _ _ _ h
  obtain ⟨next,_,h⟩ := except_bind_success _ _ _ h
  have axes := port_axes before port valid (take_fields _ _ _ _ taken).1
  have original := tape_bound dependencies port.bits written (Raw.require_success _ checked)
  have same := Except.ok.inj h
  subst result
  have tape : written.map (Raw.remap (Raw.axes before port.wires)) = steps := by
    simpa only [List.cons.injEq,Semantics.Raw.Event.circuit.injEq,true_and,and_true] using events
  rw [← tape]
  apply chunks_bound
  intro step member
  obtain ⟨originalStep,held,same⟩ := List.mem_map.mp member
  subst step
  apply localized_bound before.frame.length _ originalStep axes.2
  simpa only [axes.1] using original originalStep held

/-- Both complete quantumIf tapes, including their appended false/true
controls, are bounded by actual original step checks and owner coverage. -/
theorem quantumIf_bounds (dependencies : List Basis) (before : Raw.State) (control target controlOut targetOut : Nat)
    (zero one : List Semantics.Raw.UnitaryStep) (result : Raw.Transition) (steps : List Step)
    (read : Raw.step dependencies before (.quantumIf control target controlOut targetOut zero one) = .ok result)
    (events : result.events = [.circuit before.frame.length steps]) :
    Qirf.RuntimeLocalEvents.bounds before.frame.length [steps] = true := by
  have conditions := Raw.step_conditions _ _ _ _ read
  have valid := Raw.Ownership.valid _ conditions.1
  have dispatch := conditions.2.1
  simp only [Raw.dispatch] at dispatch
  obtain ⟨⟨c,afterControl⟩,takeControl,h⟩ := except_bind_success _ _ _ dispatch
  obtain ⟨⟨t,rest⟩,takeTarget,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,oneControl,h⟩ := except_bind_success _ _ _ h
  obtain ⟨_,checked,h⟩ := except_bind_success _ _ _ h
  obtain ⟨next,_,h⟩ := except_bind_success _ _ _ h
  obtain ⟨last,_,h⟩ := except_bind_success _ _ _ h
  have controlFields := take_fields _ _ _ _ takeControl
  have targetFields := take_fields _ _ _ _ takeTarget
  have controlBound := port_axis before c valid controlFields.1
    (beq_iff_eq.mp (Raw.require_success _ oneControl))
  have axes := port_axes before t valid (controlFields.2 targetFields.1)
  have tapes := Bool.and_eq_true_iff.mp (Raw.require_success _ checked)
  let arm (polarity : Bool) (written : List Semantics.Raw.UnitaryStep) : List Step := written.map fun step =>
    let action := Raw.remap (Raw.axes before t.wires) (Raw.unitaryStep step)
    {action with controls := action.controls ++ [(⟨before.frame.idxOf (c.wires[0]?.getD 0),polarity⟩ : Control)]}
  have armBound (polarity : Bool) (written : List Semantics.Raw.UnitaryStep)
      (checked : Raw.circuitStepsValid [] t.bits (written.map Raw.unitaryStep) = true) :
      ∀ step ∈ arm polarity written, StepBound before.frame.length step := by
    intro step member
    obtain ⟨original,held,same⟩ := List.mem_map.mp member
    subst step
    have originalBound := tape_bound [] t.bits (written.map Raw.unitaryStep) checked
      (Raw.unitaryStep original) (List.mem_map_of_mem held)
    have localized := localized_bound before.frame.length (Raw.axes before t.wires)
      (Raw.unitaryStep original) axes.2 (by simpa only [axes.1] using originalBound)
    exact control_bound _ _ _ polarity localized controlBound
  have same := Except.ok.inj h
  subst result
  have tape : arm false zero ++ arm true one = steps := by
    simpa only [arm,List.cons.injEq,Semantics.Raw.Event.circuit.injEq,true_and,and_true] using events
  rw [← tape]
  apply chunks_bound
  intro step member
  rcases List.mem_append.mp member with fromZero | fromOne
  · exact armBound false zero tapes.1 step fromZero
  · exact armBound true one tapes.2 step fromOne

#print axioms gate_bounds
#print axioms cnot_bounds
#print axioms toffoli_bounds
#print axioms apply_bounds
#print axioms quantumIf_bounds

end Qleisli.RuntimeTraceBounds
