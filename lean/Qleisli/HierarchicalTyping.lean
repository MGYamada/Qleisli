import Qleisli.HierarchicalUnitary

/-! Bind operator laws to the hierarchy's actual structural typing predicates.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
These mathematical lemmas add no executable acceptance rule. -/

namespace Qleisli.HierarchicalTyping
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators HierarchicalUnitary

deriving instance ReflBEq, LawfulBEq for Effect

theorem wire_list (side : Side) :
    (wires side).toList = side.quantum.toList.flatMap (fun p => p.axes.toList) := by
  unfold wires
  rw [← Array.foldl_toList]
  simpa using (Array.foldl_toList_eq_flatMap
    (l := side.quantum.toList) (acc := (#[] : Array Nat))
    (F := fun acc p => acc ++ p.axes) (G := fun p => p.axes.toList)
    (by intros; simp))

theorem width_sum (side : Side) :
    width side = (side.quantum.toList.map (fun p => p.axes.size)).sum := by
  have lengths := congrArg List.length (wire_list side)
  simpa [width,List.length_flatMap,List.map_map] using lengths

theorem width_append (first second : Side) :
    width (NodeTyping.append first second) = width first + width second := by
  simp [width_sum,NodeTyping.append]

theorem coordinates_width (side : Side) :
    (QleisliKernel.Layout.wires (Ports.coordinates side)).length = width side := by
  have fold : ∀ (ports : List QuantumPort) (offset : Nat) (acc : QleisliKernel.Layout.Interface),
      ((ports.foldl Ports.coordinateStep (offset,acc)).2.map (fun p => p.axes.length)).sum =
        (acc.map (fun p => p.axes.length)).sum + (ports.map (fun p => p.axes.size)).sum := by
    intro ports
    induction ports with
    | nil => intros; simp
    | cons port rest ih =>
      intro offset acc
      simp only [List.foldl_cons,Ports.coordinateStep]
      rw [ih]
      simp [Nat.add_assoc,Nat.add_left_comm]
  simp only [Ports.coordinates,Ports.coordinatesFrom,QleisliKernel.Layout.wires,
    List.length_flatMap,List.map_reverse,List.sum_reverse]
  rw [fold]
  simp [width_sum]

theorem ports_width (source destination : Side) (map : PortMap)
    (accepted : Ports.shapeValid source destination map = true) :
    width source = width destination ∧
      QleisliKernel.Layout.Permutation (width source) map.axes.toList
        (Ports.witness source map).inverseAxes := by
  simp only [Ports.shapeValid,Bool.and_eq_true,decide_eq_true_eq] at accepted
  have layoutValid := accepted.1.2
  simp only [QleisliKernel.Layout.structureValid,Bool.and_eq_true,decide_eq_true_eq] at layoutValid
  constructor
  · simpa only [Ports.layout,coordinates_width] using layoutValid.1.1.1.2
  · simpa only [Ports.layout,coordinates_width] using layoutValid.1.2

theorem rewire_unitary (interface : Interface) (map : PortMap)
    (accepted : Ports.shapeValid interface.inputs interface.outputs map = true) :
    UnitaryAt (width interface.inputs) (apply interface (.rewire map.axes.toList) []) := by
  obtain ⟨same,permutation⟩ := ports_width _ _ map accepted
  exact HierarchicalUnitary.rewire_unitary interface _ _ _ rfl same.symm permutation

theorem structural_unitary (interface : Interface) (operation : StructuralOp)
    (accepted : Structural.valid operation interface = true) :
    UnitaryAt (width interface.inputs)
      (apply interface (.rewire (Structural.axisMap interface)) []) := by
  have permutation := Structural.valid_axes operation interface accepted
  have width : width interface.outputs = width interface.inputs := by
    simpa [Structural.axisMap,HierarchicalOperators.width] using permutation.1
  exact HierarchicalUnitary.rewire_unitary interface _ _ _ rfl width permutation

theorem phase_unitary (definition : Definition) (owner j k : Nat)
    (accepted : NodeTyping.phase definition owner = true) :
    UnitaryAt (width definition.interface.inputs)
      (apply definition.interface (.phase owner j k) []) := by
  simp only [NodeTyping.phase,Bool.and_eq_true,beq_iff_eq] at accepted
  exact HierarchicalUnitary.phase_unitary definition.interface _ owner j k rfl
    (congrArg width accepted.1.2).symm

/-- The operator's actual dimensions are bound to both declared endpoints.
Equal wire counts alone do not replace the typing predicate. -/
def UnitaryInterface (interface : Interface) (operator : Operator) : Prop :=
  UnitaryAt (width interface.inputs) operator ∧ operator.outputWidth = width interface.outputs

theorem UnitaryInterface.widths {interface : Interface} {operator : Operator}
    (h : UnitaryInterface interface operator) : width interface.outputs = width interface.inputs :=
  h.2.symm.trans h.1.2.1

theorem unitaryInterface_apply (interface : Interface) (tag : Tag) (values : List Operator)
    (h : UnitaryAt (width interface.inputs) (apply interface tag values)) :
    UnitaryInterface interface (apply interface tag values) := ⟨h,rfl⟩

theorem typed_inverse (artifact : Artifact) (parent child : Definition) (index : Nat)
    (body : parent.body = .inverse index) (found : artifact.definitions[index]? = some child)
    (typed : NodeTyping.conditions artifact parent = true) (operator : Operator)
    (ready : UnitaryInterface child.interface operator) :
    UnitaryInterface parent.interface (apply parent.interface .inverse [operator]) := by
  have endpoints : parent.interface = ⟨child.interface.outputs,child.interface.inputs⟩ := by
    simp [NodeTyping.conditions,body,found] at typed
    exact typed.2.2
  apply unitaryInterface_apply
  have h := HierarchicalUnitary.inverse_unitary parent.interface
    (n := width child.interface.inputs) (by simp [endpoints,ready.widths])
    (by simp [endpoints]) ready.1
  simpa [endpoints,ready.widths] using h

theorem typed_power (artifact : Artifact) (parent child : Definition) (index count : Nat)
    (body : parent.body = .repeatOp count index) (found : artifact.definitions[index]? = some child)
    (typed : NodeTyping.conditions artifact parent = true) (operator : Operator)
    (ready : UnitaryInterface child.interface operator) :
    UnitaryInterface parent.interface (apply parent.interface (.power count) [operator]) := by
  have endpoints : parent.interface = child.interface := by
    simp [NodeTyping.conditions,body,found] at typed
    exact typed.2.2
  apply unitaryInterface_apply
  apply HierarchicalUnitary.apply_power_unitary
  · rfl
  · simp [endpoints,ready.widths]
  · simpa [endpoints] using ready.1

theorem typed_tensor (artifact : Artifact) (parent left right : Definition) (li ri : Nat)
    (body : parent.body = .tensor li ri)
    (hl : artifact.definitions[li]? = some left) (hr : artifact.definitions[ri]? = some right)
    (typed : NodeTyping.conditions artifact parent = true) (first second : Operator)
    (hf : UnitaryInterface left.interface first) (hs : UnitaryInterface right.interface second) :
    UnitaryInterface parent.interface (apply parent.interface .tensor [first,second]) := by
  have endpoints : parent.interface =
      ⟨NodeTyping.append left.interface.inputs right.interface.inputs,
        NodeTyping.append left.interface.outputs right.interface.outputs⟩ := by
    simp [NodeTyping.conditions,body,hl,hr] at typed
    exact typed.2.2
  apply unitaryInterface_apply
  have h := HierarchicalUnitary.tensor_unitary parent.interface
    (width left.interface.inputs) (width right.interface.inputs) first second
    (by simp [endpoints,width_append]) (by simp [endpoints,width_append,hf.widths,hs.widths]) hf.1 hs.1
  simpa [endpoints,width_append] using h

theorem controlled_widths (parent child : Interface)
    (typed : NodeTyping.controlledInterface parent child = true) :
    width parent.inputs = width child.inputs + 1 ∧
      width parent.outputs = width child.outputs + 1 := by
  cases hc : parent.inputs.quantum[0]? with
  | none => simp [NodeTyping.controlledInterface,hc] at typed
  | some control =>
    simp [NodeTyping.controlledInterface,hc] at typed
    have single := typed.1.1.1.1.2
    have inputs := typed.1.1.1.2
    have outputs := typed.1.1.2
    constructor
    · rw [inputs,width_append]
      simp [width_sum,single,Nat.add_comm]
    · rw [outputs,width_append]
      simp [width_sum,single,Nat.add_comm]

theorem typed_control (artifact : Artifact) (parent child : Definition) (index : Nat) (polarity : Bool)
    (body : parent.body = .control index polarity) (found : artifact.definitions[index]? = some child)
    (typed : NodeTyping.conditions artifact parent = true) (operator : Operator)
    (ready : UnitaryInterface child.interface operator) :
    UnitaryInterface parent.interface (apply parent.interface (.control polarity) [operator]) := by
  have controlled : NodeTyping.controlledInterface parent.interface child.interface = true := by
    simp [NodeTyping.conditions,body,found,NodeTyping.controlled] at typed
    exact typed.2.2
  obtain ⟨hi,ho⟩ := controlled_widths _ _ controlled
  apply unitaryInterface_apply
  rw [ready.widths] at ho
  have h := HierarchicalUnitary.control_unitary parent.interface
    (width child.interface.inputs) polarity operator hi ho ready.1
  simpa [hi] using h

/-- The actual sequence header fold preserves width when each child does.
Effects are carried unchanged by this proof; their checks remain in the fold. -/
theorem sequence_fold_width (artifact : Artifact) (children : List Nat)
    (before after : Side × Effect)
    (accepted : children.foldlM (fun state index => do
      let child ← artifact.definitions[index]?
      if state.1 != child.interface.inputs then none else
        some (child.interface.outputs,NodeTyping.join state.2 child.effect)) before = some after)
    (ready : ∀ index ∈ children, ∀ child, artifact.definitions[index]? = some child →
      width child.interface.outputs = width child.interface.inputs) :
    width after.1 = width before.1 ∧ ∀ index ∈ children, ∀ child,
      artifact.definitions[index]? = some child → width child.interface.inputs = width before.1 := by
  induction children generalizing before with
  | nil =>
    have same : before = after := by simpa using accepted
    simp [same]
  | cons index rest ih =>
    cases hd : artifact.definitions[index]? with
    | none => simp [hd] at accepted
    | some child =>
      simp only [List.foldlM_cons,hd] at accepted
      by_cases same : before.1 = child.interface.inputs
      · simp [same] at accepted
        have childWidth := ready index (by simp) child hd
        have tail := ih (child.interface.outputs,NodeTyping.join before.2 child.effect) (by simpa using accepted)
          (fun i member d found => ready i (by simp [member]) d found)
        refine ⟨by simpa [childWidth,same] using tail.1,?_⟩
        intro i member d found
        rcases List.mem_cons.mp member with equal | inside
        · subst i
          have equal := Option.some.inj (found.symm.trans hd)
          subst d
          exact congrArg width same.symm
        · simpa [childWidth,same] using tail.2 i inside d found
      · simp [same] at accepted

theorem sequence_widths (artifact : Artifact) (children : Array Nat) (interface : Interface) (effect : Effect)
    (accepted : NodeTyping.sequence artifact children = some (interface,effect))
    (ready : ∀ index ∈ children.toList, ∀ child, artifact.definitions[index]? = some child →
      width child.interface.outputs = width child.interface.inputs) :
    width interface.outputs = width interface.inputs ∧ ∀ index ∈ children.toList, ∀ child,
      artifact.definitions[index]? = some child → width child.interface.inputs = width interface.inputs := by
  cases hc : children.toList with
  | nil =>
    have empty : children = #[] := Array.toList_inj.mp hc
    simp [NodeTyping.sequence,empty] at accepted
  | cons index rest =>
    have first : children[0]? = some index := by
      rw [← Array.getElem?_toList,hc]
      rfl
    cases hd : artifact.definitions[index]? with
    | none => simp [NodeTyping.sequence,first,hd] at accepted
    | some child =>
      simp [NodeTyping.sequence,first,hd,hc] at accepted
      let step := fun (state : Side × Effect) (index : Nat) => (do
        let child : Definition ← artifact.definitions[index]?
        if state.1 != child.interface.inputs then none else
          some (child.interface.outputs,NodeTyping.join state.2 child.effect) : Option (Side × Effect))
      cases hr : rest.foldlM step (child.interface.outputs,child.effect) with
      | none =>
        simp [step] at hr
        simp [hr] at accepted
      | some result =>
        have normalized := hr
        simp [step] at normalized
        rw [normalized] at accepted
        have endpoints : interface = ⟨child.interface.inputs,result.1⟩ := by
          simp at accepted
          exact accepted.1.symm
        have tail := sequence_fold_width artifact rest _ result hr
          (fun i member d found => ready i (by simp [hc,member]) d found)
        have childWidth := ready index (by simp [hc]) child hd
        refine ⟨by simpa [endpoints,childWidth] using tail.1,?_⟩
        intro i member d found
        rcases List.mem_cons.mp member with equal | inside
        · subst i
          have equal := Option.some.inj (found.symm.trans hd)
          subst d
          simp [endpoints]
        · simpa [endpoints,childWidth] using tail.2 i inside d found

theorem typed_sequence (artifact : Artifact) (parent : Definition) (children : Array Nat)
    (body : parent.body = .sequence children) (typed : NodeTyping.conditions artifact parent = true)
    (values : Nat → Operator)
    (ready : ∀ index ∈ children.toList, ∃ child, artifact.definitions[index]? = some child ∧
      UnitaryInterface child.interface (values index)) :
    UnitaryInterface parent.interface (apply parent.interface .sequence (children.toList.map values)) := by
  have chain : NodeTyping.sequence artifact children = some (parent.interface,parent.effect) := by
    simp [NodeTyping.conditions,body] at typed
    exact typed.2
  have widths := sequence_widths artifact children parent.interface parent.effect chain (by
    intro index member child found
    obtain ⟨actual,ha,h⟩ := ready index member
    have equal := Option.some.inj (found.symm.trans ha)
    subst actual
    exact h.widths)
  apply unitaryInterface_apply
  apply HierarchicalUnitary.apply_sequence_unitary _ _ _ rfl widths.1
  intro operator member
  obtain ⟨index,inside,equal⟩ := List.mem_map.mp member
  subst operator
  obtain ⟨child,found,h⟩ := ready index inside
  simpa only [widths.2 index inside child found] using h.1

end Qleisli.HierarchicalTyping
