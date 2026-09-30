import Qleisli.HierarchicalInstrumentCoordinates
import Qleisli.Semantics.InstrumentComplete
import Qleisli.Semantics.InstrumentPartitions
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Flatten

/-! Complete output geometry and Kraus completeness of accepted instruments.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
All geometry is derived from the actual readout checks, including arbitrary
measurement order, retained registers and zero-width quantum owners. -/

namespace Qleisli.HierarchicalInstrument
open QleisliKernel.Hierarchical
open Artifact HierarchicalFiniteEvaluation HierarchicalOperators
open HierarchicalRoot (FiniteEquation)
open scoped BigOperators Matrix

theorem wires_flatMap (side : Side) :
    (wires side).toList = side.quantum.toList.flatMap (fun p => p.axes.toList) := by
  simp only [wires,← Array.flatMap_eq_foldl,Array.toList_flatMap]

private def AxisOf (ports : List QuantumPort) (owner axis : Nat) : Prop :=
  ∃ port ∈ ports, port.owner = owner ∧ port.axes.toList = [axis]

private theorem option_mapM_forall₂ {A B : Type} (f : A → Option B) (xs : List A) (ys : List B)
    (mapped : xs.mapM f = some ys) : List.Forall₂ (fun a b => f a = some b) xs ys := by
  induction xs generalizing ys with
  | nil => simp at mapped; subst ys; exact .nil
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at mapped
    | some y =>
      cases hr : xs.mapM f with
      | none => simp [List.mapM_cons,hx,hr] at mapped
      | some rest =>
        have same : y::rest = ys := by simpa [List.mapM_cons,hx,hr] using mapped
        subst ys
        exact .cons hx (ih rest hr)

private theorem requested_relation (request : Readout.Request) (axes : Array Nat)
    (found : Readout.requestedAxes request = some axes) :
    List.Forall₂ (AxisOf request.inputs.quantum.toList) request.owners.toList axes.toList := by
  have converted := congrArg (fun (value : Option (Array Nat)) => Array.toList <$> value) found
  dsimp only at converted
  rw [Readout.requestedAxes,Array.toList_mapM] at converted
  have related := option_mapM_forall₂ _ _ _ converted
  apply related.imp
  intro owner axis read
  try dsimp only at read
  simp only [bind,Option.bind] at read
  repeat (split at read <;> (try dsimp only at read) <;> (try contradiction))
  all_goals
    rename_i port lookup valid
    have member := Array.mem_of_find?_eq_some lookup
    have selected := Array.find?_some lookup
    have size : port.axes.size = 1 := by
      simp only [Bool.or_eq_true,bne_iff_ne,not_or,Classical.not_not] at valid
      exact valid.2
    refine ⟨port,by simpa using member,by simpa using selected,?_⟩
    have entry := (Array.getElem?_eq_some_iff.mp read).2
    apply List.ext_getElem
    · simpa using size
    · intro i hi hj
      have zero : i = 0 := by simpa using hj
      subst i
      simpa using entry

private theorem relation_left {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) (a : A) (member : a ∈ xs) : ∃ b ∈ ys, R a b := by
  induction related with
  | nil => simp at member
  | @cons x y xs ys head tail ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨y,by simp,head⟩
    · obtain ⟨b,present,relation⟩ := ih inside
      exact ⟨b,by simp [present],relation⟩

private theorem relation_right {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) (b : B) (member : b ∈ ys) : ∃ a ∈ xs, R a b := by
  have flipped : List.Forall₂ (fun b a => R a b) ys xs := related.flip
  exact relation_left flipped b member

/-- Unique physical axes associate an axis with a unique actual port. -/
private theorem axis_port_unique (ports : List QuantumPort)
    (distinct : (ports.flatMap (fun p => p.axes.toList)).Nodup)
    (p q : QuantumPort) (hp : p ∈ ports) (hq : q ∈ ports)
    (axis : Nat) (ha : axis ∈ p.axes.toList) (hb : axis ∈ q.axes.toList) : p = q := by
  let labelled := ports.flatMap (fun p => p.axes.toList.map (fun axis => (p,axis)))
  have mapped : labelled.map Prod.snd = ports.flatMap (fun p => p.axes.toList) := by
    simp [labelled,List.map_flatMap,List.map_map,Function.comp_def]
  have nd : (labelled.map Prod.snd).Nodup := mapped ▸ distinct
  have pa : (p,axis) ∈ labelled := by simp only [labelled,List.mem_flatMap,List.mem_map]; exact ⟨p,hp,axis,ha,rfl⟩
  have qa : (q,axis) ∈ labelled := by simp only [labelled,List.mem_flatMap,List.mem_map]; exact ⟨q,hq,axis,hb,rfl⟩
  exact congrArg Prod.fst (List.inj_on_of_nodup_map nd pa qa rfl)

private theorem relation_nodup {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) (distinct : xs.Nodup)
    (unique : ∀ a b axis, R a axis → R b axis → a = b) : ys.Nodup := by
  induction related with
  | nil => simp
  | @cons x y xs ys head tail ih =>
    have nd := List.nodup_cons.mp distinct
    refine List.nodup_cons.mpr ⟨?_,ih nd.2⟩
    intro member
    obtain ⟨other,inside,relation⟩ := relation_right tail y member
    exact nd.1 ((unique x other y head relation) ▸ inside)

/-- The selected ordered measurement axes and unchanged residual axes partition
the complete input coordinates; no coordinate or zero-width owner is discarded. -/
theorem readout_geometry (request : Readout.Request) (packet : Readout.Packet)
    (remaining : Nat) (checked : Readout.Checked)
    (accepted : Readout.check request packet remaining = .ok checked) :
    ∃ axes, Readout.requestedAxes request = some axes ∧ axes.size = request.owners.size ∧
      axes.toList.Nodup ∧ (wires packet.outputs).toList.Nodup ∧
      List.Disjoint axes.toList (wires packet.outputs).toList ∧
      (wires request.inputs).toList.Perm (axes.toList ++ (wires packet.outputs).toList) := by
  have valid := (Readout.check_conditions request packet remaining checked accepted).2.2
  obtain ⟨output,axes,actual,found,_⟩ := Readout.valid_binding request packet valid
  have inputValid : sideValid request.inputs = true := by
    simp only [Readout.valid,Bool.and_eq_true,decide_eq_true_eq] at valid
    tauto
  have ownerND : request.owners.toList.Nodup := by
    simp only [Readout.valid,Bool.and_eq_true,decide_eq_true_eq] at valid
    tauto
  have portsND : (request.inputs.quantum.toList.map QuantumPort.owner).Nodup := by
    unfold sideValid at inputValid
    split at inputValid
    next invalid => contradiction
    next bounded => simp only [Bool.and_eq_true,decide_eq_true_eq] at inputValid; tauto
  have wireND := sideValid_axes request.inputs inputValid
  have related := requested_relation request axes found
  have unique (a b axis : Nat) (ha : AxisOf request.inputs.quantum.toList a axis)
      (hb : AxisOf request.inputs.quantum.toList b axis) : a = b := by
    obtain ⟨p,hp,op,ap⟩ := ha
    obtain ⟨q,hq,oq,aq⟩ := hb
    have same := axis_port_unique request.inputs.quantum.toList (by simpa [wires_flatMap] using wireND)
      p q hp hq axis (by simp [ap]) (by simp [aq])
    simpa only [same,oq] using op.symm
  have axesND := relation_nodup related ownerND unique
  have residual : (wires packet.outputs).toList =
      (request.inputs.quantum.toList.filter (fun p => !request.owners.contains p.owner)).flatMap
        (fun p => p.axes.toList) := by
    simp only [output,wires_flatMap,Readout.output,Array.toList_filter]
  have residualND : (wires packet.outputs).toList.Nodup := by
    rw [residual]
    exact List.Nodup.sublist (List.Sublist.flatMap List.filter_sublist _)
      (by simpa only [wires_flatMap] using wireND)
  have disjoint : List.Disjoint axes.toList (wires packet.outputs).toList := by
    intro axis measured retained
    obtain ⟨owner,selected,p,hp,op,ap⟩ := relation_right related axis measured
    rw [residual] at retained
    obtain ⟨q,hq,aq⟩ := List.mem_flatMap.mp retained
    have qmem := (List.mem_filter.mp hq).1
    have unselected := (List.mem_filter.mp hq).2
    have same := axis_port_unique request.inputs.quantum.toList (by simpa only [wires_flatMap] using wireND)
      p q hp qmem axis (by simp [ap]) aq
    subst q
    have absent : owner ∉ request.owners.toList := by simpa [op] using unselected
    exact absent selected
  have cover (axis : Nat) : axis ∈ (wires request.inputs).toList ↔
      axis ∈ axes.toList ++ (wires packet.outputs).toList := by
    rw [wires_flatMap,List.mem_append,residual]
    constructor
    · intro member
      obtain ⟨p,hp,ap⟩ := List.mem_flatMap.mp member
      by_cases selected : p.owner ∈ request.owners.toList
      · obtain ⟨a,measured,q,hq,oq,aq⟩ := relation_left related p.owner selected
        have same : q = p := List.inj_on_of_nodup_map portsND hq hp oq
        subst q
        have value : axis = a := by simpa [aq] using ap
        exact Or.inl (value ▸ measured)
      · exact Or.inr (List.mem_flatMap.mpr ⟨p,List.mem_filter.mpr ⟨hp,by simpa using selected⟩,ap⟩)
    · intro member
      rcases member with measured | retained
      · obtain ⟨_,_,p,hp,_,ap⟩ := relation_right related axis measured
        exact List.mem_flatMap.mpr ⟨p,hp,by simp [ap]⟩
      · obtain ⟨p,hp,ap⟩ := List.mem_flatMap.mp retained
        exact List.mem_flatMap.mpr ⟨p,(List.mem_filter.mp hp).1,ap⟩
  exact ⟨axes,found,by simpa using related.length_eq.symm,axesND,residualND,disjoint,
    (List.perm_ext_iff_of_nodup wireND (axesND.append residualND disjoint)).mpr cover⟩

/-- The complete accepted instrument fixes the same output partition used by
its actual complex branch interpretation. Measurement order stays explicit. -/
theorem checkAll_output_axes (request : Instrument.Request) (packet : Instrument.Packet)
    (pending : Instrument.Pending) (accepted : Instrument.checkAll request packet = .ok pending) :
    ∃ axes, Readout.requestedAxes request.readout = some axes ∧ axes.size = request.readout.owners.size ∧
      axes.toList.Nodup ∧ (wires request.outputs).toList.Nodup ∧
      List.Disjoint axes.toList (wires request.outputs).toList ∧
      (wires request.circuit.interface.outputs).toList.Perm
        (axes.toList ++ (wires request.outputs).toList) := by
  have stages := Instrument.checkAll_stages request packet pending accepted
  have conditions := Instrument.assemble_conditions request packet pending.circuit pending stages.2
  have checked := conditions.2.2.2.2.1
  have geometry := readout_geometry request.readout packet.readout _ pending.readout checked
  have boundary := Instrument.checkAll_boundary request packet pending accepted
  simpa only [boundary.2.1,boundary.2.2] using geometry

/-- Summing all actual measurement outcomes preserves the complete input Gram
matrix. Geometry is derived from this accepted packet; only actual finite-leaf
equations/unitarity and independent finite meaning equations remain premises. -/
theorem checkAll_complete (leaves : Leaves Operator)
    (request : Instrument.Request) (packet : Instrument.Packet) (pending : Instrument.Pending)
    (accepted : Instrument.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.circuit.artifact.state.requests.toList,
      HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ pending.circuit.binding.requests, ∀ obligation,
      Root.finitePair packet.artifact request.circuit packet.pairs i = some obligation →
        FiniteEquation leaves obligation) :
    ∃ fuel transform,
      Meaning.actual leaves request.preparation.inputs packet fuel = some transform ∧
      Kraus.Complete (Semantics.Instrument.branchMatrix
        (wires request.preparation.inputs).toList (wires request.outputs).toList
        request.readout.owners.size transform) := by
  obtain ⟨fuel,transform,operator,axes,actual,physical,found,columns⟩ :=
    checkAll_branchColumns leaves request packet pending accepted
      (fun leaf member => HierarchicalFiniteUnitary.Leaf.equation leaves leaf (implementations leaf member))
      meanings
  have stages := Instrument.checkAll_stages request packet pending accepted
  obtain ⟨unitaryFuel,value,evaluated,_,unitary⟩ := HierarchicalRoot.checkAll_unitary leaves
    packet.artifact packet.order request.circuit packet.pairs packet.pairOrder pending.circuit
    stages.1 implementations meanings
  have same := evaluate_unique algebra (definition leaves packet.artifact) unitaryFuel fuel
    packet.artifact.entry.implementation value operator evaluated physical
  subst value
  obtain ⟨inputPartition,_⟩ := checkAll_input_axes request packet pending accepted
  obtain ⟨measured,located,size,measuredND,residualND,disjoint,outputPartition⟩ :=
    checkAll_output_axes request packet pending accepted
  have sameAxes : measured = axes := Option.some.inj (located.symm.trans found)
  subst measured
  let old := (wires request.preparation.inputs).toList
  let fresh := (wires ⟨request.preparation.fresh,#[]⟩).toList
  let outputs := (wires request.circuit.interface.outputs).toList
  let residual := (wires request.outputs).toList
  have inputSize : (old++fresh).length = width request.circuit.interface.inputs := by
    have sized := congrArg List.length inputPartition
    exact sized.symm
  have outputSize : outputs.length = (old++fresh).length := by
    exact unitary.widths.trans inputSize.symm
  have outputND : outputs.Nodup := outputPartition.nodup_iff.mpr
    (measuredND.append residualND disjoint)
  have isometry :
      (matrixAt (old++fresh).length outputs.length operator)ᴴ *
        matrixAt (old++fresh).length outputs.length operator = 1 := by
    rw [outputSize]
    rw [inputSize]
    exact unitary.1.2.2
  refine ⟨fuel,transform,actual,?_⟩
  exact Semantics.Instrument.branchMatrix_complete old fresh outputs axes.toList residual
    outputND measuredND residualND disjoint outputPartition request.readout.owners.size
    (by simpa using size) transform operator.coefficient isometry columns

/-- The entire accepted instrument preserves trace on every joint input and
finite reference, including entangled inputs. The leaf and independent meaning
premises are those of `checkAll_complete`; no axis or branch completeness
assumption is delegated to callers. -/
theorem checkAll_trace {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (leaves : Leaves Operator)
    (request : Instrument.Request) (packet : Instrument.Packet) (pending : Instrument.Pending)
    (accepted : Instrument.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.circuit.artifact.state.requests.toList,
      HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ pending.circuit.binding.requests, ∀ obligation,
      Root.finitePair packet.artifact request.circuit packet.pairs i = some obligation →
        FiniteEquation leaves obligation)
    (rho : Matrix ((Fin (wires request.preparation.inputs).toList.length → Bool) × Reference)
      ((Fin (wires request.preparation.inputs).toList.length → Bool) × Reference) ℂ) :
    ∃ fuel transform,
      Meaning.actual leaves request.preparation.inputs packet fuel = some transform ∧
      ∑ outcome, Matrix.trace (Semantics.Instrument.density
        (Semantics.Instrument.branchMatrix (wires request.preparation.inputs).toList
          (wires request.outputs).toList request.readout.owners.size transform outcome) rho) =
        Matrix.trace rho := by
  obtain ⟨fuel,transform,actual,complete⟩ :=
    checkAll_complete leaves request packet pending accepted implementations meanings
  exact ⟨fuel,transform,actual,Semantics.Instrument.complete_trace _ complete rho⟩

end Qleisli.HierarchicalInstrument
