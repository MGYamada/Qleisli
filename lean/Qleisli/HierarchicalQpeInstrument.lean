import Qleisli.HierarchicalQpeSchedule
import Qleisli.HierarchicalQpeRoot
import Qleisli.QpeComplete
import Qleisli.HierarchicalInstrumentComplete
import Qleisli.Semantics.QpeFrames
import QleisliKernel.Hierarchical.QpeInstrument

/-! Actual initialize/QPE/readout binding to the independently named full-target
QPE instrument. Coordinate frames, provider phase and classical measurement
order are retained explicitly. Source preservation and executable finite-reader
correspondence remain separate obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.HierarchicalQpeInstrument
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalFiniteEvaluation
open CoordinateOperators
open scoped BigOperators Matrix

/-- Reuse the existing actual instrument reader. This changes no body, entry,
initialization or measurement; proof-pair fields are not read by `Meaning.actual`. -/
def packetView (packet : QpeInstrument.Packet) : Instrument.Packet :=
  ⟨packet.preparation,packet.circuit.artifact,packet.circuit.order,
    packet.circuit.pairs,packet.circuit.pairOrder,packet.readout⟩

/-- The actual accepted preparation supplies a distinct old/fresh axis frame. -/
theorem checkAll_input_axes (request : QpeInstrument.Request) (packet : QpeInstrument.Packet)
    (pending : QpeInstrument.Pending) (accepted : QpeInstrument.checkAll request packet = .ok pending) :
    (wires request.circuit.circuit.interface.inputs).toList =
      (wires request.preparation.inputs).toList ++ (wires ⟨request.preparation.fresh,#[]⟩).toList ∧
    ((wires request.preparation.inputs).toList ++ (wires ⟨request.preparation.fresh,#[]⟩).toList).Nodup := by
  have stages := QpeInstrument.checkAll_conditions request packet pending accepted
  have facts := QpeInstrument.assemble_conditions request packet pending.circuit pending stages.2
  have bound := (Preparation.check_binding _ _ _ _ facts.2.1).1
  have valid := (Preparation.check_conditions _ _ _ _ facts.2.1).2.2
  have outputValid : sideValid packet.preparation.outputs = true := by
    simp only [Preparation.valid,Bool.and_eq_true] at valid
    exact valid.1.1.1.1.2
  have distinct := HierarchicalInstrument.sideValid_axes packet.preparation.outputs outputValid
  rw [bound,HierarchicalInstrument.preparation_axes] at distinct
  have boundary := facts.2.2.2.1
  simp only [QpeInstrument.boundary,Bool.and_eq_true,beq_iff_eq,and_assoc] at boundary
  refine ⟨?_,distinct⟩
  rw [← boundary.1,bound,HierarchicalInstrument.preparation_axes]

/-- Actual finite-basis columns, with zero preparation and ordered readout
obtained from the very same packet. The middle operator is an actual evaluation. -/
theorem checkAll_columns (leaves : Leaves Operator)
    (request : QpeInstrument.Request) (packet : QpeInstrument.Packet) (pending : QpeInstrument.Pending)
    (accepted : QpeInstrument.checkAll request packet = .ok pending)
    (fuel : Nat) (operator : Operator)
    (evaluated : physical algebra leaves packet.circuit.artifact fuel
      packet.circuit.artifact.entry.implementation = some operator) :
    ∃ transform axes,
      HierarchicalInstrument.Meaning.actual leaves request.preparation.inputs (packetView packet) fuel = some transform ∧
      Readout.requestedAxes request.readout = some axes ∧
      ∀ outcome output input,
        Semantics.Instrument.branchMatrix (wires request.preparation.inputs).toList
          (wires request.outputs).toList request.readout.owners.size transform outcome output input =
          operator.coefficient
            ((wires request.circuit.circuit.interface.outputs).toList.map
              (QleisliKernel.Semantics.Readout.select axes.toList
                (fun position => (List.ofFn outcome)[position]?.getD false)
                (Semantics.Instrument.assignment (wires request.outputs).toList output)))
            (List.ofFn input ++ List.replicate (wires ⟨request.preparation.fresh,#[]⟩).toList.length false) := by
  have stages := QpeInstrument.checkAll_conditions request packet pending accepted
  have facts := QpeInstrument.assemble_conditions request packet pending.circuit pending stages.2
  have prepare := Preparation.check_binding _ _ _ _ facts.2.1
  obtain ⟨_,axes,measured,axisFound,measureFound,_,_,axisMatch⟩ :=
    Readout.valid_binding request.readout packet.readout (Readout.check_conditions _ _ _ _ facts.2.2.1).2.2
  have rootStages := QpeRoot.checkAll_conditions request.circuit packet.circuit pending.circuit stages.1
  have rootFacts := QpeRoot.assemble_conditions request.circuit packet.circuit pending.circuit.artifact
    pending.circuit rootStages.2
  have schedule := QpeSchedule.inspect_conditions _ _ _ _ _ rootFacts.2.2.2.2.1
  obtain ⟨definition,found,header,_⟩ := schedule.2.2.2.2.1
  refine ⟨Semantics.Instrument.specified (wires request.preparation.inputs).toList
    (wires ⟨request.preparation.fresh,#[]⟩).toList
    (wires request.circuit.circuit.interface.inputs).toList (wires request.circuit.circuit.interface.outputs).toList
    axes.toList operator.coefficient,axes,?_,axisFound,?_⟩
  · simp only [HierarchicalInstrument.Meaning.actual,packetView,prepare.2.1,measureFound,found,evaluated,
      bind,Option.bind,pure,header,axisMatch,Semantics.Instrument.execute_specified]
  · intro outcome output input
    obtain ⟨partition,distinct⟩ := checkAll_input_axes request packet pending accepted
    unfold Semantics.Instrument.branchMatrix
    rw [partition]
    exact Semantics.Instrument.specified_basis_coefficient _ _ _ _ distinct operator.coefficient
      (List.ofFn input) (by simp) _ _

private theorem option_mapM_related {A B : Type} (f : A → Option B) (xs : List A) (ys : List B)
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

theorem array_mapM_fields {A B : Type} (f : A → Option B) (xs : Array A) (ys : Array B)
    (mapped : xs.mapM f = some ys) :
    xs.size = ys.size ∧ ∀ i (hx : i < xs.size) (hy : i < ys.size), f xs[i] = some ys[i] := by
  have related : List.Forall₂ (fun a b => f a = some b) xs.toList ys.toList := by
    apply option_mapM_related
    rw [← Array.toList_mapM,mapped]
    rfl
  exact ⟨related.length_eq,fun i hx hy => related.get hx hy⟩

/-- Accepted target coordinates point exactly to the old input columns. -/
theorem target_positions (request : QpeInstrument.Request) (packet : QpeInstrument.Packet)
    (pending : QpeInstrument.Pending) (accepted : QpeInstrument.checkAll request packet = .ok pending)
    (valid : QpeSchedule.layout request.circuit.circuit = true) :
    (wires request.preparation.inputs).size = request.circuit.circuit.target.size ∧
    ∀ i : Fin request.circuit.circuit.target.size,
      (HierarchicalQpeLayout.inputRoute request.circuit.circuit valid
        (i.natAdd request.circuit.circuit.phase.size)).val = i.val := by
  have stages := QpeInstrument.checkAll_conditions request packet pending accepted
  have facts := QpeInstrument.assemble_conditions request packet pending.circuit pending stages.2
  have boundary := QpeInstrument.boundary_fields request packet facts.2.2.2.1
  obtain ⟨phase,measured,targetMap,_⟩ := QpeInstrument.coordinates_fields request boundary.2.2.2.2.2.2.2.2
  have targetFacts := array_mapM_fields _ _ _ targetMap
  obtain ⟨partition,distinct⟩ := checkAll_input_axes request packet pending accepted
  refine ⟨targetFacts.1.symm,?_⟩
  intro i
  rw [HierarchicalQpeLayout.inputRoute_target]
  have read := targetFacts.2 i.val i.isLt (by omega)
  obtain ⟨coordinateBound,coordinateValue⟩ := Array.getElem?_eq_some_iff.mp read
  have left : (wires request.circuit.circuit.interface.inputs).toList[request.circuit.circuit.target[i]] =
      (wires request.preparation.inputs).toList[i.val]'(by simpa using (show i.val < (wires request.preparation.inputs).size by omega)) := coordinateValue
  have right : (wires request.circuit.circuit.interface.inputs).toList[i.val]'(by rw [partition]; simp; omega) =
      (wires request.preparation.inputs).toList[i.val]'(by simpa using (show i.val < (wires request.preparation.inputs).size by omega)) := by
    simp [partition,show i.val < (wires request.preparation.inputs).size by omega]
  have nd : (wires request.circuit.circuit.interface.inputs).toList.Nodup := by rwa [partition]
  exact nd.getElem_inj_iff.mp (left.trans right.symm)

theorem routeAxes_coordinate (n : Nat) (route : Equiv.Perm (Fin n))
    (axes routeArray selected result : Array Nat)
    (routeList : List.ofFn (fun i => (route i).val) = routeArray.toList)
    (computed : QpeInstrument.routeAxes axes routeArray selected = some result)
    (i axis : Nat) (coordinate : Fin n)
    (selectedAt : selected[i]? = some axis) (resultAt : result[i]? = some coordinate.val) :
    axes[(route.symm coordinate).val]? = some axis := by
  obtain ⟨value,index,hv,position,routed⟩ :=
    QpeInstrument.routeAxes_at axes routeArray selected result computed i axis selectedAt
  have same : value = coordinate.val := Option.some.inj (hv.symm.trans resultAt)
  subst value
  have size : routeArray.size = n := by simpa using (congrArg List.length routeList).symm
  obtain ⟨inside,entry⟩ := Array.getElem?_eq_some_iff.mp routed
  have bound : index < n := by omega
  have value : (route ⟨index,bound⟩).val = coordinate.val := by
    have listEntry := congrArg (fun values : List Nat => values[index]?) routeList
    simpa [bound,routed] using listEntry
  have equal : route ⟨index,bound⟩ = coordinate := Fin.ext value
  have inverse : (route.symm coordinate).val = index := by rw [← equal,Equiv.symm_apply_apply]
  rw [inverse]
  exact (QpeInstrument.position_bound axes axis index position).2

theorem routeAxes_size (axes route selected result : Array Nat)
    (computed : QpeInstrument.routeAxes axes route selected = some result) : selected.size = result.size :=
  (array_mapM_fields _ _ _ computed).1

/-- Geometry extracted from the actual packet; clients do not supply it. -/
structure Geometry (request : QpeInstrument.Request) where
  valid : QpeSchedule.layout request.circuit.circuit = true
  measured : Array Nat
  found : Readout.requestedAxes request.readout = some measured
  oldSize : (wires request.preparation.inputs).size = request.circuit.circuit.target.size
  freshSize : (wires ⟨request.preparation.fresh,#[]⟩).size = request.circuit.circuit.phase.size
  outputSize : (wires request.circuit.circuit.interface.outputs).size =
    request.circuit.circuit.phase.size+request.circuit.circuit.target.size
  measuredSize : measured.size = request.circuit.circuit.phase.size
  residualSize : (wires request.outputs).size = request.circuit.circuit.target.size
  outcomeSize : request.readout.owners.size = request.circuit.circuit.phase.size
  measuredND : measured.toList.Nodup
  residualND : (wires request.outputs).toList.Nodup
  separate : List.Disjoint measured.toList (wires request.outputs).toList
  targetInput : ∀ i : Fin request.circuit.circuit.target.size,
    (HierarchicalQpeLayout.inputRoute request.circuit.circuit valid
      (i.natAdd request.circuit.circuit.phase.size)).val = i.val
  phaseOutput : ∀ i : Fin request.circuit.circuit.phase.size,
    (wires request.circuit.circuit.interface.outputs)[
      ((HierarchicalQpeLayout.outputRoute request.circuit.circuit valid).symm
        (HierarchicalQpeLayout.inputRoute request.circuit.circuit valid
          (i.castAdd request.circuit.circuit.target.size))).val]? = some (measured[i.val]'(by omega))
  targetOutput : ∀ i : Fin request.circuit.circuit.target.size,
    (wires request.circuit.circuit.interface.outputs)[
      ((HierarchicalQpeLayout.outputRoute request.circuit.circuit valid).symm
        (HierarchicalQpeLayout.inputRoute request.circuit.circuit valid
          (i.natAdd request.circuit.circuit.phase.size))).val]? = some ((wires request.outputs)[i.val]'(by omega))

theorem checkAll_geometry (request : QpeInstrument.Request) (packet : QpeInstrument.Packet)
    (pending : QpeInstrument.Pending) (accepted : QpeInstrument.checkAll request packet = .ok pending) :
    Nonempty (Geometry request) := by
  have stages := QpeInstrument.checkAll_conditions request packet pending accepted
  have facts := QpeInstrument.assemble_conditions request packet pending.circuit pending stages.2
  have boundary := QpeInstrument.boundary_fields request packet facts.2.2.2.1
  have rootStages := QpeRoot.checkAll_conditions request.circuit packet.circuit pending.circuit stages.1
  have rootFacts := QpeRoot.assemble_conditions request.circuit packet.circuit pending.circuit.artifact
    pending.circuit rootStages.2
  have schedule := QpeSchedule.inspect_conditions _ _ _ _ _ rootFacts.2.2.2.2.1
  obtain ⟨definition,_,header,sized⟩ := schedule.2.2.2.2.1
  have dims := RoutedPower.sized_fields _ definition sized
  have outputSize : (wires request.circuit.circuit.interface.outputs).size =
      request.circuit.circuit.phase.size+request.circuit.circuit.target.size := by simpa [header] using dims.2.2.2
  obtain ⟨phase,axes,targetMap,phaseMap,phasePerm,found,phaseRoute,targetRoute⟩ :=
    QpeInstrument.coordinates_fields request boundary.2.2.2.2.2.2.2.2
  have phaseLength := (array_mapM_fields _ _ _ phaseMap).1
  have freshSize : (wires ⟨request.preparation.fresh,#[]⟩).size = request.circuit.circuit.phase.size := by
    have length := phasePerm.length_eq
    simp only [Array.length_toList] at length
    omega
  obtain ⟨measured,foundMeasured,measuredSize,measuredND,residualND,separate,_⟩ :=
    HierarchicalInstrument.readout_geometry request.readout packet.readout _ pending.readout facts.2.2.1
  have same : measured = axes := Option.some.inj (foundMeasured.symm.trans found)
  subst measured
  rw [boundary.2.2.1] at residualND separate
  have target := target_positions request packet pending accepted schedule.1
  have residualSize := routeAxes_size _ _ _ _ targetRoute
  have measuredCount : axes.size = request.circuit.circuit.phase.size := measuredSize.trans boundary.2.2.2.2.1
  let geometry : Geometry request := {
    valid := schedule.1, measured := axes, found := found, oldSize := target.1,
    freshSize := freshSize, outputSize := outputSize, measuredSize := measuredCount,
    residualSize := residualSize, outcomeSize := boundary.2.2.2.2.1,
    measuredND := measuredND, residualND := residualND, separate := separate,
    targetInput := target.2,
    phaseOutput := ?_, targetOutput := ?_ }
  · exact ⟨geometry⟩
  · intro i
    apply routeAxes_coordinate _ (HierarchicalQpeLayout.outputRoute request.circuit.circuit schedule.1)
      _ request.circuit.circuit.route axes request.circuit.circuit.phase
      (HierarchicalCircuitTrace.permutation_list _ _ _) phaseRoute i.val _
      (HierarchicalQpeLayout.inputRoute request.circuit.circuit schedule.1 (i.castAdd request.circuit.circuit.target.size))
    · simp [show i.val < axes.size by omega]
    · rw [HierarchicalQpeLayout.inputRoute_phase]
      simp
  · intro i
    apply routeAxes_coordinate _ (HierarchicalQpeLayout.outputRoute request.circuit.circuit schedule.1)
      _ request.circuit.circuit.route (wires request.outputs) request.circuit.circuit.target
      (HierarchicalCircuitTrace.permutation_list _ _ _) targetRoute i.val _
      (HierarchicalQpeLayout.inputRoute request.circuit.circuit schedule.1 (i.natAdd request.circuit.circuit.phase.size))
    · simp [show i.val < (wires request.outputs).size by omega]
    · rw [HierarchicalQpeLayout.inputRoute_target]
      simp

def castBits {a b : Nat} (size : a = b) (bits : Bits b) : Bits a :=
  fun i => bits (Fin.cast size i)

theorem castBits_list {a b : Nat} (size : a = b) (bits : Bits b) :
    List.ofFn (castBits size bits) = List.ofFn bits := by subst b; rfl

def values {A : Type} (xs : Array A) (n : Nat) (size : xs.size = n) : Fin n → A :=
  fun i => xs[i.val]'(by omega)

theorem values_list {A : Type} (xs : Array A) (n : Nat) (size : xs.size = n) :
    List.ofFn (values xs n size) = xs.toList := by
  apply List.ext_getElem
  · simp [size]
  · intro i left right
    simp [values]

theorem values_map {A B : Type} (xs : Array A) (n : Nat) (size : xs.size = n) (f : A → B) :
    List.ofFn (fun i => f (values xs n size i)) = xs.toList.map f := by
  rw [← values_list xs n size,List.map_ofFn]
  rfl

theorem geometry_output_row (request : QpeInstrument.Request) (geometry : Geometry request)
    (outcome : Bits request.circuit.circuit.phase.size) (output : Bits request.circuit.circuit.target.size) :
    List.ofFn (basisEquiv (HierarchicalQpeLayout.outputRoute request.circuit.circuit geometry.valid)
      ((basisEquiv (HierarchicalQpeLayout.inputRoute request.circuit.circuit geometry.valid)).symm (Fin.append outcome output))) =
      (wires request.circuit.circuit.interface.outputs).toList.map
        (QleisliKernel.Semantics.Readout.select geometry.measured.toList
          (fun i => (List.ofFn outcome)[i]?.getD false)
          (Semantics.Instrument.assignment (wires request.outputs).toList
            (castBits (by simpa using geometry.residualSize) output))) := by
  have outputSize := geometry.outputSize
  have residualSize := geometry.residualSize
  let residualState := Semantics.Instrument.assignment (wires request.outputs).toList
    (castBits (by simpa using geometry.residualSize) output)
  have phase : ∀ i : Fin request.circuit.circuit.phase.size,
      values (wires request.circuit.circuit.interface.outputs) _ geometry.outputSize
        ((HierarchicalQpeLayout.outputRoute request.circuit.circuit geometry.valid).symm
          (HierarchicalQpeLayout.inputRoute request.circuit.circuit geometry.valid (i.castAdd request.circuit.circuit.target.size))) =
        values geometry.measured _ geometry.measuredSize i := by
    intro i
    have found := geometry.phaseOutput i
    rw [Array.getElem?_eq_getElem (by have bound := ((HierarchicalQpeLayout.outputRoute request.circuit.circuit geometry.valid).symm
      (HierarchicalQpeLayout.inputRoute request.circuit.circuit geometry.valid (i.castAdd request.circuit.circuit.target.size))).isLt; omega)] at found
    exact Option.some.inj found
  have target : ∀ i : Fin request.circuit.circuit.target.size,
      values (wires request.circuit.circuit.interface.outputs) _ geometry.outputSize
        ((HierarchicalQpeLayout.outputRoute request.circuit.circuit geometry.valid).symm
          (HierarchicalQpeLayout.inputRoute request.circuit.circuit geometry.valid (i.natAdd request.circuit.circuit.phase.size))) =
        values (wires request.outputs) _ geometry.residualSize i := by
    intro i
    have found := geometry.targetOutput i
    rw [Array.getElem?_eq_getElem (by have bound := ((HierarchicalQpeLayout.outputRoute request.circuit.circuit geometry.valid).symm
      (HierarchicalQpeLayout.inputRoute request.circuit.circuit geometry.valid (i.natAdd request.circuit.circuit.phase.size))).isLt; omega)] at found
    exact Option.some.inj found
  have retained (i : Fin request.circuit.circuit.target.size) :
      residualState (values (wires request.outputs) _ geometry.residualSize i) = output i := by
    exact Semantics.Instrument.assignment_at (wires request.outputs).toList geometry.residualND
      (castBits (by simpa using geometry.residualSize) output) ⟨i.val,by simp; omega⟩
  have row := Semantics.QpeFrames.output_row request.circuit.circuit.phase.size request.circuit.circuit.target.size
    (HierarchicalQpeLayout.inputRoute request.circuit.circuit geometry.valid)
    (HierarchicalQpeLayout.outputRoute request.circuit.circuit geometry.valid)
    (values (wires request.circuit.circuit.interface.outputs) _ geometry.outputSize)
    (values geometry.measured _ geometry.measuredSize) (values (wires request.outputs) _ geometry.residualSize)
    (by simpa only [values_list] using geometry.measuredND)
    (by simpa only [values_list] using geometry.separate) phase target outcome output residualState retained
  rw [values_list,values_map] at row
  exact row

/-- The full retained target branch of the actual initialized/read-out transform,
with only equality transports of checked sizes. -/
noncomputable def targetBranch (request : QpeInstrument.Request) (geometry : Geometry request)
    (transform : Semantics.Instrument.Transform Unit) (outcome : Bits request.circuit.circuit.phase.size) :
    Matrix (Bits request.circuit.circuit.target.size) (Bits request.circuit.circuit.target.size) ℂ :=
  fun output input => Semantics.Instrument.branchMatrix (wires request.preparation.inputs).toList
    (wires request.outputs).toList request.readout.owners.size transform
    (castBits geometry.outcomeSize outcome)
    (castBits (by simpa using geometry.residualSize) output)
    (castBits (by simpa using geometry.oldSize) input)

/-- Every actual initialized/readout branch is the coherent root's exact QPE
slice in the checked frames. This identifies operators, including all phases. -/
theorem targetBranch_eq (request : QpeInstrument.Request) (geometry : Geometry request)
    (transform : Semantics.Instrument.Transform Unit) (operator : Operator)
    (columns : ∀ outcome output input,
      Semantics.Instrument.branchMatrix (wires request.preparation.inputs).toList
        (wires request.outputs).toList request.readout.owners.size transform outcome output input =
      operator.coefficient
        ((wires request.circuit.circuit.interface.outputs).toList.map
          (QleisliKernel.Semantics.Readout.select geometry.measured.toList
            (fun position => (List.ofFn outcome)[position]?.getD false)
            (Semantics.Instrument.assignment (wires request.outputs).toList output)))
        (List.ofFn input ++ List.replicate (wires ⟨request.preparation.fresh,#[]⟩).toList.length false))
    (outcome : Bits request.circuit.circuit.phase.size) :
    targetBranch request geometry transform outcome =
      HierarchicalQpeSchedule.branch request.circuit.circuit geometry.valid operator outcome := by
  ext output input
  rw [targetBranch,columns]
  simp only [castBits_list]
  unfold HierarchicalQpeSchedule.branch matrixAt
  rw [geometry_output_row]
  rw [Semantics.QpeFrames.input_zero_list _ _ _ geometry.targetInput]
  rw [show (wires ⟨request.preparation.fresh,#[]⟩).toList.length = request.circuit.circuit.phase.size by simpa using geometry.freshSize]

/-- Complete actual preparation/circuit/readout branch equality, once the
same-artifact provider has been independently identified. -/
theorem checkAll_kraus_withProvider (leaves : Leaves Operator)
    (request : QpeInstrument.Request) (packet : QpeInstrument.Packet) (pending : QpeInstrument.Pending)
    (accepted : QpeInstrument.checkAll request packet = .ok pending)
    (hadamards : ∀ part ∈ pending.circuit.schedule.parts.values, HierarchicalQpeSchedule.LeafEquation leaves part.hadamard)
    (fourier : ∀ r ∈ pending.circuit.schedule.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves packet.circuit.artifact providerFuel request.circuit.circuit.provider = some provider)
    (hi : provider.inputWidth = request.circuit.circuit.target.size)
    (ho : provider.outputWidth = request.circuit.circuit.target.size)
    (U : Matrix (Bits request.circuit.circuit.target.size) (Bits request.circuit.circuit.target.size) ℂ)
    (providerMeaning : matrixAt request.circuit.circuit.target.size request.circuit.circuit.target.size provider = U) :
    ∃ (geometry : Geometry request), ∃ fuel transform,
      HierarchicalInstrument.Meaning.actual leaves request.preparation.inputs (packetView packet) fuel = some transform ∧
      ∀ outcome, targetBranch request geometry transform outcome =
        Qpe.kraus request.circuit.circuit.phase.size U (HierarchicalGradient.number request.circuit.circuit.phase.size outcome) := by
  obtain ⟨geometry⟩ := checkAll_geometry request packet pending accepted
  have stages := QpeInstrument.checkAll_conditions request packet pending accepted
  have rootStages := QpeRoot.checkAll_conditions request.circuit packet.circuit pending.circuit stages.1
  have rootFacts := QpeRoot.assemble_conditions request.circuit packet.circuit pending.circuit.artifact pending.circuit rootStages.2
  obtain ⟨_,fuel,operator,actual,_,_,meaning⟩ := HierarchicalQpeSchedule.inspect_kraus leaves packet.circuit.artifact
    request.circuit.circuit packet.circuit.candidate _ pending.circuit.schedule rootFacts.2.2.2.2.1
    hadamards fourier providerFuel provider evaluated hi ho U providerMeaning
  obtain ⟨transform,axes,read,found,columns⟩ := checkAll_columns leaves request packet pending accepted fuel operator actual
  have same : axes = geometry.measured := Option.some.inj (found.symm.trans geometry.found)
  subst axes
  refine ⟨geometry,fuel,transform,read,?_⟩
  intro outcome
  rw [targetBranch_eq request geometry transform operator columns outcome]
  exact meaning outcome

/-- Complete actual target/reference outcome maps, retaining arbitrary joint
coherences and entanglement rather than only outcome probabilities. -/
theorem checkAll_reference_withProvider {R : Type} [Fintype R] [DecidableEq R]
    (leaves : Leaves Operator)
    (request : QpeInstrument.Request) (packet : QpeInstrument.Packet) (pending : QpeInstrument.Pending)
    (accepted : QpeInstrument.checkAll request packet = .ok pending)
    (hadamards : ∀ part ∈ pending.circuit.schedule.parts.values, HierarchicalQpeSchedule.LeafEquation leaves part.hadamard)
    (fourier : ∀ r ∈ pending.circuit.schedule.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves packet.circuit.artifact providerFuel request.circuit.circuit.provider = some provider)
    (hi : provider.inputWidth = request.circuit.circuit.target.size)
    (ho : provider.outputWidth = request.circuit.circuit.target.size)
    (U : Matrix (Bits request.circuit.circuit.target.size) (Bits request.circuit.circuit.target.size) ℂ)
    (providerMeaning : matrixAt request.circuit.circuit.target.size request.circuit.circuit.target.size provider = U) :
    ∃ (geometry : Geometry request), ∃ fuel transform,
      HierarchicalInstrument.Meaning.actual leaves request.preparation.inputs (packetView packet) fuel = some transform ∧
      ∀ outcome (rho : Matrix (Bits request.circuit.circuit.target.size × R) (Bits request.circuit.circuit.target.size × R) ℂ),
        Qpe.outcomeMap (targetBranch request geometry transform outcome) rho =
          Qpe.outcomeMap (Qpe.kraus request.circuit.circuit.phase.size U
            (HierarchicalGradient.number request.circuit.circuit.phase.size outcome)) rho := by
  obtain ⟨geometry,fuel,transform,actual,meaning⟩ := checkAll_kraus_withProvider leaves request packet pending accepted
    hadamards fourier providerFuel provider evaluated hi ho U providerMeaning
  exact ⟨geometry,fuel,transform,actual,fun outcome rho => by rw [meaning]⟩

theorem bit_kraus_complete (m n : Nat) (U : Matrix (Bits n) (Bits n) ℂ)
    (isometry : Uᴴ * U = 1) :
    Kraus.Complete (fun outcome : Bits m => Qpe.kraus m U (HierarchicalGradient.number m outcome)) := by
  have complete := Qpe.kraus_complete m U isometry
  unfold Kraus.Complete at complete ⊢
  rw [← complete]
  apply Fintype.sum_equiv (Qpe.bitEquiv m)
  intro outcome
  dsimp only
  rw [Qpe.bitEquiv_value,HierarchicalFourier.number_value]

/-- All physical outcomes are complete, once the bound provider's whole-space
isometry is established. The equality is for the actual prepared/readout branches. -/
theorem checkAll_complete_withProvider (leaves : Leaves Operator)
    (request : QpeInstrument.Request) (packet : QpeInstrument.Packet) (pending : QpeInstrument.Pending)
    (accepted : QpeInstrument.checkAll request packet = .ok pending)
    (hadamards : ∀ part ∈ pending.circuit.schedule.parts.values, HierarchicalQpeSchedule.LeafEquation leaves part.hadamard)
    (fourier : ∀ r ∈ pending.circuit.schedule.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (providerFuel : Nat) (provider : Operator)
    (evaluated : physical algebra leaves packet.circuit.artifact providerFuel request.circuit.circuit.provider = some provider)
    (hi : provider.inputWidth = request.circuit.circuit.target.size)
    (ho : provider.outputWidth = request.circuit.circuit.target.size)
    (U : Matrix (Bits request.circuit.circuit.target.size) (Bits request.circuit.circuit.target.size) ℂ)
    (providerMeaning : matrixAt request.circuit.circuit.target.size request.circuit.circuit.target.size provider = U)
    (isometry : Uᴴ * U = 1) :
    ∃ (geometry : Geometry request), ∃ fuel transform,
      HierarchicalInstrument.Meaning.actual leaves request.preparation.inputs (packetView packet) fuel = some transform ∧
      (∀ outcome, targetBranch request geometry transform outcome =
        Qpe.kraus request.circuit.circuit.phase.size U (HierarchicalGradient.number request.circuit.circuit.phase.size outcome)) ∧
      Kraus.Complete (targetBranch request geometry transform) := by
  obtain ⟨geometry,fuel,transform,actual,meaning⟩ := checkAll_kraus_withProvider leaves request packet pending accepted
    hadamards fourier providerFuel provider evaluated hi ho U providerMeaning
  refine ⟨geometry,fuel,transform,actual,meaning,?_⟩
  have equal : targetBranch request geometry transform = fun outcome => Qpe.kraus request.circuit.circuit.phase.size U
      (HierarchicalGradient.number request.circuit.circuit.phase.size outcome) := funext meaning
  rw [equal]
  exact bit_kraus_complete _ _ U isometry

/-- The actual classical result packs the same ordered measurements used by
the target-branch theorem, rather than an independently reconstructed bit order. -/
theorem checkAll_classical (request : QpeInstrument.Request) (packet : QpeInstrument.Packet)
    (pending : QpeInstrument.Pending) (accepted : QpeInstrument.checkAll request packet = .ok pending)
    (values : Nat → Bool) :
    request.outputs.classical = request.readout.inputs.classical.push
      ⟨request.readout.result,#[.bits request.circuit.circuit.phase.size]⟩ ∧
    ∃ measured, Readout.projected packet.readout = some measured ∧
      Readout.assemble packet.readout values = QleisliKernel.Semantics.Readout.encode
        ((measured.map (fun p => p.2.1)).toList.map values) := by
  have stages := QpeInstrument.checkAll_conditions request packet pending accepted
  have facts := QpeInstrument.assemble_conditions request packet pending.circuit pending stages.2
  have boundary := QpeInstrument.boundary_fields request packet facts.2.2.2.1
  have output := (Readout.check_boundary _ _ _ _ facts.2.2.1).2
  refine ⟨?_,Readout.check_assembly _ _ _ _ facts.2.2.1 values⟩
  simpa only [boundary.2.2.1,boundary.2.2.2.2.1] using output

/-- Actual named QPE instrument with an independently requested provider.
Full provider equality and isometry follow from the fresh provider Root binding;
all initialization/readout geometry follows from this instrument's acceptance.
The remaining premises are exact actual finite-byte equations and the separately
interpreted independent provider request, including its global phase. -/
theorem checkAll_kraus (leaves : Leaves Operator)
    (request : QpeInstrument.Request) (packet : QpeInstrument.Packet) (pending : QpeInstrument.Pending)
    (accepted : QpeInstrument.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.circuit.artifact.state.requests.toList, HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ pending.circuit.provider.requests, ∀ obligation,
      Root.finitePair (QpeRoot.providerArtifact request.circuit packet.circuit) request.circuit.provider packet.circuit.pairs i = some obligation →
        HierarchicalRoot.FiniteEquation leaves obligation)
    (hadamards : ∀ part ∈ pending.circuit.schedule.parts.values, HierarchicalQpeSchedule.LeafEquation leaves part.hadamard)
    (fourier : ∀ r ∈ pending.circuit.schedule.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (requestedFuel : Nat) (requested : Operator)
    (required : logical algebra leaves (HierarchicalRoot.requested request.circuit.provider)
      requestedFuel request.circuit.provider.entry = some requested)
    (U : Matrix (Bits request.circuit.circuit.target.size) (Bits request.circuit.circuit.target.size) ℂ)
    (providerMeaning : matrixAt request.circuit.circuit.target.size request.circuit.circuit.target.size requested = U) :
    ∃ (geometry : Geometry request), ∃ fuel transform,
      HierarchicalInstrument.Meaning.actual leaves request.preparation.inputs (packetView packet) fuel = some transform ∧
      (∀ outcome, targetBranch request geometry transform outcome =
        Qpe.kraus request.circuit.circuit.phase.size U (HierarchicalGradient.number request.circuit.circuit.phase.size outcome)) ∧
      Kraus.Complete (targetBranch request geometry transform) := by
  have checked := (QpeInstrument.checkAll_conditions request packet pending accepted).1
  obtain ⟨providerFuel,providerActual,unitary⟩ := HierarchicalQpeRoot.checkAll_provider_equal leaves
    request.circuit packet.circuit pending.circuit checked implementations meanings requestedFuel requested required
  have dims := HierarchicalQpeRoot.checkAll_provider_widths request.circuit packet.circuit pending.circuit checked requested unitary
  have width : HierarchicalOperators.width request.circuit.provider.interface.inputs = request.circuit.circuit.target.size :=
    unitary.1.1.symm.trans dims.1
  have isometry := unitary.1.2.2
  rw [width,providerMeaning] at isometry
  exact checkAll_complete_withProvider leaves request packet pending accepted hadamards fourier
    providerFuel requested providerActual dims.1 dims.2 U providerMeaning isometry

/-- Every outcome is the independently named QPE map on the complete target and
an arbitrary reference; all outcomes together preserve trace. Both statements
concern the actual initialization/circuit/readout reader from the accepted packet. -/
theorem checkAll_reference {R : Type} [Fintype R] [DecidableEq R]
    (leaves : Leaves Operator)
    (request : QpeInstrument.Request) (packet : QpeInstrument.Packet) (pending : QpeInstrument.Pending)
    (accepted : QpeInstrument.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.circuit.artifact.state.requests.toList, HierarchicalFiniteUnitary.Leaf leaves leaf)
    (meanings : ∀ i ∈ pending.circuit.provider.requests, ∀ obligation,
      Root.finitePair (QpeRoot.providerArtifact request.circuit packet.circuit) request.circuit.provider packet.circuit.pairs i = some obligation →
        HierarchicalRoot.FiniteEquation leaves obligation)
    (hadamards : ∀ part ∈ pending.circuit.schedule.parts.values, HierarchicalQpeSchedule.LeafEquation leaves part.hadamard)
    (fourier : ∀ r ∈ pending.circuit.schedule.inverse.fourier.body.requests, HierarchicalHadamard.Equation leaves r)
    (requestedFuel : Nat) (requested : Operator)
    (required : logical algebra leaves (HierarchicalRoot.requested request.circuit.provider)
      requestedFuel request.circuit.provider.entry = some requested)
    (U : Matrix (Bits request.circuit.circuit.target.size) (Bits request.circuit.circuit.target.size) ℂ)
    (providerMeaning : matrixAt request.circuit.circuit.target.size request.circuit.circuit.target.size requested = U) :
    ∃ (geometry : Geometry request), ∃ fuel transform,
      HierarchicalInstrument.Meaning.actual leaves request.preparation.inputs (packetView packet) fuel = some transform ∧
      Kraus.Complete (targetBranch request geometry transform) ∧
      (∀ outcome (rho : Matrix (Bits request.circuit.circuit.target.size × R) (Bits request.circuit.circuit.target.size × R) ℂ),
        Semantics.Instrument.density (targetBranch request geometry transform outcome) rho =
          Qpe.outcomeMap (Qpe.kraus request.circuit.circuit.phase.size U
            (HierarchicalGradient.number request.circuit.circuit.phase.size outcome)) rho) ∧
      (∀ rho : Matrix (Bits request.circuit.circuit.target.size × R) (Bits request.circuit.circuit.target.size × R) ℂ,
        ∑ outcome, Matrix.trace (Semantics.Instrument.density (targetBranch request geometry transform outcome) rho) = Matrix.trace rho) := by
  obtain ⟨geometry,fuel,transform,actual,meaning,complete⟩ := checkAll_kraus leaves request packet pending accepted
    implementations meanings hadamards fourier requestedFuel requested required U providerMeaning
  refine ⟨geometry,fuel,transform,actual,complete,?_,?_⟩
  · intro outcome rho
    change Qpe.outcomeMap (targetBranch request geometry transform outcome) rho = _
    rw [meaning]
  · intro rho
    exact Qpe.complete_trace (targetBranch request geometry transform) complete rho

end Qleisli.HierarchicalQpeInstrument
