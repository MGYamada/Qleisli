import Qleisli.HierarchicalInstrument
import Qleisli.Semantics.InstrumentCoordinates

/-! Exact branch columns of the actual accepted initialization/circuit/readout.
The finite-leaf correspondence premises remain explicit. No named QPE meaning,
source preservation or native/transport correspondence is asserted here.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.HierarchicalInstrument
open QleisliKernel.Hierarchical
open Artifact HierarchicalFiniteEvaluation HierarchicalOperators
open HierarchicalRoot (FiniteEquation)

theorem sideValid_axes (side : Side) (valid : sideValid side = true) :
    (wires side).toList.Nodup := by
  unfold sideValid at valid
  split at valid
  next exceeded => contradiction
  next bounded =>
    simp only [Bool.and_eq_true,decide_eq_true_eq] at valid
    exact valid.2

theorem preparation_axes (request : Preparation.Request) :
    (wires (Preparation.output request)).toList =
      (wires request.inputs).toList ++ (wires ⟨request.fresh,#[]⟩).toList := by
  simp [wires,Preparation.output,Array.foldl_append_eq_append]

/-- The actual preparation check establishes the complete old/fresh axis
partition and its distinctness; these are not extra caller assumptions. -/
theorem checkAll_input_axes (request : Instrument.Request) (packet : Instrument.Packet)
    (pending : Instrument.Pending) (accepted : Instrument.checkAll request packet = .ok pending) :
    (wires request.circuit.interface.inputs).toList =
      (wires request.preparation.inputs).toList ++ (wires ⟨request.preparation.fresh,#[]⟩).toList ∧
    ((wires request.preparation.inputs).toList ++
      (wires ⟨request.preparation.fresh,#[]⟩).toList).Nodup := by
  have stages := Instrument.checkAll_stages request packet pending accepted
  have conditions := Instrument.assemble_conditions request packet pending.circuit pending stages.2
  have preparation := conditions.2.2.2.1
  have bound := (Preparation.check_binding _ _ _ _ preparation).1
  have valid := (Preparation.check_conditions _ _ _ _ preparation).2.2
  have outputValid : sideValid packet.preparation.outputs = true := by
    simp only [Preparation.valid,Bool.and_eq_true] at valid
    exact valid.1.1.1.1.2
  have distinct := sideValid_axes packet.preparation.outputs outputValid
  rw [bound,preparation_axes] at distinct
  have boundary := (Instrument.checkAll_boundary request packet pending accepted).1
  refine ⟨?_,distinct⟩
  rw [← boundary,bound,preparation_axes]

/-- Every exact branch column is a zero-extended column of the constructed
actual circuit operator. Initialization, measured coordinates and axis
distinctness follow from this same packet's checks. Arbitrary input columns
and residual coordinates retain all phases needed by subsequent composition. -/
theorem checkAll_columns (leaves : Leaves Operator)
    (request : Instrument.Request) (packet : Instrument.Packet) (pending : Instrument.Pending)
    (accepted : Instrument.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.circuit.artifact.state.requests.toList, Equation leaves leaf)
    (meanings : ∀ i ∈ pending.circuit.binding.requests, ∀ obligation,
      Root.finitePair packet.artifact request.circuit packet.pairs i = some obligation →
        FiniteEquation leaves obligation) :
    ∃ fuel transform operator axes,
      Meaning.actual leaves request.preparation.inputs packet fuel = some transform ∧
      physical algebra leaves packet.artifact fuel packet.artifact.entry.implementation = some operator ∧
      Readout.requestedAxes request.readout = some axes ∧
      ∀ (input : List Bool), input.length = (wires request.preparation.inputs).toList.length →
        ∀ (outcome residual : Semantics.Instrument.Coordinates),
          transform (fun label (_ : Unit) => if label = input then 1 else 0) outcome residual () =
            operator.coefficient
              ((wires request.circuit.interface.outputs).toList.map
                (QleisliKernel.Semantics.Readout.select axes.toList outcome residual))
              (input ++ List.replicate (wires ⟨request.preparation.fresh,#[]⟩).toList.length false) := by
  have stages := Instrument.checkAll_stages request packet pending accepted
  have conditions := Instrument.assemble_conditions request packet pending.circuit pending stages.2
  have prepare := Preparation.check_binding _ _ _ _ conditions.2.2.2.1
  have readCheck := conditions.2.2.2.2.1
  obtain ⟨_,axes,measured,axisFound,measureFound,_,_,axisMatch⟩ :=
    Readout.valid_binding request.readout packet.readout
      (Readout.check_conditions _ _ _ _ readCheck).2.2
  obtain ⟨fuel,operator,physical,logical⟩ := HierarchicalRoot.checkAll_denotes
    algebra leaves packet.artifact packet.order request.circuit packet.pairs packet.pairOrder
    pending.circuit stages.1 implementations meanings
  have rootChecks := Root.checkAll_conditions _ _ _ _ _ _ stages.1
  have root := Root.inspect_conditions _ _ _ _ _ _ rootChecks.2
  obtain ⟨definition,proof,pair,definitionFound,_,_,_,_,_,header,_,_⟩ :=
    HierarchicalRoot.root_fields _ _ _ root.2.2.1
  refine ⟨fuel,Semantics.Instrument.specified (wires request.preparation.inputs).toList
    (wires ⟨request.preparation.fresh,#[]⟩).toList
    (wires request.circuit.interface.inputs).toList (wires request.circuit.interface.outputs).toList
    axes.toList operator.coefficient,operator,axes,?_,physical,axisFound,?_⟩
  · simp only [Meaning.actual,prepare.2.1,measureFound,definitionFound,physical,
      bind,Option.bind,pure,header,axisMatch,Semantics.Instrument.execute_specified]
  · intro input sized outcome residual
    obtain ⟨partition,distinct⟩ := checkAll_input_axes request packet pending accepted
    rw [partition]
    exact Semantics.Instrument.specified_basis_coefficient _ _ _ _ distinct operator.coefficient
      input sized outcome residual

/-- The public branch matrix is a slice of the constructed physical operator:
old inputs are extended by zero bits, and actual ordered measurements choose
rows while the complete residual frame is retained. -/
theorem checkAll_branchColumns (leaves : Leaves Operator)
    (request : Instrument.Request) (packet : Instrument.Packet) (pending : Instrument.Pending)
    (accepted : Instrument.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.circuit.artifact.state.requests.toList, Equation leaves leaf)
    (meanings : ∀ i ∈ pending.circuit.binding.requests, ∀ obligation,
      Root.finitePair packet.artifact request.circuit packet.pairs i = some obligation →
        FiniteEquation leaves obligation) :
    ∃ fuel transform operator axes,
      Meaning.actual leaves request.preparation.inputs packet fuel = some transform ∧
      physical algebra leaves packet.artifact fuel packet.artifact.entry.implementation = some operator ∧
      Readout.requestedAxes request.readout = some axes ∧
      ∀ outcome output input,
        Semantics.Instrument.branchMatrix (wires request.preparation.inputs).toList
          (wires request.outputs).toList request.readout.owners.size transform outcome output input =
          operator.coefficient
            ((wires request.circuit.interface.outputs).toList.map
              (QleisliKernel.Semantics.Readout.select axes.toList
                (fun position => (List.ofFn outcome)[position]?.getD false)
                (Semantics.Instrument.assignment (wires request.outputs).toList output)))
            (List.ofFn input ++ List.replicate (wires ⟨request.preparation.fresh,#[]⟩).toList.length false) := by
  obtain ⟨fuel,transform,operator,axes,actual,physical,found,columns⟩ :=
    checkAll_columns leaves request packet pending accepted implementations meanings
  refine ⟨fuel,transform,operator,axes,actual,physical,found,?_⟩
  intro outcome output input
  exact columns (List.ofFn input) (by simp) _ _

end Qleisli.HierarchicalInstrument
