import Qleisli.HierarchicalRoot
import Qleisli.Semantics.Instrument
import QleisliKernel.Hierarchical.Instrument

/-! Complete branch binding for actual initialize/unitary/readout packets.
The only semantic premises are the same actual finite-byte equations required
by Root; no source or independently named QPE formula is assumed proved.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.HierarchicalInstrument
open QleisliKernel.Hierarchical
open Artifact HierarchicalFiniteEvaluation HierarchicalOperators
open HierarchicalRoot (FiniteEquation)
namespace Meaning

/-- This reader uses actual initialization/readout bodies, actual entry ports
and constructed physical evaluation. Proposed meanings and proof conclusions
cannot supply an initialization or measured axis. -/
noncomputable def actual {Reference : Type} (leaves : Leaves Operator)
    (inputs : Side) (packet : Instrument.Packet) (fuel : Nat) :
    Option (Semantics.Instrument.Transform Reference) := do
  let fresh ← packet.preparation.initializations.mapM Preparation.project
  let measured ← Readout.projected packet.readout
  let definition ← packet.artifact.definitions[packet.artifact.entry.implementation]?
  let operator ← physical algebra leaves packet.artifact fuel packet.artifact.entry.implementation
  return Semantics.Instrument.execute (wires inputs).toList (wires ⟨fresh,#[]⟩).toList
    (wires definition.interface.inputs).toList (wires definition.interface.outputs).toList
    (measured.map (fun p => p.2.2)).toList operator.coefficient

/-- Independent request interpretation. Fresh and measured coordinates come
from the caller's request, and the pure operator comes from its meaning graph. -/
noncomputable def requested {Reference : Type} (leaves : Leaves Operator)
    (request : Instrument.Request) (fuel : Nat) :
    Option (Semantics.Instrument.Transform Reference) := do
  let measured ← Readout.requestedAxes request.readout
  let operator ← logical algebra leaves (HierarchicalRoot.requested request.circuit)
    fuel request.circuit.entry
  return Semantics.Instrument.specified (wires request.preparation.inputs).toList
    (wires ⟨request.preparation.fresh,#[]⟩).toList
    (wires request.circuit.interface.inputs).toList (wires request.circuit.interface.outputs).toList
    measured.toList operator.coefficient

/-- Proof metadata and submitted meanings cannot change the actual branch
interpretation. Classical packing is checked separately by `checkAll_classical`.
This lemma does not assert validity of an artifact after its metadata changes. -/
theorem actual_ir_only {Reference : Type} (leaves : Leaves Operator) (inputs : Side)
    (first second : Instrument.Packet) (fuel : Nat)
    (initializations : first.preparation.initializations = second.preparation.initializations)
    (measurements : first.readout.measurements = second.readout.measurements)
    (definitions : first.artifact.definitions = second.artifact.definitions)
    (entry : first.artifact.entry.implementation = second.artifact.entry.implementation) :
    actual (Reference := Reference) leaves inputs first fuel = actual leaves inputs second fuel := by
  have pure := physical_ir_only algebra leaves first.artifact second.artifact definitions
  simp only [actual,initializations,Readout.projected,measurements,definitions,entry,pure]

end Meaning

/-- Classical output order is checked against the actual intermediate CBit
names, in the same request that binds the quantum instrument. -/
theorem checkAll_classical (request : Instrument.Request) (packet : Instrument.Packet)
    (pending : Instrument.Pending) (accepted : Instrument.checkAll request packet = .ok pending)
    (values : Nat → Bool) :
    request.outputs.classical = request.readout.inputs.classical.push
        ⟨request.readout.result,#[.bits request.readout.owners.size]⟩ ∧
    ∃ measured, Readout.projected packet.readout = some measured ∧
      Readout.assemble packet.readout values = QleisliKernel.Semantics.Readout.encode
        ((measured.map (fun (p : Nat × Nat × Nat) => p.2.1)).toList.map values) := by
  have stages := Instrument.checkAll_stages request packet pending accepted
  have checked := (Instrument.assemble_conditions request packet pending.circuit pending stages.2).2.2.2.2.1
  have boundary := Instrument.checkAll_boundary request packet pending accepted
  have outputs := (Readout.check_boundary _ _ _ _ checked).2
  exact ⟨by simpa only [boundary.2.2] using outputs,
    Readout.check_assembly _ _ _ _ checked values⟩

/-- Acceptance constructs one full unnormalized branch transform on arbitrary
residual/reference states. Neither a whole-graph interpretation equation nor a
claimed algorithm conclusion is a premise. -/
theorem checkAll_branches {Reference : Type} (leaves : Leaves Operator)
    (request : Instrument.Request) (packet : Instrument.Packet) (pending : Instrument.Pending)
    (accepted : Instrument.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.circuit.artifact.state.requests.toList, Equation leaves leaf)
    (meanings : ∀ i ∈ pending.circuit.binding.requests, ∀ obligation,
      Root.finitePair packet.artifact request.circuit packet.pairs i = some obligation →
        FiniteEquation leaves obligation) :
    ∃ fuel transform,
      Meaning.actual (Reference := Reference) leaves request.preparation.inputs packet fuel = some transform ∧
      Meaning.requested leaves request fuel = some transform := by
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
    axes.toList operator.coefficient,?_,?_⟩
  · simp only [Meaning.actual,prepare.2.1,measureFound,definitionFound,physical,
      bind,Option.bind,pure,header,axisMatch,Semantics.Instrument.execute_specified]
  · simp only [Meaning.requested,axisFound,logical,bind,Option.bind,pure]

/-- Equality of full residual/reference density matrices for every outcome.
The caller's joint input may contain arbitrary coherences or entanglement.
This is not merely equality of measurement probabilities. -/
theorem checkAll_density {Reference : Type} [Fintype Reference] [DecidableEq Reference]
    (leaves : Leaves Operator) (request : Instrument.Request) (packet : Instrument.Packet)
    (pending : Instrument.Pending) (accepted : Instrument.checkAll request packet = .ok pending)
    (implementations : ∀ leaf ∈ pending.circuit.artifact.state.requests.toList, Equation leaves leaf)
    (meanings : ∀ i ∈ pending.circuit.binding.requests, ∀ obligation,
      Root.finitePair packet.artifact request.circuit packet.pairs i = some obligation →
        FiniteEquation leaves obligation)
    (rho : Matrix ((Fin (wires request.preparation.inputs).toList.length → Bool) × Reference)
      ((Fin (wires request.preparation.inputs).toList.length → Bool) × Reference) ℂ)
    (outcome : Fin request.readout.owners.size → Bool) :
    ∃ fuel actual required,
      Meaning.actual leaves request.preparation.inputs packet fuel = some actual ∧
      Meaning.requested leaves request fuel = some required ∧
      Semantics.Instrument.density
          (Semantics.Instrument.branchMatrix (wires request.preparation.inputs).toList
            (wires request.outputs).toList request.readout.owners.size actual outcome) rho =
        Semantics.Instrument.density
          (Semantics.Instrument.branchMatrix (wires request.preparation.inputs).toList
            (wires request.outputs).toList request.readout.owners.size required outcome) rho := by
  obtain ⟨fuel,transform,physical,logical⟩ := checkAll_branches (Reference := Unit)
    leaves request packet pending accepted implementations meanings
  exact ⟨fuel,transform,transform,physical,logical,rfl⟩

end Qleisli.HierarchicalInstrument
