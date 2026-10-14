import QleisliKernel.Qirf.EngineeringInstrument
import Qleisli.EngineeringInstrument
import Qleisli.QirfInstrumentContract
import Qleisli.QirfValidity

/-! Original-graph meaning for the separate engineering instrument comparison.
The independent complete unnormalized instrument retains all original public
labels, residual coherences and arbitrary finite references. Each original
graph has its own exact body meaning and complete Kraus equation. The inequality
does not identify those meanings, permit cleanup or coherent control, certify
resources or discharge constitutional PR/RS, even at epsilon zero. Source/type
lowering, decoder, native compiler/runtime and public byte APIs remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.NativeEngineeringInstrument
open QleisliKernel QleisliKernel.Semantics.Exact
open QleisliKernel.Qirf.EngineeringInstrument
open Qleisli.Semantics.EngineeringInstrument
open scoped BigOperators Matrix

/-- Original public result IDs determine the labels; private histories are
summed by the independent CP semantics and are never renormalized. -/
noncomputable def originalOperators (rows cols results : Nat) (outputs : List Nat)
    (histories : List QleisliKernel.Raw.Instrument.History) :
    Kraus Unit (Fin results → Bool) (Fin histories.length) (Fin cols) (Fin rows) :=
  fun _ outcome => Qleisli.Qirf.InstrumentContract.operators outputs histories
    (List.ofFn outcome) rows cols

theorem prepared_choi (rows cols results : Nat) (outputs : List Nat)
    (original : List QleisliKernel.Raw.Instrument.History)
    (prepared : List QleisliKernel.Raw.InstrumentEquality.History) (work left : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.prepare outputs original).run work =
      (.ok prepared,left))
    (input : Unit) (outcome : Fin results → Bool) (row otherRow : Fin rows) (col otherCol : Fin cols) :
    choi (originalOperators rows cols results outputs original) input outcome
      (row,col) (otherRow,otherCol) =
    choi (Qleisli.EngineeringInstrument.historyOperators rows cols results prepared) input outcome
      (row,col) (otherRow,otherCol) := by
  change Qleisli.Semantics.InstrumentEquality.choi
    (Qleisli.Qirf.InstrumentContract.operators outputs original (List.ofFn outcome) rows cols)
      (row,col) (otherRow,otherCol) =
    Qleisli.Semantics.InstrumentEquality.choi
      (Qleisli.Raw.InstrumentEquality.operators prepared (List.ofFn outcome) rows cols)
        (row,col) (otherRow,otherCol)
  rw [Qleisli.Qirf.InstrumentContract.choi_projected,
    Qleisli.Raw.InstrumentEquality.choi_meaning,
    Qleisli.Qirf.InstrumentContract.prepare_projected _ _ _ _ _ ok]

/-- Equality of projected coefficients transfers every amplified adjoint
observable, without equating private history indices or dropping public labels. -/
theorem prepared_adjoint {R : Type} [Fintype R]
    (rows cols results : Nat) (outputs : List Nat)
    (original : List QleisliKernel.Raw.Instrument.History)
    (prepared : List QleisliKernel.Raw.InstrumentEquality.History) (work left : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.prepare outputs original).run work =
      (.ok prepared,left))
    (observables : Observable (Fin results → Bool) (Fin rows) R) (input : Unit) :
    adjointWithReference (originalOperators rows cols results outputs original) observables input =
      adjointWithReference (Qleisli.EngineeringInstrument.historyOperators rows cols results prepared)
        observables input := by
  rw [Qleisli.EngineeringInstrument.adjoint_coefficients,
    Qleisli.EngineeringInstrument.adjoint_coefficients]
  simp_rw [prepared_choi rows cols results outputs original prepared work left ok]

private theorem validate_dimensions (rows cols results : Nat)
    (histories : List QleisliKernel.Raw.InstrumentEquality.History) (work left : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.validate rows cols results histories).run work =
      (.ok (),left)) :
    ∀ history ∈ histories, history.operator.rows = rows ∧ history.operator.cols = cols := by
  obtain ⟨_,middle,_,rest⟩ := QleisliKernel.Finite.bind_success _ _ _ _ _ ok
  intro history member
  obtain ⟨before,after,h⟩ := Qleisli.Raw.InstrumentEquality.forM_member _ _ _ _ rest history member
  obtain ⟨_,_,_,h⟩ := QleisliKernel.Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := QleisliKernel.Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,_,dimensions,_⟩ := QleisliKernel.Finite.bind_success _ _ _ _ _ h
  simpa only [Bool.and_eq_true,beq_iff_eq] using
    (QleisliKernel.Finite.guard_success _ _ _ _ dimensions).1

private theorem prepare_dimensions (outputs : List Nat)
    (original : List QleisliKernel.Raw.Instrument.History)
    (prepared : List QleisliKernel.Raw.InstrumentEquality.History) (work left rows cols : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.prepare outputs original).run work =
      (.ok prepared,left))
    (valid : ∀ history ∈ prepared, history.operator.rows = rows ∧ history.operator.cols = cols) :
    ∀ history ∈ original, history.operator.rows = rows ∧ history.operator.cols = cols := by
  have relation := Qleisli.Raw.InstrumentEquality.prepare_reference _ _ _ _ _ ok
  clear ok
  induction relation with
  | nil => simp
  | @cons a b as bs relates rest ih =>
    intro history member
    rcases List.mem_cons.mp member with same | tail
    · subst history
      rw [relates.1]
      exact valid b (by simp)
    · exact ih (fun h member => valid h (by simp [member])) history tail

/-- Independent original-body denotation and exact completeness, for one
freshly checked graph. This is not a source-preservation or target claim. -/
structure BodyMeaning (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (root : QleisliKernel.Qirf.Validity.Root) (instrument : QleisliKernel.Raw.Instrument.Checked) : Prop where
  rootMeaning : Qleisli.Qirf.Validity.RootMeaning artifact order root
  body : Qleisli.Semantics.RawInstrument.ProgramMeaning root.dependencies root.program []
    (instrument.histories.map Qleisli.Raw.Instrument.Denotation.reference)
  complete : ∑ h, (Qleisli.Raw.Instrument.family instrument h)ᴴ *
    Qleisli.Raw.Instrument.family instrument h = 1

/-- The complete requested signature/projection checks and the original maps
remain distinct from the engineering inequality between those maps. -/
structure Meaning (request : Request) (checked : Checked)
    (projection : QleisliKernel.Semantics.InstrumentContract.Projection) : Prop where
  actual : BodyMeaning request.actual request.actualOrder checked.actual checked.actualInstrument
  expected : BodyMeaning request.expected request.expectedOrder checked.expected checked.expectedInstrument
  signaturesEqual : request.actualSignature = request.expectedSignature
  projected : ∃ before after,
    (QleisliKernel.Qirf.InstrumentContract.project request.expectedSignature.result).run before =
      (.ok projection,after)
  actualInterface : ∃ before after,
    (QleisliKernel.Qirf.InstrumentContract.interface request.actualSignature projection checked.actual).run
      before = (.ok (),after)
  expectedInterface : ∃ before after,
    (QleisliKernel.Qirf.InstrumentContract.interface request.expectedSignature projection checked.expected).run
      before = (.ok (),after)
  actualDimensions : ∀ h ∈ checked.actualInstrument.histories,
    h.operator.rows = 2^checked.actualInstrument.structureCheck.state.quantum.frame.length ∧
    h.operator.cols = 2^checked.actualInstrument.structureCheck.prepared.inputBits
  expectedDimensions : ∀ h ∈ checked.expectedInstrument.histories,
    h.operator.rows = 2^checked.actualInstrument.structureCheck.state.quantum.frame.length ∧
    h.operator.cols = 2^checked.actualInstrument.structureCheck.prepared.inputBits
  bound : CompleteAdjointBound
    (originalOperators (2^checked.actualInstrument.structureCheck.state.quantum.frame.length)
      (2^checked.actualInstrument.structureCheck.prepared.inputBits) projection.classicalBits
      checked.actual.program.classicalOutputs checked.actualInstrument.histories)
    (originalOperators (2^checked.actualInstrument.structureCheck.state.quantum.frame.length)
      (2^checked.actualInstrument.structureCheck.prepared.inputBits) projection.classicalBits
      checked.expected.program.classicalOutputs checked.expectedInstrument.histories)
    (Qleisli.Semantics.Exact.rational request.epsilon : ℝ)

theorem check_meaning (request : Request) (checked : Checked) (work left : Nat)
    (ok : (QleisliKernel.Qirf.EngineeringInstrument.check request).run work = (.ok checked,left)) :
    ∃ projection, Meaning request checked projection := by
  obtain ⟨accepted⟩ := QleisliKernel.Qirf.EngineeringInstrument.check_acceptance _ _ _ _ ok
  have facts := QleisliKernel.Engineering.Instrument.checkHistories_conditions
    _ _ _ _ _ _ _ _ _ _ accepted.bounded
  obtain ⟨a,b,ha⟩ := facts.actualValidated
  obtain ⟨c,d,he⟩ := facts.expectedValidated
  have actualDimensions := prepare_dimensions _ _ _ _ _ _ _ accepted.actualPrepared
    (validate_dimensions _ _ _ _ _ _ ha)
  have expectedDimensions := prepare_dimensions _ _ _ _ _ _ _ accepted.expectedPrepared
    (validate_dimensions _ _ _ _ _ _ he)
  have bounded := Qleisli.EngineeringInstrument.checkHistories_bound
    _ _ _ _ _ _ _ _ _ _ accepted.bounded
  refine ⟨accepted.projection,⟨?_,?_,accepted.signaturesEqual,
    ⟨_,_,accepted.projected⟩,⟨_,_,accepted.actualInterface⟩,⟨_,_,accepted.expectedInterface⟩,
    actualDimensions,expectedDimensions,⟨bounded.1,?_⟩⟩⟩
  · exact ⟨Qleisli.Qirf.Validity.root_meaning _ _ _ _
      (QleisliKernel.Qirf.Validity.checkRoot_postcondition _ _ _ _ _ accepted.actualRoot),
      Qleisli.Qirf.InstrumentContract.reconstruct_denotes _ _ _ _ _ _ accepted.actualReconstructed,
      Qleisli.Qirf.InstrumentContract.reconstruct_kraus_complete _ _ _ _ _ _ accepted.actualReconstructed⟩
  · exact ⟨Qleisli.Qirf.Validity.root_meaning _ _ _ _
      (QleisliKernel.Qirf.Validity.checkRoot_postcondition _ _ _ _ _ accepted.expectedRoot),
      Qleisli.Qirf.InstrumentContract.reconstruct_denotes _ _ _ _ _ _ accepted.expectedReconstructed,
      Qleisli.Qirf.InstrumentContract.reconstruct_kraus_complete _ _ _ _ _ _ accepted.expectedReconstructed⟩
  · intro R _ observables input
    rw [prepared_adjoint _ _ _ _ _ _ _ _ accepted.actualPrepared,
      prepared_adjoint _ _ _ _ _ _ _ _ accepted.expectedPrepared]
    exact bounded.2 R observables input

end Qleisli.NativeEngineeringInstrument
