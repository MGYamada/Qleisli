import NativeCoefficient
import QleisliKernel.Qirf.InstrumentContract

/-! Original-QIRF gate refinement, still unwired from public acceptance.
All premises below are actual executions, not supplied matrices or receipts.
No source/type-lowering, decoder, runtime or constitutional discharge is claimed.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Experiments.OriginalInstrumentGate
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Observation QleisliKernel.Finite
open Qleisli.Semantics.Exact QleisliKernel.Qirf.InstrumentContract
open scoped BigOperators Matrix

theorem reconstruct_denotes (dependencies : List QleisliKernel.Semantics.Finite.Dependency)
    (program : Program) (classical : List Bool)
    (checked : QleisliKernel.Raw.Instrument.Checked) (work left : Nat)
    (ok : (QleisliKernel.Raw.Instrument.reconstruct dependencies program classical).run work = (.ok checked,left)) :
    Qleisli.Semantics.RawInstrument.ProgramMeaning dependencies program classical
      (checked.histories.map Qleisli.Raw.Instrument.Denotation.reference) := by
  rcases QleisliKernel.Raw.Instrument.reconstruct_execution _ _ _ _ _ _ ok with
    ⟨initial,a,b,c,hv,hi,he,_⟩
  have original := (QleisliKernel.Raw.Observation.verify_conditions _ _ _ _ _ hv).2.2
  have identity := Qleisli.Exact.identity_meaning _ _ hi
  refine ⟨checked.structureCheck.prepared,initial,original,?_,
    Qleisli.Raw.Instrument.Denotation.run_reference _ _ _ _ _ _ _ he⟩
  exact ⟨identity.2.1,identity.2.2.1,fun row col hr hc => identity.2.2.2 row col
    (identity.2.1 ▸ hr) (identity.2.2.1 ▸ hc)⟩

theorem reconstruct_complete (dependencies : List QleisliKernel.Semantics.Finite.Dependency)
    (program : Program) (classical : List Bool)
    (checked : QleisliKernel.Raw.Instrument.Checked) (work left : Nat)
    (ok : (QleisliKernel.Raw.Instrument.reconstruct dependencies program classical).run work = (.ok checked,left)) :
    ∀ row col, row < 2^checked.structureCheck.prepared.inputBits → col < 2^checked.structureCheck.prepared.inputBits →
      (checked.histories.map (fun h => Qleisli.Raw.Instrument.historyGram h row col)).sum =
        if row = col then 1 else 0 := by
  rcases QleisliKernel.Raw.Instrument.reconstruct_conditions _ _ _ _ _ _ ok with
    ⟨_,_,_,total,identity,_,hg,hi,equal⟩
  have complete := Qleisli.Raw.Instrument.gram_meaning _ _ _ _ _ hg
  have identityEntries := (Qleisli.Exact.identity_meaning _ _ hi).2.2.2
  intro row col hr hc
  rw [← complete.2.2 row col hr hc,equal]
  exact identityEntries row col hr hc

private theorem range_sum (n : Nat) (f : Nat → ℂ) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    rw [Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc,Fin.val_last] using congrArg (fun z => z + f n) ih

/-- Complete trace preservation follows from the executable Gram check,
including every hidden reset/discard/measurement outcome. -/
theorem reconstruct_kraus_complete (dependencies : List QleisliKernel.Semantics.Finite.Dependency)
    (program : Program) (classical : List Bool)
    (checked : QleisliKernel.Raw.Instrument.Checked) (work left : Nat)
    (ok : (QleisliKernel.Raw.Instrument.reconstruct dependencies program classical).run work = (.ok checked,left)) :
    ∑ i, (Qleisli.Raw.Instrument.family checked i)ᴴ * Qleisli.Raw.Instrument.family checked i = 1 := by
  have complete := reconstruct_complete _ _ _ _ _ _ ok
  rcases QleisliKernel.Raw.Instrument.reconstruct_execution _ _ _ _ _ _ ok with ⟨_,_,_,_,_,_,_,shape⟩
  have rows : ∀ h ∈ checked.histories,
      h.operator.rows = 2^checked.structureCheck.state.quantum.frame.length := by
    simp only [List.all_eq_true,Bool.and_eq_true,beq_iff_eq] at shape
    exact fun h member => (shape h member).1
  ext row col
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply]
  have lists : (checked.histories.map (fun h => Qleisli.Raw.Instrument.historyGram h row col)).sum =
      ∑ i, ∑ k, star (Qleisli.Raw.Instrument.family checked i k row) * Qleisli.Raw.Instrument.family checked i k col := by
    rw [← List.ofFn_getElem_eq_map checked.histories (fun h => Qleisli.Raw.Instrument.historyGram h row col),List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    rw [Qleisli.Raw.Instrument.historyGram,rows _ (List.getElem_mem _)]
    exact range_sum _ _
  rw [← lists]
  have result := complete row col row.isLt col.isLt
  simpa only [Fin.ext_iff] using result

/-- Public labels are read independently from the original result IDs. Hidden
indices stay private, and their complete unnormalized operators are summed. -/
noncomputable def projected (outputs : List Nat)
    (histories : List QleisliKernel.Raw.Instrument.History) (outcome : List Bool)
    (row col otherRow otherCol : Nat) : ℂ :=
  (histories.map fun history =>
    if outputs.mapM (Qleisli.Semantics.RawInstrument.value history.values) = some outcome then
      entry history.operator row col * star (entry history.operator otherRow otherCol) else 0).sum

theorem prepare_projected (outputs : List Nat)
    (original : List QleisliKernel.Raw.Instrument.History)
    (prepared : List QleisliKernel.Raw.InstrumentEquality.History) (work left : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.prepare outputs original).run work = (.ok prepared,left))
    (outcome : List Bool) (row col otherRow otherCol : Nat) :
    InstrumentCoefficient.meaning prepared outcome row col otherRow otherCol =
      projected outputs original outcome row col otherRow otherCol := by
  have relation := InstrumentCoefficient.prepare_reference _ _ _ _ _ ok
  clear ok
  induction relation with
  | nil => rfl
  | @cons a b as bs relates rest ih =>
    simp only [InstrumentCoefficient.meaning,projected,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    simp only [InstrumentCoefficient.contribution,← relates.1,relates.2,Option.some.injEq]

noncomputable def operators (outputs : List Nat)
    (histories : List QleisliKernel.Raw.Instrument.History) (outcome : List Bool)
    (rows cols : Nat) : Fin histories.length → Matrix (Fin rows) (Fin cols) ℂ :=
  fun index row col => if outputs.mapM (Qleisli.Semantics.RawInstrument.value histories[index].values) = some outcome then
    entry histories[index].operator row col else 0

theorem choi_projected (outputs : List Nat) (histories : List QleisliKernel.Raw.Instrument.History)
    (outcome : List Bool) (rows cols : Nat) (row otherRow : Fin rows) (col otherCol : Fin cols) :
    InstrumentEquality.choi (operators outputs histories outcome rows cols) (row,col) (otherRow,otherCol) =
      projected outputs histories outcome row col otherRow otherCol := by
  unfold InstrumentEquality.choi projected
  rw [← List.ofFn_getElem_eq_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro index _
  simp only [operators]
  split <;> simp_all

private theorem validate_dimensions (rows cols results : Nat)
    (histories : List QleisliKernel.Raw.InstrumentEquality.History) (work left : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.validate rows cols results histories).run work = (.ok (),left)) :
    ∀ history ∈ histories, history.operator.rows = rows ∧ history.operator.cols = cols := by
  obtain ⟨_,middle,_,rest⟩ := bind_success _ _ _ _ _ ok
  intro history member
  obtain ⟨before,after,h⟩ := InstrumentCoefficient.forM_member _ _ _ _ rest history member
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,dimensions,_⟩ := bind_success _ _ _ _ _ h
  simpa only [Bool.and_eq_true,beq_iff_eq] using (guard_success _ _ _ _ dimensions).1

private theorem prepare_dimensions (outputs : List Nat)
    (original : List QleisliKernel.Raw.Instrument.History)
    (prepared : List QleisliKernel.Raw.InstrumentEquality.History) (work left rows cols : Nat)
    (ok : (QleisliKernel.Raw.InstrumentEquality.prepare outputs original).run work = (.ok prepared,left))
    (valid : ∀ history ∈ prepared, history.operator.rows = rows ∧ history.operator.cols = cols) :
    ∀ history ∈ original, history.operator.rows = rows ∧ history.operator.cols = cols := by
  have relation := InstrumentCoefficient.prepare_reference _ _ _ _ _ ok
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

/-- The compared families contain every original row and column; equality is
not obtained by truncating an expected instrument to the actual dimensions. -/
theorem check_dimensions (actual expected : QleisliKernel.Qirf.Artifact)
    (actualOrder expectedOrder : Array Nat)
    (actualSignature expectedSignature : QleisliKernel.Semantics.InstrumentContract.Signature)
    (identity : QleisliKernel.Semantics.Function.Identity) (checked : Checked) (work left : Nat)
    (ok : (check actual actualOrder expected expectedOrder actualSignature expectedSignature identity).run work =
      (.ok checked,left)) :
    (∀ history ∈ checked.actualInstrument.histories,
      history.operator.rows = 2^checked.actualInstrument.structureCheck.state.quantum.frame.length ∧
      history.operator.cols = 2^checked.actualInstrument.structureCheck.prepared.inputBits) ∧
    (∀ history ∈ checked.expectedInstrument.histories,
      history.operator.rows = 2^checked.actualInstrument.structureCheck.state.quantum.frame.length ∧
      history.operator.cols = 2^checked.actualInstrument.structureCheck.prepared.inputBits) := by
  obtain ⟨accepted⟩ := check_acceptance _ _ _ _ _ _ _ _ _ _ ok
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ accepted.compared
  obtain ⟨_,w₂,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,he,_⟩ := bind_success _ _ _ _ _ h
  exact ⟨prepare_dimensions _ _ _ _ _ _ _ accepted.actualPrepared (validate_dimensions _ _ _ _ _ _ ha),
    prepare_dimensions _ _ _ _ _ _ _ accepted.expectedPrepared (validate_dimensions _ _ _ _ _ _ he)⟩

/-- Success of the actual complete original-graph gate gives exact equality of
the original outcome-indexed maps on any joint matrix and finite reference.
The acceptance facts separately retain fresh roots/dependencies, signatures,
principal-effect/interface checks and both reconstruction executions. -/
theorem check_instrument {R : Type} [Fintype R] [DecidableEq R]
    (actual expected : QleisliKernel.Qirf.Artifact) (actualOrder expectedOrder : Array Nat)
    (actualSignature expectedSignature : QleisliKernel.Semantics.InstrumentContract.Signature)
    (identity : QleisliKernel.Semantics.Function.Identity) (checked : Checked) (work left : Nat)
    (ok : (check actual actualOrder expected expectedOrder actualSignature expectedSignature identity).run work =
      (.ok checked,left))
    (rho : Matrix (Fin (2^checked.actualInstrument.structureCheck.prepared.inputBits) × R)
      (Fin (2^checked.actualInstrument.structureCheck.prepared.inputBits) × R) ℂ) :
    (fun outcome => InstrumentEquality.channel
      (operators checked.actual.program.classicalOutputs checked.actualInstrument.histories outcome
        (2^checked.actualInstrument.structureCheck.state.quantum.frame.length)
        (2^checked.actualInstrument.structureCheck.prepared.inputBits)) rho) =
    (fun outcome => InstrumentEquality.channel
      (operators checked.expected.program.classicalOutputs checked.expectedInstrument.histories outcome
        (2^checked.actualInstrument.structureCheck.state.quantum.frame.length)
        (2^checked.actualInstrument.structureCheck.prepared.inputBits)) rho) := by
  obtain ⟨accepted⟩ := check_acceptance _ _ _ _ _ _ _ _ _ _ ok
  apply InstrumentEquality.instrument_eq_of_choi_eq
  intro outcome
  ext ⟨row,col⟩ ⟨otherRow,otherCol⟩
  rw [choi_projected,choi_projected,
    ← prepare_projected _ _ _ _ _ accepted.actualPrepared,
    ← prepare_projected _ _ _ _ _ accepted.expectedPrepared]
  exact InstrumentCoefficient.compare_meaning _ _ _ _ _ _ _ accepted.compared
    _ _ _ _ _ row.isLt col.isLt otherRow.isLt otherCol.isLt

end Qleisli.Experiments.OriginalInstrumentGate
