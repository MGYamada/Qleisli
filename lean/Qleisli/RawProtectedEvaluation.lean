import QleisliKernel.Raw.ProtectedEvaluation
import Qleisli.RawDenotation
import Qleisli.RawProtected

/-! Actual original-use evaluation to complete physical complex coefficients.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.ProtectedEvaluation
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open QleisliKernel.Raw QleisliKernel.Raw.ProtectedEvaluation QleisliKernel.Finite
open Qleisli.Semantics.Exact

def StateMeaning (state : QleisliKernel.Raw.ProtectedEvaluation.State) (ψ : Nat → ℂ) : Prop :=
  ∀ label value work left, (state label).run work = (.ok value,left) → scalar value = ψ label

private theorem halfRoot_meaning : scalar QleisliKernel.Finite.halfRoot = Qleisli.Semantics.Finite.halfRoot := by
  simp [QleisliKernel.Finite.halfRoot,Qleisli.Semantics.Finite.halfRoot,scalar,rational,Coefficient.integer]
  ring

private theorem phase_meaning (k : Nat) : scalar (QleisliKernel.Exact.Scalar.phase k) = Qleisli.Semantics.Finite.phase k := by
  have residue : (k : Int) % 8 = (k % 8 : Nat) := by omega
  have bound : k % 8 < 8 := Nat.mod_lt _ (by omega)
  unfold QleisliKernel.Exact.Scalar.phase Qleisli.Semantics.Finite.phase
  rw [residue]
  generalize k % 8 = r at *
  interval_cases r <;> simp [scalar,rational,Coefficient.integer,Qleisli.Semantics.Finite.halfRoot] <;> ring

theorem multiply_meaning (value factor result : Scalar) (work left : Nat)
    (ok : (multiply value factor).run work = (.ok result,left)) :
    scalar result = scalar value * scalar factor := by
  exact Exact.scalar_mul_preserves _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ ok).1)

theorem gate_meaning (operation : Gate) (axis : Nat) (state : QleisliKernel.Raw.ProtectedEvaluation.State)
    (ψ : Nat → ℂ) (represented : StateMeaning state ψ) :
    StateMeaning (gate operation axis state) (Qleisli.Semantics.Protected.gate operation axis ψ) := by
  intro label value work left ok
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  cases operation with
  | x => exact represented _ _ _ _ h
  | z =>
    obtain ⟨previous,w₂,hp,hm⟩ := bind_success _ _ _ _ _ h
    have result := multiply_meaning _ _ _ _ _ hm
    rw [represented _ _ _ _ hp,phaseValue,phase_meaning] at result
    by_cases condition : bit label axis = 1 <;>
      simpa [Qleisli.Semantics.Protected.gate,Qleisli.Semantics.Finite.phase,condition] using result
  | t =>
    obtain ⟨previous,w₂,hp,hm⟩ := bind_success _ _ _ _ _ h
    have result := multiply_meaning _ _ _ _ _ hm
    rw [represented _ _ _ _ hp,phaseValue,phase_meaning] at result
    by_cases condition : bit label axis = 1 <;>
      simpa [Qleisli.Semantics.Protected.gate,Qleisli.Semantics.Finite.phase,condition] using result
  | h =>
    obtain ⟨low,w₂,hl,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨high,w₃,hh,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨signed,w₄,hs,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨combined,w₅,hc,hm⟩ := bind_success _ _ _ _ _ h
    have lowMeaning := represented _ _ _ _ hl
    have highMeaning := represented _ _ _ _ hh
    have signedMeaning : scalar signed = if bit label axis == 1 then
        -ψ (label-bit label axis*2^axis+2^axis) else ψ (label-bit label axis*2^axis+2^axis) := by
      have signedOk := arithmetic_success _ _ (lift_success _ _ _ _ hs).1
      split at signedOk
      · rename_i condition
        have negated := Exact.scalar_neg_preserves _ _ signedOk
        simpa [condition,highMeaning] using negated
      · rename_i condition
        cases signedOk
        simpa [condition] using highMeaning
    have added := Exact.scalar_add_preserves _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ hc).1)
    have result := multiply_meaning _ _ _ _ _ hm
    rw [added,lowMeaning,signedMeaning,halfRoot_meaning] at result
    exact result

theorem use_meaning (source ancilla : Nat) (operation : Use) (state : QleisliKernel.Raw.ProtectedEvaluation.State)
    (ψ : Nat → ℂ) (represented : StateMeaning state ψ) :
    StateMeaning (use source ancilla operation state)
      (fun label => Qleisli.Semantics.Protected.blockUse source ancilla operation (fun label (_ : Unit) => ψ label) label ()) := by
  intro label value work left ok
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  cases operation with
  | protectedGate location operation =>
    obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨previous,w₃,hp,hm⟩ := bind_success _ _ _ _ _ h
    have result := multiply_meaning _ _ _ _ _ hm
    rw [represented _ _ _ _ hp,phaseValue,phase_meaning] at result
    simp only [Qleisli.Semantics.Protected.blockUse]
    split_ifs at result ⊢ <;> simp_all only [Qleisli.Semantics.Finite.phase]
  | targetGate controls axis operation =>
    change (if QleisliKernel.Semantics.Protected.enabled source ancilla controls then
      gate operation axis state label else state label).run w₁ = (.ok value,left) at h
    split at h
    · rename_i enabled
      simpa [Qleisli.Semantics.Protected.blockUse,enabled] using gate_meaning operation axis state ψ represented label value w₁ left h
    · rename_i disabled
      simpa [Qleisli.Semantics.Protected.blockUse,disabled] using represented _ _ _ _ h
  | phase controls operation =>
    obtain ⟨previous,w₂,hp,hm⟩ := bind_success _ _ _ _ _ h
    have result := multiply_meaning _ _ _ _ _ hm
    rw [represented _ _ _ _ hp,phaseValue,phase_meaning] at result
    simp only [Qleisli.Semantics.Protected.blockUse]
    split_ifs at result ⊢ <;> simp_all only [Qleisli.Semantics.Finite.phase]

theorem run_meaning (source ancilla : Nat) (operations : List Use)
    (state : QleisliKernel.Raw.ProtectedEvaluation.State) (ψ : Nat → ℂ) (represented : StateMeaning state ψ) :
    StateMeaning (run source ancilla operations state)
      (fun label => Qleisli.Semantics.Protected.blocks source ancilla operations (fun label (_ : Unit) => ψ label) label ()) := by
  induction operations generalizing state ψ with
  | nil => exact represented
  | cons operation operations ih =>
    have next := use_meaning source ancilla operation state ψ represented
    have final := ih _ _ next
    have eta : (fun label (_ : Unit) => Qleisli.Semantics.Protected.blockUse source ancilla operation
        (fun label (_ : Unit) => ψ label) label ()) =
        Qleisli.Semantics.Protected.blockUse source ancilla operation (fun label (_ : Unit) => ψ label) := by
      funext label reference
      cases reference
      rfl
    simpa [run,Qleisli.Semantics.Protected.blocks,List.foldl_cons,eta] using final

theorem coefficient_meaning (sourceBits : Nat) (function : List Nat) (uses : List Use)
    (valid : ∀ use ∈ uses, Qleisli.Semantics.Protected.DiagonalProtected use)
    (dimension index : Nat) (value : Scalar) (work left : Nat)
    (ok : (coefficient sourceBits function uses dimension index).run work = (.ok value,left)) :
    scalar value = Qleisli.Semantics.ProtectedMatrix.coefficient sourceBits function uses dimension index := by
  let row := index / dimension
  let col := index % dimension
  let source := row % 2^sourceBits
  let ψ : Nat → ℂ := fun target => if target == col / 2^sourceBits then 1 else 0
  have initial : StateMeaning (fun target => pure (if target == col / 2^sourceBits then Scalar.one else Scalar.zero)) ψ := by
    intro label value work left good
    have same := (pure_success _ _ _ _ good).1
    subst value
    change scalar (if label == col / 2^sourceBits then Scalar.one else Scalar.zero) =
      if label == col / 2^sourceBits then 1 else 0
    split_ifs
    · exact Exact.scalar_one_meaning
    · exact Exact.scalar_zero_meaning
  have physical := Qleisli.Semantics.Protected.clean_factorization
    (fun source => function[source]?.getD 0) uses valid
    (Qleisli.Semantics.ProtectedMatrix.basis sourceBits col)
  unfold Qleisli.Semantics.ProtectedMatrix.coefficient
  change scalar value = Qleisli.Semantics.Protected.compute (fun source => function[source]?.getD 0)
    (Qleisli.Semantics.Protected.run uses (Qleisli.Semantics.Protected.compute
      (fun source => function[source]?.getD 0) (Qleisli.Semantics.Protected.zero
        (Qleisli.Semantics.ProtectedMatrix.basis sourceBits col)))) source 0 (row / 2^sourceBits) ()
  rw [physical]
  simp only [Qleisli.Semantics.Protected.zero,Qleisli.Semantics.Protected.logical]
  change scalar value = Qleisli.Semantics.Protected.blocks source (function[source]?.getD 0) uses
    (Qleisli.Semantics.ProtectedMatrix.basis sourceBits col source) (row / 2^sourceBits) ()
  unfold coefficient at ok
  change (if source == col % 2^sourceBits then _ else _ : WorkM Scalar).run work = _ at ok
  split at ok
  · rename_i sameSource
    have expected := run_meaning source (function[source]?.getD 0) uses _ ψ initial
      (row / 2^sourceBits) value work left ok
    have equal : Qleisli.Semantics.ProtectedMatrix.basis sourceBits col source =
        fun target (_ : Unit) => if target == col / 2^sourceBits then (1 : ℂ) else 0 := by
      funext target reference
      simp [Qleisli.Semantics.ProtectedMatrix.basis,sameSource]
    rw [equal]
    exact expected
  · rename_i differentSource
    have same := (pure_success _ _ _ _ ok).1
    subst value
    have equal : Qleisli.Semantics.ProtectedMatrix.basis sourceBits col source =
        fun _ _ => (0 : ℂ) := by
      funext target reference
      simp [Qleisli.Semantics.ProtectedMatrix.basis,differentSource]
    rw [equal,Qleisli.Semantics.Protected.blocks_zero]
    exact Exact.scalar_zero_meaning

private theorem map_relation {α β : Type} (operation : α → WorkM β) (relation : α → β → Prop)
    (sound : ∀ item value work left, (operation item).run work = (.ok value,left) → relation item value)
    (items : List α) (values : List β) (work left : Nat)
    (ok : (items.mapM operation).run work = (.ok values,left)) : List.Forall₂ relation items values := by
  induction items generalizing values work left with
  | nil =>
    simp only [List.mapM_nil] at ok
    rw [(pure_success _ _ _ _ ok).1]
    exact .nil
  | cons item items ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨value,w₁,hv,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨rest,w₂,hr,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst values
    exact .cons (sound item value work w₁ hv) (ih rest w₁ w₂ hr)

theorem matrix_meaning (sourceBits dataBits ancillaBits : Nat) (function : List Nat) (uses : List Use)
    (actual : Matrix) (work left : Nat)
    (ok : (matrix sourceBits dataBits ancillaBits function uses).run work = (.ok actual,left)) :
    Qleisli.Semantics.ProtectedMatrix.Meaning sourceBits dataBits function uses actual := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hg,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨entries,w₄,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₅,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  have good := (guard_success _ _ _ _ hg).1
  simp only [Bool.and_eq_true] at good
  have diagonal := uses_valid_diagonal _ _ _ _ good.2
  have values := map_relation _ _ (coefficient_meaning sourceBits function uses diagonal (2^dataBits)) _ _ _ _ he
  have made := (QleisliKernel.Exact.matrix_make_value _ _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ hm).1)).1
  rw [made]
  exact ⟨rfl,rfl,values⟩

theorem event_denotes (dependencies : List Dependency) (event : Event) (actual : Matrix) (work left : Nat)
    (ok : (QleisliKernel.Raw.ProtectedEvaluation.eventMatrix dependencies event).run work = (.ok actual,left)) :
    Qleisli.Semantics.Raw.EventMeaning dependencies event actual := by
  cases event with
  | protectedComputed bits axes sourceBits ancillaBits function uses =>
    obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨logical,w₂,hm,hp⟩ := bind_success _ _ _ _ _ h
    exact ⟨logical,Or.inr (matrix_meaning _ _ _ _ _ _ _ _ hm),promote_denotes _ _ _ _ _ _ hp⟩
  | circuit _ _ | init0 _ | liftBasis _ _ _ _ _ | reorder _ _ | computed _ _ _ _ _ _ _ =>
    exact Qleisli.Raw.event_denotes _ _ _ _ _ ok

theorem events_denote (dependencies : List Dependency) (events : List Event) (initial actual : Matrix)
    (work left : Nat) (ok : (events.foldlM (QleisliKernel.Raw.ProtectedEvaluation.evolve dependencies) initial).run work = (.ok actual,left)) :
    Qleisli.Semantics.Raw.EventsMeaning dependencies events initial actual := by
  induction events generalizing initial work with
  | nil =>
    simp only [List.foldlM_nil] at ok
    rw [(pure_success _ _ _ _ ok).1]
    exact .nil _
  | cons event events ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,he⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨action,before,ha,hc⟩ := bind_success _ _ _ _ _ hn
    exact .cons _ _ _ _ _ _ (event_denotes _ _ _ _ _ ha)
      (Exact.compose_meaning _ _ _ _ _ (exactWork_success _ _ _ _ hc)) (ih next middle he)

theorem reconstruct_denotes (dependencies : List Dependency) (program : Program) (actual : Matrix)
    (work left : Nat) (ok : (QleisliKernel.Raw.ProtectedEvaluation.reconstruct dependencies program).run work = (.ok actual,left)) :
    Qleisli.Semantics.Raw.ProgramMeaning dependencies program actual := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨prepared,w₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨initial,w₄,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₅,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  have original := prepare_reference _ _ _ (lift_success _ _ _ _ hp).1
  have identity := arithmetic_success _ _ (lift_success _ _ _ _ hi).1
  rcases Exact.identity_meaning _ _ identity with ⟨_,rows,cols,entries⟩
  exact ⟨prepared.reference,initial,original,⟨rows,cols,fun row col hr hc => entries row col (rows ▸ hr) (cols ▸ hc)⟩,
    events_denote _ _ _ _ _ _ he⟩

end Qleisli.Raw.ProtectedEvaluation
