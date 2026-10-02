import QleisliKernel.Raw.Coefficient
import Qleisli.RawProtectedEvaluation
import Qleisli.Semantics.RawAction
import Qleisli.Semantics.ObservingAction

/-! Actual matrix-free exact coefficients refine independent unbounded complex
actions, including the original physical C/W/C body and protected zero image.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.Coefficient
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open QleisliKernel.Raw.Coefficient QleisliKernel.Finite Qleisli.Semantics.Exact
open ProtectedEvaluation (StateMeaning)

private theorem sum_fold (term : Nat → WorkM Scalar) (meaning : Nat → ℂ)
    (sound : ∀ index value work left, (term index).run work = (.ok value,left) → scalar value = meaning index)
    (indices : List Nat) (initial actual : Scalar) (work left : Nat)
    (ok : (indices.foldlM (fun previous index => do
      let value ← term index
      lift (arithmetic (QleisliKernel.Exact.Scalar.add previous value))) initial).run work = (.ok actual,left)) :
    scalar actual = scalar initial + (indices.map meaning).sum := by
  induction indices generalizing initial work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst actual
    simp
  | cons index indices ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,hr⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨value,after,hv,ha⟩ := bind_success _ _ _ _ _ hn
    have added := Exact.scalar_add_preserves _ _ _ (arithmetic_success _ _ (lift_success _ _ _ _ ha).1)
    have rest := ih next middle hr
    rw [added,sound _ _ _ _ hv] at rest
    simpa only [List.map_cons,List.sum_cons,add_assoc] using rest

theorem sum_meaning (count : Nat) (term : Nat → WorkM Scalar) (meaning : Nat → ℂ)
    (sound : ∀ index value work left, (term index).run work = (.ok value,left) → scalar value = meaning index)
    (actual : Scalar) (work left : Nat) (ok : (sum count term).run work = (.ok actual,left)) :
    scalar actual = ((List.range count).map meaning).sum := by
  obtain ⟨_,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  simpa only [Exact.scalar_zero_meaning,zero_add] using sum_fold term meaning sound _ _ _ _ _ h

theorem step_meaning (dependencies : List Dependency) (operation : Step)
    (state : State) (ψ : Nat → ℂ) (represented : StateMeaning state ψ) :
    StateMeaning (step dependencies operation state) (Qleisli.Semantics.RawAction.step dependencies operation ψ) := by
  intro output actual work left ok
  obtain ⟨_,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  change (if !enabled operation.controls output then _ else _ : WorkM Scalar).run middle = _ at h
  simp only [Qleisli.Semantics.RawAction.step]
  split at h
  · rename_i disabled
    simp only [disabled,if_true]
    exact represented _ _ _ _ h
  · rename_i active
    simp only [active,Bool.false_eq_true,if_false]
    cases ha : operation.action with
    | hadamard axis =>
      rw [ha] at h
      exact ProtectedEvaluation.gate_meaning .h axis state ψ represented output actual middle left h
    | monomial axes permutation phases =>
      rw [ha] at h
      dsimp only at h ⊢
      apply sum_meaning _ _ _ _ _ _ _ h
      intro input value work left accepted
      split at accepted
      · rename_i selected
        obtain ⟨previous,after,hp,hm⟩ := bind_success _ _ _ _ _ accepted
        have result := ProtectedEvaluation.multiply_meaning _ _ _ _ _ hm
        have phase := ProtectedEvaluation.phaseValue_meaning (phases[input]?.getD 0)
        change scalar (QleisliKernel.Exact.Scalar.phase (phases[input]?.getD 0)) = _ at phase
        rw [represented _ _ _ _ hp,phase] at result
        simpa only [selected,if_true] using result
      · rename_i rejected
        have same := (pure_success _ _ _ _ accepted).1
        subst value
        simpa only [rejected,if_false] using Exact.scalar_zero_meaning
    | contract axes index adjoint =>
      rw [ha] at h
      dsimp only at h ⊢
      obtain ⟨dependency,after,hd,h⟩ := bind_success _ _ _ _ _ h
      have found := (lift_success _ _ _ _ hd).1
      have present : dependencies[index]? = some dependency := by
        cases eq : dependencies[index]? <;> simp_all [readOption]
      rw [present]
      apply sum_meaning _ _ _ _ _ _ _ h
      intro input value work left accepted
      obtain ⟨previous,w₁,hp,h⟩ := bind_success _ _ _ _ _ accepted
      obtain ⟨entryValue,w₂,he,hm⟩ := bind_success _ _ _ _ _ h
      have result := ProtectedEvaluation.multiply_meaning _ _ _ _ _ hm
      rw [represented _ _ _ _ hp] at result
      have read := arithmetic_success _ _ (lift_success _ _ _ _ he).1
      cases adjoint with
      | false =>
        cases read
        exact result
      | true =>
        rw [Exact.scalar_conjugate_preserves _ _ read] at result
        exact result

theorem circuit_meaning (dependencies : List Dependency) (operations : List Step)
    (state : State) (ψ : Nat → ℂ) (represented : StateMeaning state ψ) :
    StateMeaning (circuit dependencies operations state) (Qleisli.Semantics.RawAction.circuit dependencies operations ψ) := by
  induction operations generalizing state ψ with
  | nil => exact represented
  | cons operation operations ih =>
    simpa only [circuit,Qleisli.Semantics.RawAction.circuit,List.foldl_cons] using
      ih _ _ (step_meaning dependencies operation state ψ represented)

theorem event_meaning (dependencies : List Dependency) (operation : Event)
    (state : State) (ψ : Nat → ℂ) (represented : StateMeaning state ψ) :
    StateMeaning (event dependencies operation state) (Qleisli.Semantics.RawAction.event dependencies operation ψ) := by
  intro output actual work left ok
  obtain ⟨_,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  cases operation with
  | circuit bits steps => exact circuit_meaning dependencies steps state ψ represented output actual middle left h
  | init0 bits =>
    change (if output < 2^bits then state output else pure Scalar.zero).run middle = _ at h
    split at h
    · rename_i small
      simpa [Qleisli.Semantics.RawAction.event,small] using represented _ _ _ _ h
    · rename_i large
      have same := (pure_success _ _ _ _ h).1
      subst actual
      simpa [Qleisli.Semantics.RawAction.event,large] using Exact.scalar_zero_meaning
  | liftBasis before after inputAxes outputAxes table =>
    apply sum_meaning _ _ _ _ _ _ _ h
    intro input value work left success
    split at success
    · rename_i selected
      simpa [selected] using represented _ _ _ _ success
    · rename_i absent
      have same := (pure_success _ _ _ _ success).1
      subst value
      simpa [absent] using Exact.scalar_zero_meaning
  | reorder bits axes =>
    apply sum_meaning _ _ _ _ _ _ _ h
    intro input value work left success
    split at success
    · rename_i selected
      simpa [selected] using represented _ _ _ _ success
    · rename_i absent
      have same := (pure_success _ _ _ _ success).1
      subst value
      simpa [absent] using Exact.scalar_zero_meaning
  | computed bits axes sourceBits ancillaBits function uses logical =>
    apply circuit_meaning dependencies
      ([computeStep sourceBits axes.length ancillaBits function] ++ uses ++
        [computeStep sourceBits axes.length ancillaBits function]) _
      (fun input => if input < 2^axes.length then ψ (scatter output axes input) else 0) ?_
      (gather output axes) actual middle left h
    intro input value work left success
    change (if input < 2^axes.length then state (scatter output axes input) else pure Scalar.zero).run work = (.ok value,left) at success
    change scalar value = if input < 2^axes.length then ψ (scatter output axes input) else 0
    split at success
    · rename_i inData
      simpa [inData] using represented _ _ _ _ success
    · rename_i outside
      have same := (pure_success _ _ _ _ success).1
      subst value
      simpa [outside] using Exact.scalar_zero_meaning
  | protectedComputed bits axes sourceBits ancillaBits function uses =>
    obtain ⟨_,after,hg,h⟩ := bind_success _ _ _ _ _ h
    have valid := (guard_success _ _ _ _ hg).1
    have diagonal := Qleisli.Raw.uses_valid_diagonal _ _ _ _ valid
    let source := gather output axes % 2^sourceBits
    let input : Nat → ℂ := fun target => ψ (scatter output axes (source+target*2^sourceBits))
    have inputMeaning : StateMeaning (fun target => state (scatter output axes (source+target*2^sourceBits))) input := by
      intro target value work left success
      exact represented _ _ _ _ success
    have result := ProtectedEvaluation.run_meaning source (function[source]?.getD 0) uses _ input inputMeaning
      (gather output axes / 2^sourceBits) actual after left h
    let logicalInput : Qleisli.Semantics.Protected.Logical Unit :=
      fun source target _ => ψ (scatter output axes (source+target*2^sourceBits))
    have physical := Qleisli.Semantics.Protected.clean_factorization
      (fun source => function[source]?.getD 0) uses diagonal logicalInput
    change scalar actual = Qleisli.Semantics.Protected.compute (fun source => function[source]?.getD 0)
      (Qleisli.Semantics.Protected.run uses (Qleisli.Semantics.Protected.compute
        (fun source => function[source]?.getD 0) (Qleisli.Semantics.Protected.zero logicalInput)))
      source 0 (gather output axes / 2^sourceBits) ()
    rw [physical]
    exact result

theorem erased_meaning (bits : Nat) (axes : List Nat) (outcome : Nat)
    (state : State) (ψ : Nat → ℂ) (represented : StateMeaning state ψ) :
    StateMeaning (erased bits axes outcome state) (Qleisli.Semantics.ObservingAction.erase bits axes outcome ψ) := by
  intro output actual work left ok
  apply sum_meaning _ _ _ _ _ _ _ ok
  intro input value work left success
  split at success
  · rename_i selected
    simp only [Bool.and_eq_true,beq_iff_eq] at selected
    simpa only [selected,if_true] using represented _ _ _ _ success
  · rename_i absent
    simp only [Bool.and_eq_true,beq_iff_eq] at absent
    have same := (pure_success _ _ _ _ success).1
    subst value
    simpa only [absent,if_false] using Exact.scalar_zero_meaning

end Qleisli.Raw.Coefficient
