import Qleisli.HierarchicalFourier
import Qleisli.Qpe
import Qleisli.CoordinateOperators

/-! Matrix composition used by the actual-circuit QPE binding.
The three component equations are explicit premises here; the actual IR
inspector must establish them. No projected plan, algorithm name or provider
flag supplies an equation. All coefficients retain global and relative phase.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.HierarchicalQpeCircuit
open scoped BigOperators Matrix

variable {T : Type} [Fintype T] [DecidableEq T]

/-- Phase-fixed H on the only bit, expressed without a checker or gate name. -/
noncomputable def oneHadamard :
    Matrix (CoordinateOperators.Bits 1) (CoordinateOperators.Bits 1) ℂ :=
  fun output input => Interference.complexModel.halfRoot *
    if output 0 && input 0 then -1 else 1

/-- Tensor preparation retains the same little-endian order at every width. -/
noncomputable def hadamards : (width : Nat) →
    Matrix (CoordinateOperators.Bits width) (CoordinateOperators.Bits width) ℂ
  | 0 => 1
  | width+1 => CoordinateOperators.tensor (hadamards width) oneHadamard

theorem hadamards_zero (width : Nat) (output : CoordinateOperators.Bits width) :
    hadamards width output (fun _ => false) = Interference.complexModel.halfRoot^width := by
  induction width with
  | zero =>
    have same : output = (fun _ => false) := Subsingleton.elim _ _
    simp [hadamards,Matrix.one_apply,same]
  | succ width ih =>
    simp only [hadamards,CoordinateOperators.tensor,oneHadamard,Bool.and_false,
      Bool.false_eq_true,if_false,mul_one,ih,pow_succ]

/-- One actual H event at each ordered phase coordinate composes to the tensor
preparation above. The subsequent binder supplies these individual H equations. -/
theorem hadamard_schedule (width : Nat) :
    (List.ofFn (fun axis : Fin width =>
      CoordinateOperators.lift (fun _ : Fin 1 => axis) oneHadamard)).foldl
      (fun before operator => operator * before) 1 = hadamards width := by
  induction width with
  | zero => simp [hadamards]
  | succ width ih =>
    rw [List.ofFn_succ',List.concat_eq_append,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    have mapped :
        (List.ofFn (fun axis : Fin width =>
          CoordinateOperators.lift (fun _ : Fin 1 => axis.castSucc) oneHadamard)) =
        (List.ofFn (fun axis : Fin width =>
          CoordinateOperators.lift (fun _ : Fin 1 => axis) oneHadamard)).map
          (CoordinateOperators.lift (Fin.castAdd 1)) := by
      rw [List.map_ofFn]
      congr 1
      funext axis
      have injective : Function.Injective (Fin.castAdd 1 : Fin width → Fin (width+1)) := by
        intro a b equal
        exact Fin.ext (congrArg (fun i : Fin (width+1) => i.val) equal)
      simp only [Function.comp_apply]
      rw [CoordinateOperators.lift_compose _ injective]
      rfl
    rw [mapped,List.foldl_map]
    rw [← CoordinateOperators.lift_one (Fin.castAdd 1),← CoordinateOperators.lift_left_fold,ih]
    have last : (fun _ : Fin 1 => Fin.last width) = (Fin.natAdd width : Fin 1 → Fin (width+1)) := by
      funext i
      apply Fin.ext
      simp
    rw [last,CoordinateOperators.tensor_lifts]
    rfl

/-- Apply a phase-register matrix while retaining the complete target. -/
noncomputable def onPhase {P : Type} [DecidableEq T] (A : Matrix P P ℂ) :
    Matrix (P × T) (P × T) ℂ :=
  fun output input => if output.2 = input.2 then A output.1 input.1 else 0

/-- The controlled-power layer retains every phase-register basis label.
The target action includes the complete provider phase. -/
noncomputable def powers (width : Nat) (U : Matrix T T ℂ) :
    Matrix ((Fin width → Bool) × T) ((Fin width → Bool) × T) ℂ :=
  fun output input => if output.1 = input.1 then
    (U ^ HierarchicalGradient.number width input.1) output.2 input.2 else 0

/-- Basis-label-preserving blocks, without assuming the phase register is in
a basis state or unentangled with its target. -/
noncomputable def blocks {P : Type} [DecidableEq P] (A : P → Matrix T T ℂ) :
    Matrix (P × T) (P × T) ℂ :=
  fun output input => if output.1 = input.1 then A input.1 output.2 input.2 else 0

omit [DecidableEq T] in
theorem blocks_mul {P : Type} [Fintype P] [DecidableEq P]
    (A B : P → Matrix T T ℂ) :
    blocks A * blocks B = blocks (fun p => A p * B p) := by
  ext ⟨p,t⟩ ⟨q,u⟩
  by_cases same : p = q
  · subst q
    simp [blocks,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite]
  · simp [blocks,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,same]

omit [Fintype T] in
theorem blocks_one {P : Type} [DecidableEq P] :
    blocks (fun _ : P => (1 : Matrix T T ℂ)) = 1 := by
  ext ⟨p,t⟩ ⟨q,u⟩
  by_cases same : p = q <;> simp [blocks,Matrix.one_apply,Prod.ext_iff,same]

/-- One controlled power, acting on its explicit phase bit and on the same
whole target matrix as every other stage. -/
noncomputable def stage (width : Nat) (U : Matrix T T ℂ) (axis : Fin width) :
    Matrix ((Fin width → Bool) × T) ((Fin width → Bool) × T) ℂ :=
  blocks (fun bits => U^(if bits axis then 2^axis.val else 0))

theorem stage_fold (width : Nat) (U : Matrix T T ℂ) (axes : List (Fin width)) :
    axes.foldl (fun current axis => stage width U axis * current) 1 =
      blocks (fun bits => U^((axes.map (fun axis => if bits axis then 2^axis.val else 0)).sum)) := by
  classical
  induction axes using List.reverseRecOn with
  | nil => simp [blocks_one]
  | append_singleton axes axis ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    rw [ih]
    simp only [stage,blocks_mul,List.map_append,
      List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,add_zero]
    congr 1
    funext bits
    rw [← pow_add,Nat.add_comm]

/-- The ordered schedule uses exactly one controlled U^(2^k) for each bit k.
No exponentially expanded target matrix is needed by its structural checker. -/
theorem stage_schedule (width : Nat) (U : Matrix T T ℂ) :
    (List.finRange width).foldl (fun current axis => stage width U axis * current) 1 =
      powers width U := by
  rw [stage_fold]
  have count (bits : Fin width → Bool) :
      ((List.finRange width).map (fun axis => if bits axis then 2^axis.val else 0)).sum =
        HierarchicalGradient.number width bits := by
    rw [HierarchicalFourier.number_sum]
    simpa only [List.ofFn_eq_map] using (List.sum_ofFn (f := fun axis : Fin width => if bits axis then 2^axis.val else 0))
  simp only [count]
  rfl

/-- Time order is preparation, controlled powers, then inverse Fourier. -/
noncomputable def circuit (width : Nat)
    (preparation : Matrix (Fin width → Bool) (Fin width → Bool) ℂ)
    (U : Matrix T T ℂ) :
    Matrix ((Fin width → Bool) × T) ((Fin width → Bool) × T) ℂ :=
  onPhase (HierarchicalFourier.fourier width)ᴴ * powers width U * onPhase preparation

theorem circuit_coefficient (width : Nat)
    (preparation : Matrix (Fin width → Bool) (Fin width → Bool) ℂ)
    (U : Matrix T T ℂ) (outcome initial : Fin width → Bool) (output input : T) :
    circuit width preparation U (outcome,output) (initial,input) =
      ∑ control : Fin width → Bool,
        (star (HierarchicalFourier.fourier width control outcome) *
          preparation control initial) *
          (U ^ HierarchicalGradient.number width control) output input := by
  classical
  simp only [circuit,Matrix.mul_apply,Fintype.sum_prod_type,onPhase,powers,
    Matrix.conjTranspose_apply]
  simp only [Finset.sum_mul,ite_mul,mul_ite,zero_mul,mul_zero]
  simp [mul_comm,mul_left_comm]

theorem inverse_fourier_coefficient (width : Nat) (control outcome : Fin width → Bool) :
    star (HierarchicalFourier.fourier width control outcome) =
      Complex.exp (-2 * Real.pi * Complex.I *
        (HierarchicalGradient.number width control : ℂ) *
        (HierarchicalGradient.number width outcome : ℂ) / (2 : ℂ)^width) /
        (Real.sqrt ((2 : ℝ)^width) : ℂ) := by
  unfold HierarchicalFourier.fourier
  change (starRingEnd ℂ) (_ / _) = _
  simp only [map_div₀, ← Complex.exp_conj, map_mul, map_pow, Complex.conj_ofReal,
    Complex.conj_natCast, Complex.conj_I, map_ofNat]
  congr 2
  ring

/-- A full target branch of the composed circuit is the independently specified
Kraus operator. No eigenstate, exact eigenphase or provider-isometry premise is
needed for this equation; completeness has its separate isometry obligation. -/
theorem circuit_branch (width : Nat)
    (preparation : Matrix (Fin width → Bool) (Fin width → Bool) ℂ)
    (uniform : ∀ control, preparation control (fun _ => false) =
      Interference.complexModel.halfRoot^width)
    (U : Matrix T T ℂ) (outcome : Fin width → Bool) :
    (fun output input => circuit width preparation U (outcome,output) ((fun _ => false),input)) =
      Qpe.kraus width U (HierarchicalGradient.number width outcome) := by
  classical
  ext output input
  rw [circuit_coefficient]
  simp only [uniform,inverse_fourier_coefficient,mul_comm _ (Interference.complexModel.halfRoot^width),
    Qpe.preparation_readout_scale]
  unfold Qpe.kraus
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Fintype.sum_equiv (Qpe.bitEquiv width)
  intro control
  rw [Qpe.bitEquiv_value]
  rw [HierarchicalFourier.number_value]

end Qleisli.HierarchicalQpeCircuit
