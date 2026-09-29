import Qleisli.QpeComplete
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-! Coherent operator meaning of the actual executable controlled-power action.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The provider premise and external IR/evidence binding remain explicit. -/

namespace Qleisli.ControlledPowers
open scoped BigOperators Matrix

variable {B T : Type} [Fintype B] [DecidableEq B] [Fintype T] [DecidableEq T]

/-- Preserve the control basis coherently; no outcome or dephasing map occurs. -/
noncomputable def block (operators : B → Matrix T T ℂ) : Matrix (B × T) (B × T) ℂ :=
  fun output input => if output.1 = input.1 then operators output.1 output.2 input.2 else 0

omit [DecidableEq T] in
theorem block_mul (left right : B → Matrix T T ℂ) :
    block (fun b => left b * right b) = block left * block right := by
  ext ⟨b,i⟩ ⟨c,j⟩
  by_cases same : b = c
  · subst c
    simp [block, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [block, Matrix.mul_apply, Fintype.sum_prod_type, same]

omit [Fintype B] [Fintype T] [DecidableEq T] in
theorem block_conj (operators : B → Matrix T T ℂ) :
    block (fun b => (operators b)ᴴ) = (block operators)ᴴ := by
  ext ⟨b,i⟩ ⟨c,j⟩
  by_cases same : b = c
  · subst c; simp [block, Matrix.conjTranspose_apply]
  · simp [block, Matrix.conjTranspose_apply, same, Ne.symm same]

omit [Fintype B] [Fintype T] in
theorem block_one : block (fun _ : B => (1 : Matrix T T ℂ)) = 1 := by
  ext ⟨b,i⟩ ⟨c,j⟩
  by_cases same : b = c <;> simp [block, Matrix.one_apply, Prod.ext_iff, same]

omit [DecidableEq T] in
theorem block_mulVec (operators : B → Matrix T T ℂ) (amplitude : B × T → ℂ) (b : B) (i : T) :
    (block operators *ᵥ amplitude) (b,i) = (operators b *ᵥ (fun j => amplitude (b,j))) i := by
  simp [block, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem block_isometry (operators : B → Matrix T T ℂ)
    (isometries : ∀ b, (operators b)ᴴ * operators b = 1) :
    (block operators)ᴴ * block operators = 1 := by
  rw [← block_conj, ← block_mul]
  simpa only [isometries] using (block_one (B := B) (T := T))

/-- Actual literal iteration on amplitudes agrees with matrix powers. -/
theorem iterate_mulVec (U : Matrix T T ℂ) (count : Nat) (amplitude : T → ℂ) :
    QleisliKernel.ControlledPowers.iterate (fun v => U *ᵥ v) count amplitude = U^count *ᵥ amplitude := by
  induction count with
  | zero => simp [QleisliKernel.ControlledPowers.iterate]
  | succ count ih =>
    change U *ᵥ QleisliKernel.ControlledPowers.iterate (fun v => U *ᵥ v) count amplitude = _
    rw [ih, Matrix.mulVec_mulVec, pow_succ']

/-- Each block is obtained from the actual executable stage, not its request. -/
noncomputable def singleOperator (operations : Nat → Matrix T T ℂ)
    (stage : QleisliKernel.ControlledPowers.Stage) : Matrix (Bool × T) (Bool × T) ℂ :=
  block fun b => QleisliKernel.ControlledPowers.applyStage (fun provider A => operations provider * A)
    (fun axis => axis == 0 && b) 1 stage

noncomputable def controlled (U : Matrix T T ℂ) : Matrix (Bool × T) (Bool × T) ℂ :=
  block fun b => if b then U else 1

theorem checked_single_operator (operations : Nat → Matrix T T ℂ) (exponent provider : Nat)
    (stage : QleisliKernel.ControlledPowers.Stage)
    (accepted : QleisliKernel.ControlledPowers.checkSingle exponent provider stage = true) :
    singleOperator operations stage = controlled ((operations provider)^(2^exponent)) := by
  unfold singleOperator controlled
  congr 1
  funext b
  rw [QleisliKernel.ControlledPowers.checkSingle_action _ exponent provider stage accepted]
  simp [Qpe.iterate_left_mul]

/-- Arbitrary joint amplitudes, not just basis states or a fixed control bit. -/
theorem checked_single_native (operations : Nat → Matrix T T ℂ) (exponent provider : Nat)
    (stage : QleisliKernel.ControlledPowers.Stage)
    (accepted : QleisliKernel.ControlledPowers.checkSingle exponent provider stage = true)
    (amplitude : Bool × T → ℂ) (b : Bool) (i : T) :
    QleisliKernel.ControlledPowers.coherentStage (fun p v => operations p *ᵥ v)
      (fun bit axis => axis == 0 && bit) (fun bit j => amplitude (bit,j)) stage b i =
      (singleOperator operations stage *ᵥ amplitude) (b,i) := by
  rw [checked_single_operator operations exponent provider stage accepted]
  rw [controlled, block_mulVec]
  unfold QleisliKernel.ControlledPowers.coherentStage
  rw [QleisliKernel.ControlledPowers.checkSingle_action _ exponent provider stage accepted]
  cases b <;> simp [iterate_mulVec]

theorem checked_single_isometry (operations : Nat → Matrix T T ℂ) (exponent provider : Nat)
    (stage : QleisliKernel.ControlledPowers.Stage)
    (accepted : QleisliKernel.ControlledPowers.checkSingle exponent provider stage = true)
    (providerIsometry : (operations provider)ᴴ * operations provider = 1) :
    (singleOperator operations stage)ᴴ * singleOperator operations stage = 1 := by
  rw [checked_single_operator operations exponent provider stage accepted]
  apply block_isometry
  intro b
  cases b
  · simp
  · exact Qpe.power_isometry _ providerIsometry _

theorem checked_single_unitary (operations : Nat → Matrix T T ℂ) (exponent provider : Nat)
    (stage : QleisliKernel.ControlledPowers.Stage)
    (accepted : QleisliKernel.ControlledPowers.checkSingle exponent provider stage = true)
    (providerIsometry : (operations provider)ᴴ * operations provider = 1) :
    (singleOperator operations stage)ᴴ * singleOperator operations stage = 1 ∧
    singleOperator operations stage * (singleOperator operations stage)ᴴ = 1 := by
  have h := checked_single_isometry operations exponent provider stage accepted providerIsometry
  exact ⟨h, mul_eq_one_comm.mp h⟩

/-- The complete schedule also retains coherences between every control word. -/
noncomputable def scheduleOperator (operations : Nat → Matrix T T ℂ)
    (controls : B → QleisliKernel.Interference.Bits) (stages : List QleisliKernel.ControlledPowers.Stage) :
    Matrix (B × T) (B × T) ℂ :=
  block fun b => QleisliKernel.ControlledPowers.run (fun provider A => operations provider * A) (controls b) stages 1

omit [Fintype B] in
theorem checked_schedule_operator (operations : Nat → Matrix T T ℂ)
    (controls : B → QleisliKernel.Interference.Bits) (width provider : Nat)
    (stages : List QleisliKernel.ControlledPowers.Stage)
    (accepted : QleisliKernel.ControlledPowers.check width provider stages = true) :
    scheduleOperator operations controls stages =
      block (fun b => (operations provider)^(QleisliKernel.ControlledPowers.value width (controls b))) := by
  unfold scheduleOperator
  congr 1
  funext b
  rw [QleisliKernel.ControlledPowers.check_action _ width provider stages accepted, Qpe.iterate_left_mul,
    Matrix.mul_one]

theorem checked_schedule_native (operations : Nat → Matrix T T ℂ)
    (controls : B → QleisliKernel.Interference.Bits) (width provider : Nat)
    (stages : List QleisliKernel.ControlledPowers.Stage)
    (accepted : QleisliKernel.ControlledPowers.check width provider stages = true)
    (amplitude : B × T → ℂ) (b : B) (i : T) :
    QleisliKernel.ControlledPowers.coherentRun (fun p v => operations p *ᵥ v) controls stages
      (fun control j => amplitude (control,j)) b i =
      (scheduleOperator operations controls stages *ᵥ amplitude) (b,i) := by
  rw [checked_schedule_operator operations controls width provider stages accepted, block_mulVec,
    QleisliKernel.ControlledPowers.coherentRun_apply, QleisliKernel.ControlledPowers.check_action _ width provider stages accepted,
    iterate_mulVec]

theorem checked_schedule_isometry (operations : Nat → Matrix T T ℂ)
    (controls : B → QleisliKernel.Interference.Bits) (width provider : Nat)
    (stages : List QleisliKernel.ControlledPowers.Stage)
    (accepted : QleisliKernel.ControlledPowers.check width provider stages = true)
    (providerIsometry : (operations provider)ᴴ * operations provider = 1) :
    (scheduleOperator operations controls stages)ᴴ * scheduleOperator operations controls stages = 1 := by
  rw [checked_schedule_operator operations controls width provider stages accepted]
  exact block_isometry _ (fun _ => Qpe.power_isometry _ providerIsometry _)

variable {R : Type} [Fintype R] [DecidableEq R]

/-- Equality of the entire reference-extended action, including off-diagonal
control coherences. No normalization, eigenstate or separability premise. -/
theorem checked_single_reference (operations : Nat → Matrix T T ℂ) (exponent provider : Nat)
    (stage : QleisliKernel.ControlledPowers.Stage)
    (accepted : QleisliKernel.ControlledPowers.checkSingle exponent provider stage = true)
    (rho : Matrix ((Bool × T) × R) ((Bool × T) × R) ℂ) :
    Qpe.outcomeMap (singleOperator operations stage) rho =
      Qpe.outcomeMap (controlled ((operations provider)^(2^exponent))) rho := by
  rw [checked_single_operator operations exponent provider stage accepted]

end Qleisli.ControlledPowers
