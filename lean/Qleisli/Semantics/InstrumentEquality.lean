import Qleisli.Semantics.Instrument

/-! Independent finite instrument-equality mathematics for the adopted #46
design. No acceptance checker, source adapter or evidence producer is imported.
This reference is independent of executable comparison. Source preservation
and constitutional discharge remain separate obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.InstrumentEquality
open scoped BigOperators
open Qleisli.Semantics.Instrument

/-- Complete unnormalized CP map for one fixed public outcome. Hidden histories
are summed, so their labels and the particular Kraus decomposition are private. -/
noncomputable def channel {I O H R : Type} [Fintype I] [Fintype H] [Fintype R]
    [DecidableEq R] (operators : H → Matrix O I ℂ)
    (rho : Matrix (I × R) (I × R) ℂ) : Matrix (O × R) (O × R) ℂ :=
  ∑ h, density (operators h) rho

/-- Independently specified full Choi coefficients, including all coherences. -/
noncomputable def choi {I O H : Type} [Fintype H]
    (operators : H → Matrix O I ℂ) : Matrix (O × I) (O × I) ℂ :=
  fun left right => ∑ h, operators h left.1 left.2 * star (operators h right.1 right.2)

theorem density_entry {I O R : Type} [Fintype I] [Fintype R] [DecidableEq R]
    (operator : Matrix O I ℂ) (rho : Matrix (I × R) (I × R) ℂ)
    (o p : O) (r s : R) :
    density operator rho (o,r) (p,s) =
      ∑ i, ∑ j, operator o i * rho (i,r) (j,s) * star (operator p j) := by
  simp [density, withReference, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem channel_entry {I O H R : Type} [Fintype I] [Fintype H] [Fintype R]
    [DecidableEq R] (operators : H → Matrix O I ℂ)
    (rho : Matrix (I × R) (I × R) ℂ) (o p : O) (r s : R) :
    channel operators rho (o,r) (p,s) =
      ∑ i, ∑ j, choi operators (o,i) (p,j) * rho (i,r) (j,s) := by
  simp only [channel, Matrix.sum_apply, density_entry, choi, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h _
  exact mul_right_comm _ _ _

/-- Equality of complete coefficients implies equality on every joint input
matrix and arbitrary finite reference. No normalization, separability, density
positivity or equal hidden-history count is a premise. -/
theorem channel_eq_of_choi_eq {I O Left Right R : Type}
    [Fintype I] [Fintype Left] [Fintype Right] [Fintype R] [DecidableEq R]
    (implementation : Left → Matrix O I ℂ) (expected : Right → Matrix O I ℂ)
    (equal : choi implementation = choi expected)
    (rho : Matrix (I × R) (I × R) ℂ) :
    channel implementation rho = channel expected rho := by
  ext ⟨o,r⟩ ⟨p,s⟩
  simp only [channel_entry, equal]

/-- Public outcomes are compared separately, with their labels unchanged. This
is equality of a complete unnormalized instrument, not of a selected branch. -/
theorem instrument_eq_of_choi_eq {I O Left Right R Y : Type}
    [Fintype I] [Fintype Left] [Fintype Right] [Fintype R] [DecidableEq R]
    (implementation : Y → Left → Matrix O I ℂ)
    (expected : Y → Right → Matrix O I ℂ)
    (equal : ∀ outcome, choi (implementation outcome) = choi (expected outcome))
    (rho : Matrix (I × R) (I × R) ℂ) :
    (fun outcome => channel (implementation outcome) rho) =
      (fun outcome => channel (expected outcome) rho) := by
  funext outcome
  exact channel_eq_of_choi_eq _ _ (equal outcome) rho

end Qleisli.Semantics.InstrumentEquality
