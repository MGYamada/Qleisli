import QleisliKernel.Finite

/-! Exact independent-request equality at the VM-27 boundary.
The decoder is an unproved adapter; this decision uses actual exact matrices.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Hierarchical.FiniteBinding
open Semantics.Exact

/-- Charge comparison under the same budget as decoding and leaf checking. -/
def check (actual required : Matrix) (remaining : Nat) : Except Finite.Error Nat :=
  if remaining > 10000000 || actual.entries.length > remaining then .error .limit
  else if actual == required then .ok (remaining - actual.entries.length)
  else .error .equation

theorem check_conditions (actual required : Matrix) (remaining left : Nat)
    (accepted : check actual required remaining = .ok left) :
    actual = required ∧ remaining ≤ 10000000 ∧
      actual.entries.length ≤ remaining ∧ left = remaining - actual.entries.length := by
  unfold check at accepted
  split at accepted
  next exceeded => contradiction
  next bounded =>
    split at accepted
    next equal =>
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at bounded
      exact ⟨by simpa using equal, Nat.le_of_not_gt bounded.1,
        Nat.le_of_not_gt bounded.2, (Except.ok.inj accepted).symm⟩
    next different => contradiction

end QleisliKernel.Hierarchical.FiniteBinding
