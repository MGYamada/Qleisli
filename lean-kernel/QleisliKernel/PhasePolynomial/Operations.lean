import QleisliKernel.PhasePolynomial

/-! Sparse phase scaling and coherent positive controls.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
These total operations issue no acceptance evidence. Callers must validate
axis scopes, ownership and budgets before admitting their results. -/

namespace QleisliKernel.PhasePolynomial

/-- Repeated diagonal composition scales coefficients, never the body size. -/
def scale (count : Nat) (terms : Polynomial) : Polynomial :=
  terms.map (fun term => ⟨term.axes,(term.ticks * count) % modulus⟩)

/-- Only a true control is represented here. Routing/scoping must establish
that this is a separate control axis before an enclosing checker accepts it. -/
def controlTrue (axis : Nat) (terms : Polynomial) : Polynomial :=
  terms.map (fun term => ⟨(axis :: term.axes).mergeSort (· ≤ ·),term.ticks⟩)

theorem scale_length (count : Nat) (terms : Polynomial) :
    (scale count terms).length = terms.length := by simp [scale]

theorem controlTrue_length (axis : Nat) (terms : Polynomial) :
    (controlTrue axis terms).length = terms.length := by simp [controlTrue]

theorem scale_sound (count : Nat) (terms : Polynomial) (bits : Nat → Bool) :
    evaluate (scale count terms) bits = (evaluate terms bits * count) % modulus := by
  induction terms with
  | nil => simp [scale,evaluate]
  | cons term rest ih =>
    simp only [scale,List.map_cons,evaluate_cons] at *
    rw [ih]
    simp only [Term.value]
    split <;> simp [Nat.add_mul]

theorem controlTrue_sound (axis : Nat) (terms : Polynomial) (bits : Nat → Bool) :
    evaluate (controlTrue axis terms) bits = if bits axis then evaluate terms bits else 0 := by
  unfold controlTrue evaluate
  simp only [List.map_map,Function.comp_def]
  have term (t : Term) :
      Term.value ⟨(axis :: t.axes).mergeSort (· ≤ ·),t.ticks⟩ bits =
        if bits axis then t.value bits else 0 := by
    simp only [Term.value,(List.mergeSort_perm _ _).all_eq,List.all_cons]
    cases bits axis <;> simp
  simp only [term]
  cases bits axis with
  | true => simp
  | false =>
    have zero : (terms.map (fun _ => (0 : Nat))).sum = 0 := by
      induction terms <;> simp_all
    simpa using congrArg (fun n => n % modulus) zero

end QleisliKernel.PhasePolynomial
