import QleisliKernel.Semantics.Protected
import Qleisli.Semantics.Finite
import Mathlib.Data.Nat.Bitwise

/-! Non-dense complex semantics of original protected compute/use/uncompute.
Source, auxiliary and target coordinates stay separate. Arbitrary reference
coordinates allow correlated inputs. No checker, capacity or receipt is imported.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Semantics.Protected
open QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Protected Qleisli.Semantics.Finite

abbrev Logical (R : Type) := Nat → Nat → R → ℂ
abbrev Physical (R : Type) := Nat → Nat → Nat → R → ℂ

noncomputable def zero {R : Type} (ψ : Logical R) : Physical R :=
  fun source ancilla target reference => if ancilla = 0 then ψ source target reference else 0

/-- Literal reversible XOR computation, with no truth-table expansion. -/
noncomputable def compute {R : Type} (function : Nat → Nat) (ψ : Physical R) : Physical R :=
  fun source ancilla target reference => ψ source (ancilla ^^^ function source) target reference

noncomputable def gate (operation : Gate) (axis : Nat) (ψ : Nat → ℂ) (label : Nat) : ℂ :=
  match operation with
  | .x => ψ (label ^^^ 2^axis)
  | .z => ψ label * (if bit label axis == 1 then phase 4 else 1)
  | .t => ψ label * (if bit label axis == 1 then phase 1 else 1)
  | .h =>
    let low := label - bit label axis * 2^axis
    (ψ low + (if bit label axis == 1 then -ψ (low+2^axis) else ψ (low+2^axis))) * halfRoot

/-- Actual original use, including invalid source/auxiliary X/H actions. The
clean-return proof must establish the checker excludes those actions. -/
noncomputable def physicalUse {R : Type} (use : Use) (ψ : Physical R) : Physical R :=
  fun source ancilla target reference => match use with
  | .protectedGate location operation =>
    match location.region with
    | .source => gate operation location.index (fun label => ψ label ancilla target reference) source
    | .ancilla => gate operation location.index (fun label => ψ source label target reference) ancilla
  | .targetGate controls targetAxis operation =>
    if enabled source ancilla controls then gate operation targetAxis (fun label => ψ source ancilla label reference) target
    else ψ source ancilla target reference
  | .phase controls operation => ψ source ancilla target reference *
    (if enabled source ancilla controls then phase (phaseExponent operation) else 1)

noncomputable def blockUse {R : Type} (source ancilla : Nat) (use : Use)
    (ψ : Nat → R → ℂ) : Nat → R → ℂ :=
  fun target reference => match use with
  | .protectedGate location operation => ψ target reference *
    (if value source ancilla location then phase (if operation == .z then 4 else 1) else 1)
  | .targetGate controls targetAxis operation =>
    if enabled source ancilla controls then gate operation targetAxis (fun label => ψ label reference) target
    else ψ target reference
  | .phase controls operation => ψ target reference *
    (if enabled source ancilla controls then phase (phaseExponent operation) else 1)

noncomputable def run {R : Type} (uses : List Use) (ψ : Physical R) : Physical R :=
  uses.foldl (fun ψ use => physicalUse use ψ) ψ

noncomputable def blocks {R : Type} (source ancilla : Nat) (uses : List Use)
    (ψ : Nat → R → ℂ) : Nat → R → ℂ :=
  uses.foldl (fun ψ use => blockUse source ancilla use ψ) ψ

noncomputable def logical {R : Type} (function : Nat → Nat) (uses : List Use) (ψ : Logical R) : Logical R :=
  fun source => blocks source (function source) uses (ψ source)

def DiagonalProtected : Use → Prop
  | .protectedGate _ operation => operation = .z ∨ operation = .t
  | _ => True

theorem gate_zero (operation : Gate) (axis label : Nat) : gate operation axis (fun _ => 0) label = 0 := by
  cases operation <;> simp [gate]

theorem blockUse_zero {R : Type} (source ancilla : Nat) (use : Use) :
    blockUse (R := R) source ancilla use (fun _ _ => 0) = fun _ _ => 0 := by
  funext target reference
  cases use <;> simp [blockUse,gate_zero]

theorem blocks_zero {R : Type} (source ancilla : Nat) (uses : List Use) :
    blocks (R := R) source ancilla uses (fun _ _ => 0) = fun _ _ => 0 := by
  induction uses with
  | nil => rfl
  | cons use uses ih => simpa [blocks,List.foldl_cons,blockUse_zero] using ih

theorem physicalUse_block {R : Type} (use : Use) (valid : DiagonalProtected use) (ψ : Physical R)
    (source ancilla : Nat) :
    physicalUse use ψ source ancilla = blockUse source ancilla use (ψ source ancilla) := by
  funext target reference
  cases use with
  | protectedGate location operation =>
    rcases location with ⟨region,index⟩
    rcases valid with rfl | rfl <;> cases region <;> simp [physicalUse,blockUse,gate,value]
  | targetGate controls axis operation => rfl
  | phase controls operation => rfl

theorem run_blocks {R : Type} (uses : List Use) (valid : ∀ use ∈ uses, DiagonalProtected use)
    (ψ : Physical R) (source ancilla : Nat) :
    run uses ψ source ancilla = blocks source ancilla uses (ψ source ancilla) := by
  induction uses generalizing ψ with
  | nil => rfl
  | cons use uses ih =>
    rw [run,List.foldl_cons]
    rw [← run,ih (fun use hu => valid use (List.mem_cons_of_mem _ hu))]
    rw [physicalUse_block use (valid use (by simp))]
    rfl

/-- Exact factorization on every source/target/reference amplitude. No product
state premise, global matrix, maximum width or post-discard equality is used. -/
theorem clean_factorization {R : Type} (function : Nat → Nat) (uses : List Use)
    (valid : ∀ use ∈ uses, DiagonalProtected use) (ψ : Logical R) :
    compute function (run uses (compute function (zero ψ))) = zero (logical function uses ψ) := by
  funext source ancilla target reference
  change run uses (compute function (zero ψ)) source (ancilla ^^^ function source) target reference = _
  rw [run_blocks uses valid]
  have supported : compute function (zero ψ) source (ancilla ^^^ function source) =
      fun target reference => if ancilla = 0 then ψ source target reference else 0 := by
    funext target reference
    simp only [compute,zero,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  rw [supported]
  by_cases clean : ancilla = 0
  · subst ancilla
    simp [zero,logical]
  · simp only [if_neg clean,blocks_zero,zero]

theorem clean_dirty {R : Type} (function : Nat → Nat) (uses : List Use)
    (valid : ∀ use ∈ uses, DiagonalProtected use) (ψ : Logical R)
    (source ancilla target : Nat) (reference : R) (dirty : ancilla ≠ 0) :
    compute function (run uses (compute function (zero ψ))) source ancilla target reference = 0 := by
  rw [clean_factorization function uses valid ψ]
  simp [zero,dirty]

end Qleisli.Semantics.Protected
