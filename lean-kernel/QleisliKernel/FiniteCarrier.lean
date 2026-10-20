import QleisliKernel.Semantics.FiniteCarrier
import QleisliKernel.Finite

/-! Bounded finite-carrier reading for #64. Reuse the existing exact arithmetic,
work accounting and matrix/isometry checks. This component is not connected to
the native protocol and issues no accepted handle. Original-body/dependency,
typed-port/effect and source integration are still required.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.FiniteCarrier
open Semantics.FiniteCarrier Semantics.Exact Finite

def originBytes (origin : Origin) : Nat :=
  origin.moduleName.utf8ByteSize + origin.declarationName.utf8ByteSize + origin.source.utf8ByteSize

def originValid (origin : Origin) : Bool :=
  !origin.moduleName.isEmpty && !origin.declarationName.isEmpty &&
    origin.moduleName.utf8ByteSize ≤ 4096 && origin.declarationName.utf8ByteSize ≤ 4096

def namesValid (names : List String) : Bool :=
  names.all (fun name => !name.isEmpty && name.utf8ByteSize ≤ 4096) &&
    names.eraseDups.length == names.length

/-- Prefix shape is checked before code enumeration. Depth/node/width bounds
remain the existing finite-contract profile, including zero-width nodes. -/
def treeStep (stack : Option (List Nat)) (atom : Atom) : Option (List Nat) := do
  let depth :: rest ← stack | none
  if depth > 32 then none else
  match children atom with
  | none => some rest
  | some arity =>
    if arity > 128 then none
    else some (List.replicate arity (depth+1) ++ rest)

def nodeRead (totals : Nat × Nat) (atom : Atom) : WorkM (Nat × Nat) := do
  let (bits,bytes) ← match atom with
    | .bits width =>
      guard (width ≤ 6) .limit
      pure (width,0)
    | .bit => pure (1,0)
    | .tuple arity =>
      guard (3 ≤ arity && arity ≤ 128)
      pure (0,0)
    | .enumeration origin names | .record origin names => do
      guard (names.length ≤ 128) .limit
      let bytes := originBytes origin + (names.map String.utf8ByteSize).sum
      guard (totals.2 + bytes ≤ 1048576) .limit
      -- Charge complete comparisons before duplicate detection/string traversal.
      exactWork (Exact.charge (bytes * (names.length+1) + 1))
      guard (originValid origin && namesValid names)
      match atom with
      | .enumeration _ _ =>
        guard (!names.isEmpty && names.length ≤ 64)
        pure (tagBits names.length,bytes)
      | _ => pure (0,bytes)
    | _ => pure (0,0)
  guard (totals.1 + bits ≤ 6) .limit
  return (totals.1+bits,totals.2+bytes)

/-- Actual accepted reader result equals the independent prefix interpretation.
No power-of-two logical dimension is inferred from its physical width. -/
def read (basis : Basis) : WorkM Layout := do
  guard (basis.length ≤ 128) .limit
  exactWork (Exact.charge (basis.length * 128 + 1))
  guard (basis.foldl treeStep (some [0]) == some [])
  let _ ← basis.foldlM nodeRead (0,0)
  lift (readOption (layout basis))

def code (basis : Basis) : WorkM Matrix := do
  let result ← read basis
  let matrix ← matrixRead (encoding result)
  let isometry ← exactWork (Exact.Matrix.isometryWork matrix)
  guard isometry .notIsometric
  return matrix

theorem read_reference (basis : Basis) (result : Layout) (work left : Nat)
    (ok : (read basis).run work = (.ok result,left)) : layout basis = some result := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,_,h⟩ := bind_success _ _ _ _ _ h
  have selected := (lift_success _ _ _ _ h).1
  cases source : layout basis <;> simp_all [readOption]

theorem code_conditions (basis : Basis) (matrix : Matrix) (work left : Nat)
    (ok : (code basis).run work = (.ok matrix,left)) :
    ∃ result before after,
      layout basis = some result ∧ matrix = encoding result ∧
      Exact.Matrix.isometry matrix before = (.ok true,after) := by
  obtain ⟨result,w₁,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨readMatrix,w₂,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨iso,w₃,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hg,h⟩ := bind_success _ _ _ _ _ h
  have matrix_eq := (matrixRead_value _ _ _ _ hm).1
  subst readMatrix
  have iso_true := (guard_success _ _ _ _ hg).1
  subst iso
  have same := (pure_success _ _ _ _ h).1
  subst matrix
  exact ⟨result,w₂,w₃,read_reference _ _ _ _ hr,rfl,exactWork_success _ _ _ _ hi⟩

end QleisliKernel.FiniteCarrier
