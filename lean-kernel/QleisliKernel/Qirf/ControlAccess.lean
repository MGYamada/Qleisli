import QleisliKernel.Qirf.Contract
import QleisliKernel.Semantics.ControlAccess

/-! Internal bounded control-sector obligation for the original QIRF root.
No protocol/CLI/source access path is added by this component. Its caller must
still establish original source places, lifetimes, locality and resource links.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.ControlAccess
open Semantics.Exact Semantics.Finite Semantics.ControlAccess Finite

def sectors (matrix : Matrix) (axes : List Nat) : Bool :=
  (List.range matrix.rows).all fun row =>
    (List.range matrix.cols).all fun col =>
      (gather row axes == gather col axes) || decide (Zero (matrix.entry row col))

theorem sectors_sound (matrix : Matrix) (axes : List Nat)
    (ok : sectors matrix axes = true) : PreservesSectors matrix axes := by
  simp only [sectors, List.all_eq_true] at ok
  intro row hr col hc different
  have result := ok row hr col hc
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at result
  exact result.resolve_left different

/-- Validate the finite coordinate domain before charging and traversing it.
Missing entries cannot masquerade as zeros; axes are original, unique and in range. -/
def checkMatrix (bits : Nat) (matrix : Matrix) (axes : List Nat) : WorkM Unit := do
  guard (bits ≤ 6 && matrix.rows == 2^bits && matrix.cols == 2^bits &&
    matrix.entries.length == matrix.rows * matrix.cols) .limit
  guard (axesValid bits axes) .request
  exactWork (Exact.charge (matrix.rows * matrix.cols * (axes.length + 4)))
  guard (sectors matrix axes) .equation

/-- A matrix supplied by the producer is never substituted for reconstruction.
Fresh graph/root acceptance, exact tree identity and actual dependencies precede
unitarity and the requested sector obligation. The finite profile remains six bits. -/
def check (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (axes : List Nat) : WorkM Matrix := do
  let root ← Validity.checkRoot artifact order
  guard (artifact.rootInterface == some (signature,signature)) .request
  guard (Raw.BranchFunction.preflight signature root.program) .limit
  let actual ← Raw.BranchFunction.reconstruct root.dependencies root.program
  wholeSpace actual
  checkMatrix (width signature) actual axes
  return actual

theorem checkMatrix_sectors (bits : Nat) (matrix : Matrix) (axes : List Nat)
    (work left : Nat) (ok : (checkMatrix bits matrix axes).run work = (.ok (),left)) :
    PreservesSectors matrix axes := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  exact sectors_sound matrix axes (guard_success _ _ _ _ h).1

/-- Bind this condition to the same actual root and matrix, not an unrelated
accepted handle or a theorem about a desired replacement operator. -/
theorem check_bound (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (axes : List Nat) (actual : Matrix) (work left : Nat)
    (ok : (check artifact order signature axes).run work = (.ok actual,left)) :
    ∃ root a b c,
      (Validity.checkRoot artifact order).run work = (.ok root,a) ∧
      artifact.rootInterface = some (signature,signature) ∧
      Raw.BranchFunction.preflight signature root.program = true ∧
      (Raw.BranchFunction.reconstruct root.dependencies root.program).run a = (.ok actual,b) ∧
      (wholeSpace actual).run b = (.ok (),c) ∧
      (checkMatrix (width signature) actual axes).run c = (.ok (),left) ∧
      PreservesSectors actual axes := by
  obtain ⟨root,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,a₁,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨interface,same₁⟩ := guard_success _ _ _ _ hi
  subst a₁
  obtain ⟨_,a₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨preflight,same₂⟩ := guard_success _ _ _ _ hp
  subst a₂
  obtain ⟨matrix,b,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,c,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨value,same⟩ := pure_success _ _ _ _ h
  subst actual
  subst d
  exact ⟨root,a,b,c,hr,beq_iff_eq.mp interface,preflight,hm,hu,hs,
    checkMatrix_sectors _ _ _ _ _ hs⟩

end QleisliKernel.Qirf.ControlAccess
