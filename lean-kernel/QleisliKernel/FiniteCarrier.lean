import QleisliKernel.Semantics.FiniteCarrier
import QleisliKernel.Finite
import QleisliKernel.ExactSparse

/-! Bounded finite-carrier reading for #64. Reuse the existing exact arithmetic,
work accounting and matrix/isometry checks. Qirf.Carrier and Protocol.Carrier
connect this reader to the actual body, dependencies, typed ports and original
declarations. This reader alone grants no native decision or source preservation.
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

/-- A layout encoding has at most one nonzero entry per column. Its adjoint
has at most one term per Gram row. The estimate only selects the strategy;
both checks read the same admitted matrix and charge their actual work. -/
private def preferSparseCodeGram (matrix : Matrix) : Bool :=
  let area := matrix.rows * matrix.cols
  6*area + matrix.cols + 5*matrix.cols*matrix.cols < area + 2*area*matrix.cols

def code (basis : Basis) : WorkM Matrix := do
  let result ← read basis
  let matrix ← matrixRead (encoding result)
  let isometry ← exactWork (if preferSparseCodeGram matrix then
    Exact.Matrix.sparseIsometryWork matrix else Exact.Matrix.isometryWork matrix)
  guard isometry .notIsometric
  return matrix

inductive CodeSide where
  | left | right

private def compactProductCost (side : CodeSide) (x y : Matrix) : Nat :=
  let common := x.rows*x.cols + y.rows*y.cols + 3*x.rows*y.cols
  match side with
  | .left => common + x.rows*(2*x.cols+1) + 2*(max x.rows x.cols)*y.cols + 4*y.rows*y.cols
  | .right => common + y.cols*(2*y.rows+1) + 2*(max y.rows y.cols)*x.rows + 4*x.rows*x.cols

/-- A decision about one actual code matrix, retained across all products
that use that operand. -/
inductive CodePlan (matrix : Matrix) where
  | compact
  | identity (square : matrix.rows = matrix.cols)
      (exactIdentity : Exact.Matrix.identity matrix.rows = .ok matrix)
  | select (support : Exact.Matrix.SingleEntrySupports matrix)

private def inspectIdentity (matrix : Matrix) : WorkM (CodePlan matrix) := do
  if square : matrix.rows = matrix.cols then
    if 8 ≤ matrix.rows && Exact.matrixValid matrix.rows matrix.cols then
      exactWork (Exact.charge (4*matrix.rows*matrix.cols + 1))
      match made : Exact.Matrix.identity matrix.rows with
      | .ok identity =>
        if same : identity = matrix then
          return .identity square (made.trans (congrArg Except.ok same))
        else return .compact
      | .error _ => return .compact
    else return .compact
  else return .compact

/-- Check reusable row and column selections against the literal operand.
Each candidate is bounded before inspecting any coefficients. -/
def prepareCode (matrix : Matrix) : WorkM (CodePlan matrix) := do
  match ← inspectIdentity matrix with
  | .compact =>
    if 8 ≤ max matrix.rows matrix.cols then
      let supports ← exactWork (Exact.Matrix.readSingleEntrySupports matrix)
      return (supports.map CodePlan.select).getD .compact
    else return .compact
  | plan => return plan

structure CodePlans (input output : Matrix) where
  inputPlan : Option (CodePlan input) := none
  outputPlan : Option (CodePlan output) := none

def prepareCodes (input output : Matrix) : WorkM (CodePlans input output) := do
  let inputPlan ← prepareCode input
  let outputPlan ← prepareCode output
  return ⟨some inputPlan,some outputPlan⟩

def CodeSide.operand (side : CodeSide) (x y : Matrix) : Matrix :=
  match side with | .left => x | .right => y

def CodeSide.otherOperand (side : CodeSide) (x y : Matrix) : Matrix :=
  match side with | .left => y | .right => x

inductive OperandAdmission (matrix : Matrix) where
  | fresh
  | checked (admitted : Exact.Matrix.Admitted matrix)

private def readOperand (matrix : Matrix) : OperandAdmission matrix → WorkM Matrix
  | .fresh => matrixRead matrix
  | .checked _ => pure matrix

private theorem readOperand_bound (matrix result : Matrix) (admission : OperandAdmission matrix)
    (work left : Nat) (ran : (readOperand matrix admission).run work = (.ok result,left)) :
    result = matrix ∧ Exact.Matrix.Admitted result := by
  cases admission with
  | fresh => exact ⟨(matrixRead_value _ _ _ _ ran).1,matrixRead_admitted _ _ _ _ ran⟩
  | checked admitted =>
    have same := (pure_success _ _ _ _ ran).1
    subst result
    exact ⟨rfl,admitted⟩

private def usePlan {matrix : Matrix} : Option (CodePlan matrix) → WorkM (CodePlan matrix)
  | none => inspectIdentity matrix
  | some plan => pure plan

/-- The estimate selects the cost strategy only. A retained plan refers to
the literal operand used here. Compact support still comes from that matrix. -/
def codeProductWithAdmission (side : CodeSide) (x y : Matrix)
    (plan : Option (CodePlan (side.operand x y)))
    (admission : OperandAdmission (side.otherOperand x y)) : WorkM Matrix := do
  if x.cols == y.rows && compactProductCost side x y < 2*x.rows*x.cols*y.cols then
    match side,plan,admission with
    | .left,plan,admission =>
      let admitted ← readOperand y admission
      match ← usePlan plan with
      | .identity .. => pure admitted
      | .select support => exactWork (Exact.Matrix.composeSingleLeftWork x admitted support.rows)
      | .compact => exactWork (Exact.Matrix.composeSparseLeftWork x admitted)
    | .right,plan,admission =>
      let admitted ← readOperand x admission
      match ← usePlan plan with
      | .identity .. => pure admitted
      | .select support => exactWork (Exact.Matrix.composeSingleRightWork admitted y support.columns)
      | .compact => exactWork (Exact.Matrix.composeSparseRightWork admitted y)
  else exactWork (Exact.Matrix.composeWork x y)

def codeProductUsing (side : CodeSide) (x y : Matrix)
    (plan : Option (CodePlan (side.operand x y))) : WorkM Matrix :=
  codeProductWithAdmission side x y plan .fresh

def codeProduct (side : CodeSide) (x y : Matrix) : WorkM Matrix :=
  codeProductUsing side x y none

theorem codeProductWithAdmission_dense (side : CodeSide) (x y result : Matrix)
    (plan : Option (CodePlan (side.operand x y)))
    (admission : OperandAdmission (side.otherOperand x y)) (work left : Nat)
    (ok : (codeProductWithAdmission side x y plan admission).run work = (.ok result,left)) :
    ∃ before after, Exact.Matrix.compose x y before = (.ok result,after) := by
  unfold codeProductWithAdmission at ok
  split at ok
  · rename_i compact
    simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at compact
    cases side
    · obtain ⟨input,middle,read,computed⟩ := bind_success _ _ _ _ _ ok
      obtain ⟨same,admitted⟩ := readOperand_bound _ _ admission _ _ read
      subst input
      obtain ⟨decision,after,_,computed⟩ := bind_success _ _ _ _ _ computed
      cases decision with
      | compact => exact ⟨_,0,Exact.Matrix.composeSparseLeft_success x y result admitted after left
          (exactWork_success _ _ _ _ computed)⟩
      | select support => exact ⟨_,0,Exact.Matrix.composeSingleLeft_success x y result admitted
          support.rows after left (exactWork_success _ _ _ _ computed)⟩
      | identity square literal =>
        have returned := (pure_success _ _ _ _ computed).1
        subst result
        change x.rows = x.cols at square
        change Exact.Matrix.identity x.rows = .ok x at literal
        rw [square,compact.1] at literal
        exact ⟨_,0,Exact.Matrix.compose_identity_left x y admitted literal⟩
    · obtain ⟨input,middle,read,computed⟩ := bind_success _ _ _ _ _ ok
      obtain ⟨same,admitted⟩ := readOperand_bound _ _ admission _ _ read
      subst input
      obtain ⟨decision,after,_,computed⟩ := bind_success _ _ _ _ _ computed
      cases decision with
      | compact => exact ⟨_,0,Exact.Matrix.composeSparseRight_success x y result admitted after left
          (exactWork_success _ _ _ _ computed)⟩
      | select support => exact ⟨_,0,Exact.Matrix.composeSingleRight_success x y result admitted
          support.columns after left (exactWork_success _ _ _ _ computed)⟩
      | identity _ literal =>
        have returned := (pure_success _ _ _ _ computed).1
        subst result
        change Exact.Matrix.identity y.rows = .ok y at literal
        rw [← compact.1] at literal
        exact ⟨_,0,Exact.Matrix.compose_identity_right x y admitted literal⟩
  · exact ⟨work,left,exactWork_success _ _ _ _ ok⟩

theorem codeProductUsing_dense (side : CodeSide) (x y result : Matrix)
    (plan : Option (CodePlan (side.operand x y))) (work left : Nat)
    (ok : (codeProductUsing side x y plan).run work = (.ok result,left)) :
    ∃ before after, Exact.Matrix.compose x y before = (.ok result,after) :=
  codeProductWithAdmission_dense side x y result plan .fresh work left ok

theorem codeProduct_admitted (side : CodeSide) (x y result : Matrix)
    (plan : Option (CodePlan (side.operand x y)))
    (admission : OperandAdmission (side.otherOperand x y))
    (ran : ∃ work left, (codeProductWithAdmission side x y plan admission).run work = (.ok result,left)) :
    Exact.Matrix.Admitted result := by
  obtain ⟨work,left,ran⟩ := ran
  obtain ⟨before,after,checked⟩ := codeProductWithAdmission_dense side x y result plan admission work left ran
  exact Exact.compose_admitted _ _ _ before after checked

theorem codeProduct_dense (side : CodeSide) (x y result : Matrix) (work left : Nat)
    (ok : (codeProduct side x y).run work = (.ok result,left)) :
    ∃ before after, Exact.Matrix.compose x y before = (.ok result,after) :=
  codeProductUsing_dense side x y result none work left ok

#print axioms codeProductWithAdmission_dense
#print axioms codeProduct_admitted

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
  have checked : ∃ before after,
      Exact.Matrix.isometry (encoding result) before = (.ok true,after) := by
    by_cases sparse : preferSparseCodeGram (encoding result) = true
    · rw [if_pos sparse] at hi
      exact Exact.Matrix.sparseIsometry_success _ (matrixRead_admitted _ _ _ _ hm) _ _
        (exactWork_success _ _ _ _ hi)
    · rw [if_neg sparse] at hi
      exact ⟨w₂,w₃,exactWork_success _ _ _ _ hi⟩
  obtain ⟨before,after,gram⟩ := checked
  exact ⟨result,before,after,read_reference _ _ _ _ hr,rfl,gram⟩

end QleisliKernel.FiniteCarrier
