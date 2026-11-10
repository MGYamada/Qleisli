import QleisliKernel.FiniteRestriction.Circuit
import QleisliKernel.ExactSparse

/-! Bounded reconstruction of every sector of one original finite circuit.
Each port retains its existing six-bit profile; no joined dense matrix is built.
This internal component adds no native mode or accepted handle. Its enclosing
caller must freshly bind dependencies, original Raw/source subjects and arms.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.FiniteRestriction
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Exact
open QleisliKernel.Finite

/-- Charge original fields before validation/restriction. Quadratic terms cover
the existing duplicate-axis/permutation checks, including malformed proposals. -/
def restrictionFields (steps : List Step) : Nat :=
  (steps.map fun step =>
    let axes := targets step.action
    16 * (step.controls.length + axes.length + 1)^2 +
      match step.action with
      | .monomial _ permutation phases => 16 * (permutation.length+1)^2 + phases.length
      | _ => 0).sum

/-- The actual restriction of an ordered tape equals the expected tape,
including all control predicates, wire positions, phases and dependency slots. -/
structure TapeMatch (selector label : Nat) (outer expected : List Step) : Type where
  bounded : label < 2^selector
  restriction : restrictSteps selector label outer = some expected

/-- Compare the restricted instructions before any matrix construction. The
caller still binds both tapes to the same dependency and source subjects. -/
def checkTape (selector label : Nat) (outer expected : List Step) :
    WorkM (TapeMatch selector label outer expected) := do
  guard (selector ≤ 6 && outer.length ≤ 1024 && expected.length ≤ 1024) .limit
  exactWork (QleisliKernel.Exact.charge (restrictionFields outer))
  if bounded : label < 2^selector then
    match read : restrictSteps selector label outer with
    | none => throw .request
    | some actual =>
      exactWork (QleisliKernel.Exact.charge (restrictionFields actual + restrictionFields expected + 1))
      if same : actual == expected then
        return ⟨bounded,read.trans (congrArg some (beq_iff_eq.mp same))⟩
      else throw .equation
  else throw .request

theorem TapeMatch.execution (dependencies : List Dependency) {selector label : Nat}
    {outer expected : List Step} (checked : TapeMatch selector label outer expected)
    (values : List Scalar) :
    outer.foldlM (fun input step => applyStep dependencies step input) (liftVector selector label values) =
      (expected.foldlM (fun input step => applyStep dependencies step input) values).map
        (liftVector selector label) :=
  foldSteps_lift dependencies outer selector label values expected checked.bounded checked.restriction

#print axioms TapeMatch.execution

def joinedBasis (selector target : Basis) : Basis := .pair :: (selector ++ target)

-- At up to four rows the ordinary Gram charge is smaller than reading
-- and compacting even a permutation matrix. Keep that path for small sectors.
def computedSectorSpace (matrix : Matrix) : WorkM Unit := do
  if matrix.cols ≤ 4 then
    wholeSpace matrix
  else
    guard (matrix.rows == matrix.cols)
    let admitted ← matrixRead matrix
    let isometry ← exactWork (QleisliKernel.Exact.Matrix.sparseIsometryWork admitted)
    guard isometry .notIsometric

theorem computedSectorSpace_conditions (matrix : Matrix) (work left : Nat)
    (ok : (computedSectorSpace matrix).run work = (.ok (),left)) :
    matrix.rows = matrix.cols ∧ ∃ before after,
      QleisliKernel.Exact.Matrix.isometry matrix before = (.ok true,after) := by
  by_cases small : matrix.cols ≤ 4
  · exact wholeSpace_conditions _ _ _ (by simpa only [computedSectorSpace,if_pos small] using ok)
  simp only [computedSectorSpace,if_neg small] at ok
  obtain ⟨_,w₁,shape,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨read,w₂,admission,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨isometry,w₃,checked,h⟩ := bind_success _ _ _ _ _ h
  have trueCheck := (guard_success _ _ _ _ h).1
  subst isometry
  obtain ⟨same,valid⟩ := matrixRead_value _ _ _ _ admission
  subst read
  have admitted : QleisliKernel.Exact.Matrix.Admitted matrix := by
    unfold matrixRead at admission
    obtain ⟨_,_,dimensions,h⟩ := bind_success _ _ _ _ _ admission
    obtain ⟨_,_,length,_⟩ := bind_success _ _ _ _ _ h
    exact ⟨(guard_success _ _ _ _ dimensions).1,beq_iff_eq.mp (guard_success _ _ _ _ length).1,
      List.all_eq_true.mp valid⟩
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ shape).1,
    QleisliKernel.Exact.Matrix.sparseIsometry_success matrix admitted w₂ w₃
      (exactWork_success _ _ _ _ checked)⟩

#print axioms computedSectorSpace_conditions

private def reconstructSector (dependencies : List Dependency) (target : Basis)
    (steps : List Step) : WorkM Matrix := do
  let actual ← circuitMatrix dependencies ⟨target,steps⟩
  wholeSpace actual
  return actual

private def evaluateSector (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) : WorkM Matrix := do
  let restricted ← lift (readOption (restrictSteps selector label steps))
  reconstructSector dependencies target restricted

/-- Independently reconstruct the restriction of all original steps. A desired
matrix never substitutes for the actual body or its exact local execution. -/
def checkSector (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) (required : Matrix) : WorkM Matrix := do
  guard (selector ≤ 6 && basisValid target && steps.length ≤ 1024) .limit
  guard (label < 2^selector) .request
  exactWork (QleisliKernel.Exact.charge (restrictionFields steps))
  let required ← matrixRead required
  guard (required.rows == 2^width target && required.cols == 2^width target) .request
  let actual ← evaluateSector dependencies selector label target steps
  guard (actual == required) .equation
  return actual

/-- Original trees, complete physical sectors and original step validity remain
explicit. The old global six-bit finite matrix checker is unchanged. -/
def checkSectors (dependencies : List Dependency) (selector target : Basis)
    (circuit : Circuit) (required : List Matrix) : WorkM (List Matrix) := do
  guard (basisValid selector && basisValid target && circuit.steps.length ≤ 1024) .limit
  guard (circuit.basis == joinedBasis selector target && required.length == 2^width selector) .request
  exactWork (QleisliKernel.Exact.charge (restrictionFields circuit.steps))
  guard (circuit.steps.all (stepValid dependencies (width selector + width target))) .request
  required.zipIdx.mapM fun (meaning,label) =>
    checkSector dependencies (width selector) label target circuit.steps meaning

/-- Restriction visits controls and axes. A retained monomial shares its
permutation and phase lists with the original step. -/
private def scanFields (steps : List Step) : Nat :=
  steps.foldl (fun total step =>
    total + 16 * (step.controls.length + (targets step.action).length + 1)) 0

/-- Reconstruct all canonical physical sectors once before an enclosing logical
code-space check. No producer matrix or sector subset supplies this result. -/
def readSector (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) : WorkM Matrix := do
  guard (selector ≤ 6 && basisValid target && steps.length ≤ 1024) .limit
  guard (label < 2^selector) .request
  exactWork (QleisliKernel.Exact.charge (scanFields steps))
  let restricted ← lift (readOption (restrictSteps selector label steps))
  -- The local circuit validator inspects only active instructions. Reserve
  -- their full validation cost before it examines the retained payloads.
  exactWork (QleisliKernel.Exact.charge (restrictionFields restricted))
  let actual ← circuitMatrix dependencies ⟨target,restricted⟩
  computedSectorSpace actual
  return actual

def readSectors (dependencies : List Dependency) (selector target : Basis)
    (circuit : Circuit) : WorkM (List Matrix) := do
  guard (basisValid selector && basisValid target && circuit.steps.length ≤ 1024) .limit
  guard (circuit.basis == joinedBasis selector target) .request
  exactWork (QleisliKernel.Exact.charge (restrictionFields circuit.steps))
  guard (circuit.steps.all (stepValid dependencies (width selector + width target))) .request
  (List.range (2^width selector)).mapM fun label =>
    readSector dependencies (width selector) label target circuit.steps

def SectorEvaluationBinding (dependencies : List Dependency) (selector : Nat)
    (target : Basis) (steps : List Step) (label : Nat) (actual : Matrix) : Prop :=
  label < 2^selector ∧ ∃ restricted before after unitaryAfter,
    restrictSteps selector label steps = some restricted ∧
    (circuitMatrix dependencies ⟨target,restricted⟩).run before = (.ok actual,after) ∧
    (computedSectorSpace actual).run after = (.ok (),unitaryAfter) ∧
    (∀ values : List Scalar,
      steps.foldlM (fun values step => applyStep dependencies step values)
          (liftVector selector label values) =
        (restricted.foldlM (fun values step => applyStep dependencies step values) values).map
          (liftVector selector label))

/-- Binding postcondition for one original ordered request. The executable
reconstruction witness is separate from the enclosing source/Raw binding. -/
def SectorBinding (dependencies : List Dependency) (selector : Nat) (target : Basis)
    (steps : List Step) (request : Matrix × Nat) (actual : Matrix) : Prop :=
  actual = request.1 ∧ request.2 < 2^selector ∧
    ∃ restricted before after unitaryAfter,
      restrictSteps selector request.2 steps = some restricted ∧
      (circuitMatrix dependencies ⟨target,restricted⟩).run before = (.ok actual,after) ∧
      (wholeSpace actual).run after = (.ok (),unitaryAfter) ∧
      (∀ values : List Scalar,
        steps.foldlM (fun values step => applyStep dependencies step values)
            (liftVector selector request.2 values) =
          (restricted.foldlM (fun values step => applyStep dependencies step values) values).map
            (liftVector selector request.2))

/-- Success binds the original complete step list to its local reconstruction
and every input vector's actual execution, including any arithmetic error. -/
theorem checkSector_bound (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) (required actual : Matrix) (work left : Nat)
    (ok : (checkSector dependencies selector label target steps required).run work = (.ok actual,left)) :
    SectorBinding dependencies selector target steps (required,label) actual := by
  simp only [checkSector,evaluateSector,reconstructSector,bind_assoc,pure_bind] at ok
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hl,h⟩ := bind_success _ _ _ _ _ h
  have bound : label < 2^selector := by simpa using (guard_success _ _ _ _ hl).1
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨read,w₄,hr,h⟩ := bind_success _ _ _ _ _ h
  have same := (matrixRead_value _ _ _ _ hr).1
  subst read
  obtain ⟨_,w₅,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨restricted,w₆,hs,h⟩ := bind_success _ _ _ _ _ h
  have restrictedEq : restrictSteps selector label steps = some restricted := by
    have got := (lift_success _ _ _ _ hs).1
    cases found : restrictSteps selector label steps <;> simp_all [readOption]
  obtain ⟨result,w₇,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₈,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₉,he,h⟩ := bind_success _ _ _ _ _ h
  have finalEq := (pure_success _ _ _ _ h).1
  subst actual
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ he).1,bound,restricted,w₆,w₇,w₈,
    restrictedEq,hc,hu,fun values => foldSteps_lift dependencies steps selector label values
      restricted bound restrictedEq⟩

/-- The finite-error work monad preserves the complete ordered list relation. -/
theorem mapM_relation {α β : Type} (step : α → WorkM β) (p : α → β → Prop)
    (preserve : ∀ a b work left, (step a).run work = (.ok b,left) → p a b)
    (xs : List α) (ys : List β) (work left : Nat)
    (ok : (xs.mapM step).run work = (.ok ys,left)) :
    QleisliKernel.Exact.ListRel p xs ys := by
  induction xs generalizing ys work left with
  | nil =>
    simp only [List.mapM_nil] at ok
    obtain ⟨same,_⟩ := pure_success [] ys work left ok
    subst ys
    trivial
  | cons a xs ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨b,middle,hb,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨rest,tailWork,ht,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨same,_⟩ := pure_success (b :: rest) ys tailWork left h
    subst ys
    exact ⟨preserve a b work middle hb,ih rest middle tailWork ht⟩

/-- Every physical label is checked in its canonical ordinal position. Missing,
reordered or truncated results cannot supply this complete list relation. -/
theorem checkSectors_bound (dependencies : List Dependency) (selector target : Basis)
    (circuit : Circuit) (required actual : List Matrix) (work left : Nat)
    (ok : (checkSectors dependencies selector target circuit required).run work = (.ok actual,left)) :
    (basisValid selector && basisValid target && circuit.steps.length ≤ 1024) = true ∧
      (circuit.basis == joinedBasis selector target && required.length == 2^width selector) = true ∧
      circuit.steps.all (stepValid dependencies (width selector + width target)) = true ∧
      QleisliKernel.Exact.ListRel
        (SectorBinding dependencies (width selector) target circuit.steps) required.zipIdx actual := by
  obtain ⟨_,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hs,h⟩ := bind_success _ _ _ _ _ h
  have relation := mapM_relation
    (fun (request : Matrix × Nat) =>
      checkSector dependencies (width selector) request.2 target circuit.steps request.1)
    (SectorBinding dependencies (width selector) target circuit.steps)
    (fun request result work left checked =>
      checkSector_bound dependencies (width selector) request.2 target circuit.steps
        request.1 result work left checked) required.zipIdx actual w₄ left h
  exact ⟨(guard_success _ _ _ _ hl).1,(guard_success _ _ _ _ hi).1,
    (guard_success _ _ _ _ hs).1,relation⟩

theorem readSector_bound (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) (actual : Matrix) (work left : Nat)
    (ok : (readSector dependencies selector label target steps).run work = (.ok actual,left)) :
    SectorEvaluationBinding dependencies selector target steps label actual := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  have bound : label < 2^selector := by simpa using (guard_success _ _ _ _ hl).1
  obtain ⟨restricted,w₄,hs,h⟩ := bind_success _ _ _ _ _ h
  have restrictedEq : restrictSteps selector label steps = some restricted := by
    have got := (lift_success _ _ _ _ hs).1
    cases found : restrictSteps selector label steps <;> simp_all [readOption]
  obtain ⟨_,w₅,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₆,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,hu,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  exact ⟨bound,restricted,w₅,w₆,w₇,restrictedEq,hc,hu,
    fun values => foldSteps_lift dependencies steps selector label values restricted bound restrictedEq⟩

theorem readSectors_bound (dependencies : List Dependency) (selector target : Basis)
    (circuit : Circuit) (actual : List Matrix) (work left : Nat)
    (ok : (readSectors dependencies selector target circuit).run work = (.ok actual,left)) :
    (basisValid selector && basisValid target && circuit.steps.length ≤ 1024) = true ∧
      circuit.basis = joinedBasis selector target ∧
      circuit.steps.all (stepValid dependencies (width selector + width target)) = true ∧
      QleisliKernel.Exact.ListRel
        (SectorEvaluationBinding dependencies (width selector) target circuit.steps)
        (List.range (2^width selector)) actual := by
  obtain ⟨_,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hs,h⟩ := bind_success _ _ _ _ _ h
  have relation := mapM_relation
    (fun label => readSector dependencies (width selector) label target circuit.steps)
    (SectorEvaluationBinding dependencies (width selector) target circuit.steps)
    (fun label result work left checked =>
      readSector_bound dependencies (width selector) label target circuit.steps result work left checked)
    (List.range (2^width selector)) actual w₄ left h
  exact ⟨(guard_success _ _ _ _ hl).1,beq_iff_eq.mp (guard_success _ _ _ _ hi).1,
    (guard_success _ _ _ _ hs).1,relation⟩


end QleisliKernel.FiniteRestriction
