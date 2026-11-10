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

def compactSectorSpace (matrix : Matrix) : WorkM Unit := do
  guard (matrix.rows == matrix.cols)
  let admitted ← matrixRead matrix
  let isometry ← exactWork (QleisliKernel.Exact.Matrix.sparseIsometryWork admitted)
  guard isometry .notIsometric

theorem compactSectorSpace_conditions (matrix : Matrix) (work left : Nat)
    (ok : (compactSectorSpace matrix).run work = (.ok (),left)) :
    matrix.rows = matrix.cols ∧ ∃ before after,
      QleisliKernel.Exact.Matrix.isometry matrix before = (.ok true,after) := by
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

#print axioms compactSectorSpace_conditions

-- Each retained Hadamard at most doubles a column's support. A dependency
-- can spread it over its own axes, and a monomial can only permute it.
-- This estimate chooses the work strategy; it grants no semantic evidence.
private def preferCompactGram (dimension : Nat) (steps : List Step) : Bool :=
  let support := steps.foldl (fun bound step =>
    let spread := match step.action with
      | .hadamard _ => 2
      | .contract axes _ _ => 2 ^ axes.length
      | .monomial .. => 1
    min dimension (bound * spread)) 1
  let cells := dimension * dimension
  cells * (13 + 2 * support) + dimension < cells * (1 + 2 * dimension)

def sectorSpace (steps : List Step) (matrix : Matrix) : WorkM Unit :=
  if preferCompactGram matrix.cols steps then compactSectorSpace matrix else wholeSpace matrix

theorem sectorSpace_conditions (steps : List Step) (matrix : Matrix) (work left : Nat)
    (ok : (sectorSpace steps matrix).run work = (.ok (),left)) :
    matrix.rows = matrix.cols ∧ ∃ before after,
      QleisliKernel.Exact.Matrix.isometry matrix before = (.ok true,after) := by
  unfold sectorSpace at ok
  split at ok
  · exact compactSectorSpace_conditions _ _ _ ok
  · exact wholeSpace_conditions _ _ _ ok

#print axioms sectorSpace_conditions

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

private def readRestriction (selector label : Nat) (target : Basis)
    (steps : List Step) : WorkM (List Step) := do
  guard (selector ≤ 6 && basisValid target && steps.length ≤ 1024) .limit
  guard (label < 2^selector) .request
  exactWork (QleisliKernel.Exact.charge (scanFields steps))
  lift (readOption (restrictSteps selector label steps))

private def computeSector (dependencies : List Dependency) (target : Basis)
    (restricted : List Step) : WorkM Matrix := do
  -- Only a fresh local computation needs another full payload validation.
  exactWork (QleisliKernel.Exact.charge (restrictionFields restricted))
  let actual ← circuitMatrix dependencies ⟨target,restricted⟩
  sectorSpace restricted actual
  return actual

def readSector (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) : WorkM Matrix := do
  let restricted ← readRestriction selector label target steps
  computeSector dependencies target restricted

private abbrev SectorCache := List (List Step × Matrix)

-- Comparison visits at most the candidate's fields per cached key. Include
-- complete phase and permutation lists before structural equality can read them.
private def comparisonFields (steps : List Step) : Nat :=
  steps.foldl (fun total step =>
    total + 4 + 2 * step.controls.length + (match step.action with
      | .hadamard _ => 0
      | .contract axes _ _ => axes.length
      | .monomial axes permutation phases => axes.length + permutation.length + phases.length)) 1

private def readCachedSector (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) (cache : SectorCache) : WorkM (Matrix × SectorCache) := do
  let restricted ← readRestriction selector label target steps
  exactWork (QleisliKernel.Exact.charge (cache.length * comparisonFields restricted))
  match cache.find? (fun entry => entry.1 == restricted) with
  | some entry => return (entry.2,cache)
  | none =>
    let actual ← computeSector dependencies target restricted
    return (actual,(restricted,actual) :: cache)

private def readCachedSectors (dependencies : List Dependency) (selector : Nat)
    (target : Basis) (steps : List Step) (cache : SectorCache) (labels : List Nat) :
    WorkM (List Matrix) :=
  Nat.rec (motive := fun _ => SectorCache → List Nat → WorkM (List Matrix))
    (fun _ remaining => match remaining with | [] => pure [] | _ :: _ => throw .limit)
    (fun _ tail current remaining => match remaining with
      | [] => pure []
      | label :: labels => do
        let (actual,next) ← readCachedSector dependencies selector label target steps current
        let remaining ← tail next labels
        return actual :: remaining) labels.length cache labels

/-- Validate the complete original tape once. Each canonical label still
restricts that tape afresh. Only structurally identical restrictions share a
locally checked matrix, with the same target and dependency environment. -/
def readSectors (dependencies : List Dependency) (selector target : Basis)
    (circuit : Circuit) : WorkM (List Matrix) := do
  guard (basisValid selector && basisValid target && circuit.steps.length ≤ 1024) .limit
  guard (circuit.basis == joinedBasis selector target) .request
  exactWork (QleisliKernel.Exact.charge (restrictionFields circuit.steps))
  guard (circuit.steps.all (stepValid dependencies (width selector + width target))) .request
  readCachedSectors dependencies (width selector) target circuit.steps []
    (List.range (2^width selector))

def SectorEvaluationBinding (dependencies : List Dependency) (selector : Nat)
    (target : Basis) (steps : List Step) (label : Nat) (actual : Matrix) : Prop :=
  label < 2^selector ∧ ∃ restricted before after unitaryAfter,
    restrictSteps selector label steps = some restricted ∧
    (circuitMatrix dependencies ⟨target,restricted⟩).run before = (.ok actual,after) ∧
    (sectorSpace restricted actual).run after = (.ok (),unitaryAfter) ∧
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

private theorem readRestriction_bound (selector label : Nat) (target : Basis)
    (steps restricted : List Step) (work left : Nat)
    (ok : (readRestriction selector label target steps).run work = (.ok restricted,left)) :
    label < 2^selector ∧ restrictSteps selector label steps = some restricted := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  have got := (lift_success _ _ _ _ h).1
  constructor
  · simpa using (guard_success _ _ _ _ hl).1
  · cases found : restrictSteps selector label steps <;> simp_all [readOption]

private def Reconstructed (dependencies : List Dependency) (target : Basis)
    (steps : List Step) (actual : Matrix) : Prop :=
  ∃ before after unitaryAfter,
    (circuitMatrix dependencies ⟨target,steps⟩).run before = (.ok actual,after) ∧
    (sectorSpace steps actual).run after = (.ok (),unitaryAfter)

private theorem computeSector_bound (dependencies : List Dependency) (target : Basis)
    (steps : List Step) (actual : Matrix) (work left : Nat)
    (ok : (computeSector dependencies target steps).run work = (.ok actual,left)) :
    Reconstructed dependencies target steps actual := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨result,w₂,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hu,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  exact ⟨w₁,w₂,w₃,hc,hu⟩

private theorem bind_reconstruction (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps restricted : List Step) (actual : Matrix)
    (bound : label < 2^selector) (read : restrictSteps selector label steps = some restricted)
    (reconstructed : Reconstructed dependencies target restricted actual) :
    SectorEvaluationBinding dependencies selector target steps label actual := by
  obtain ⟨before,after,unitaryAfter,hc,hu⟩ := reconstructed
  exact ⟨bound,restricted,before,after,unitaryAfter,read,hc,hu,
    fun values => foldSteps_lift dependencies steps selector label values restricted bound read⟩

theorem readSector_bound (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) (actual : Matrix) (work left : Nat)
    (ok : (readSector dependencies selector label target steps).run work = (.ok actual,left)) :
    SectorEvaluationBinding dependencies selector target steps label actual := by
  obtain ⟨restricted,mid,read,computed⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨bound,restrictedEq⟩ := readRestriction_bound _ _ _ _ _ _ _ read
  exact bind_reconstruction _ _ _ _ _ _ _ bound restrictedEq
    (computeSector_bound _ _ _ _ mid left computed)

private def ValidCache (dependencies : List Dependency) (target : Basis)
    (cache : SectorCache) : Prop :=
  ∀ entry ∈ cache, Reconstructed dependencies target entry.1 entry.2

private theorem readCachedSector_bound (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) (cache : SectorCache) (actual : Matrix)
    (next : SectorCache) (work left : Nat) (valid : ValidCache dependencies target cache)
    (ok : (readCachedSector dependencies selector label target steps cache).run work =
      (.ok (actual,next),left)) :
    SectorEvaluationBinding dependencies selector target steps label actual ∧
      ValidCache dependencies target next := by
  obtain ⟨restricted,w₁,read,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨bound,restrictedEq⟩ := readRestriction_bound _ _ _ _ _ _ _ read
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  split at h
  · rename_i entry found
    have returned := (pure_success _ _ _ _ h).1
    cases returned
    have mem : entry ∈ cache := List.mem_of_find?_eq_some found
    have hit : (entry.1 == restricted) = true := List.find?_some (p := fun (item : List Step × Matrix) => item.1 == restricted) found
    have same : entry.1 = restricted := beq_iff_eq.mp hit
    have reconstructed := valid entry mem
    rw [same] at reconstructed
    exact ⟨bind_reconstruction _ _ _ _ _ _ _ bound restrictedEq reconstructed,valid⟩
  · obtain ⟨value,w₃,computed,h⟩ := bind_success _ _ _ _ _ h
    have returned := (pure_success _ _ _ _ h).1
    cases returned
    have reconstructed := computeSector_bound _ _ _ _ w₂ w₃ computed
    refine ⟨bind_reconstruction _ _ _ _ _ _ _ bound restrictedEq reconstructed,?_⟩
    intro entry inside
    rcases List.mem_cons.mp inside with equal | mem
    · subst entry
      exact reconstructed
    · exact valid entry mem

private theorem readCachedSectors_bound (dependencies : List Dependency) (selector : Nat)
    (target : Basis) (steps : List Step) (cache : SectorCache) (labels : List Nat)
    (actual : List Matrix) (work left : Nat) (valid : ValidCache dependencies target cache)
    (ok : (readCachedSectors dependencies selector target steps cache labels).run work =
      (.ok actual,left)) :
    QleisliKernel.Exact.ListRel (SectorEvaluationBinding dependencies selector target steps)
      labels actual := by
  induction labels generalizing cache actual work left with
  | nil =>
    have same := (pure_success [] actual work left ok).1
    subst actual
    trivial
  | cons label labels ih =>
    obtain ⟨⟨value,next⟩,w₁,read,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨bound,nextValid⟩ := readCachedSector_bound _ _ _ _ _ _ _ _ _ _ valid read
    obtain ⟨remaining,w₂,tail,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst actual
    exact ⟨bound,ih next remaining w₁ w₂ nextValid tail⟩

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
  have relation := readCachedSectors_bound dependencies (width selector) target circuit.steps []
    (List.range (2^width selector)) actual w₄ left (by simp [ValidCache]) h
  exact ⟨(guard_success _ _ _ _ hl).1,beq_iff_eq.mp (guard_success _ _ _ _ hi).1,
    (guard_success _ _ _ _ hs).1,relation⟩


#print axioms readSectors_bound

end QleisliKernel.FiniteRestriction
