import QleisliKernel.FiniteRestriction.Circuit

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

def joinedBasis (selector target : Basis) : Basis := .pair :: (selector ++ target)

/-- Independently reconstruct the restriction of all original steps. A desired
matrix never substitutes for the actual body or its exact local execution. -/
def checkSector (dependencies : List Dependency) (selector label : Nat)
    (target : Basis) (steps : List Step) (required : Matrix) : WorkM Matrix := do
  guard (selector ≤ 6 && basisValid target && steps.length ≤ 1024) .limit
  guard (label < 2^selector) .request
  exactWork (QleisliKernel.Exact.charge (restrictionFields steps))
  let required ← matrixRead required
  guard (required.rows == 2^width target && required.cols == 2^width target) .request
  let restricted ← lift (readOption (restrictSteps selector label steps))
  let actual ← circuitMatrix dependencies ⟨target,restricted⟩
  wholeSpace actual
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

end QleisliKernel.FiniteRestriction
