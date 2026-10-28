import QleisliKernel.FiniteRestriction.Vector

/-! Restrict every original circuit step in order, retaining uncontrolled
scaffolding from every arm. This theorem alone grants no production acceptance;
validity/work bounds and actual-root/original-arm binding remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.FiniteRestriction
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Exact

/-- Restrict every original step in order. A disabled action alone is omitted;
uncontrolled steps from other arms remain. Any selector-targeting step refuses. -/
def restrictSteps (selector low : Nat) (steps : List Step) : Option (List Step) :=
  steps.foldr (fun step pending => do
    let restricted ← restrictStep selector low step
    let tail ← pending
    return restricted.toList ++ tail) (some [])

theorem restrictSteps_cons (selector low : Nat) (step : Step) (rest : List Step) :
    restrictSteps selector low (step :: rest) = (do
      let restricted ← restrictStep selector low step
      let tail ← restrictSteps selector low rest
      return restricted.toList ++ tail) := rfl

/-- All successful sector restrictions commute with the actual full circuit's
step fold, including the first error, exact phase and dependency selection.
This is an execution theorem, not a validity/work or original-arm binding gate. -/
theorem foldSteps_lift (dependencies : List Dependency) (steps : List Step)
    (selector low : Nat) (values : List Scalar) (restricted : List Step)
    (bound : low < 2^selector) (ran : restrictSteps selector low steps = some restricted) :
    steps.foldlM (fun values step => QleisliKernel.Finite.applyStep dependencies step values)
        (liftVector selector low values) =
      (restricted.foldlM (fun values step => QleisliKernel.Finite.applyStep dependencies step values)
        values).map (liftVector selector low) := by
  induction steps generalizing values restricted with
  | nil =>
    have same : restricted = [] := by simpa [restrictSteps] using ran.symm
    subst restricted
    rfl
  | cons step rest ih =>
    cases headRan : restrictStep selector low step with
    | none => simp [restrictSteps_cons, headRan] at ran
    | some head =>
      cases tailRan : restrictSteps selector low rest with
      | none => simp [restrictSteps_cons, headRan, tailRan] at ran
      | some tail =>
        cases head with
        | none =>
          have same : restricted = tail := by
            simpa [restrictSteps_cons, headRan, tailRan] using ran.symm
          subst restricted
          rw [List.foldlM_cons, applyStep_lift dependencies step selector low values none bound headRan,
            localApply_none]
          simpa [Except.map, bind, Except.bind] using ih values tail tailRan
        | some localStep =>
          have same : restricted = localStep :: tail := by
            simpa [restrictSteps_cons, headRan, tailRan] using ran.symm
          subst restricted
          rw [List.foldlM_cons, applyStep_lift dependencies step selector low values
            (some localStep) bound headRan, localApply_some]
          simp only [List.foldlM_cons]
          cases executed : QleisliKernel.Finite.applyStep dependencies localStep values with
          | error error => simp [Except.map, bind, Except.bind]
          | ok result =>
            simpa [Except.map, bind, Except.bind] using ih result tail tailRan

end QleisliKernel.FiniteRestriction
