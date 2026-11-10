import Qleisli.RuntimePureNamedComposition

/-! Recurse through the exact pure-body steps and the original child receipts.
The same ordered refinement is used at every child depth.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Step runBlockCore)
open RuntimeSelectionSteps (Edge)
open Qleisli.RuntimeNamedChildRuns (CheckedStepAt IsPureLiteral PureCallAt RootInputs)
open Qleisli.RuntimePureNamedScope (PureBlock)
open Qleisli.RuntimeCallHistory (SourceAgreementWithin)

def NeedsPureLeaf {dependencies program block} : Step dependencies program block → Prop
  | .pure (.named ..) => False
  | .pure _ => True
  | _ => False

/-- A pure leaf keeps the caller's empty ordinary state, so the shared
semantic leaf law also proves the pure callback's stronger relation. -/
theorem pureLeafRefinement_of_semantic {dependencies program block}
    (steps : List (Step dependencies program block))
    (certifies : Step dependencies program block → Prop)
    (evaluate : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (law : StepRefinement steps (fun step => certifies step ∧ NeedsPureLeaf step) evaluate
      (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement steps (fun step => certifies step ∧ NeedsPureLeaf step) evaluate
      (fun _ => SourceAgreementWithin (some (· = {})) inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position checked ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  have same : ordinaryAfter = ordinaryBefore := by
    cases first
    case pure => exact ordinary
    all_goals exact False.elim checked.2
  refine WithChunkWriteBound.of_trace ?_
  intro writes expected actual outputs agrees executed
  obtain ⟨expectedOutputs,evaluation,paired⟩ :=
    ((law prior first later position checked owners ordinary read).apply writes) agrees.2 executed
  exact ⟨expectedOutputs,evaluation,paired.imp (fun _ _ relation => ⟨same.trans agrees.1,relation⟩)⟩

/-- Pure named children recurse at their written occurrence. The child
operator receives the same original source history in each spectator column. -/
noncomputable def pureRecursiveSourceSteps {dependencies}
    (leaves : ScopedSourceSteps dependencies) : Nat → ScopedSourceSteps dependencies
  | 0 => leaves
  | depth+1 => fun scope prior step source =>
    match step with
    | .pure (.named ..) =>
      evaluateOriginalPureNamed (pureRecursiveSourceSteps leaves depth) scope prior.length step source
    | _ => leaves scope prior step source

/-- Induct on the real callback fuel and retain the exact empty ordinary
frame and original checked steps through every pure named call. -/
theorem pureRecursiveSourceSteps_refine {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root}
    (leaves : ScopedSourceSteps root.dependencies) (inputs : List Nat) (origin : RootInputs)
    (localLeaves : ∀ depth {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)), PureBlock block →
      ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root mode depth) origin step ∧ NeedsPureLeaf step)
        (leaves scope) (fun _ => SourceAgreementWithin (some (· = {})) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id))) :
    ∀ depth {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)), PureBlock block →
      (∀ first ∈ steps, IsPureLiteral first) → ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root mode depth) origin step ∧
          PureCallAt (runBlockCore artifact root mode depth) origin {} step)
        (pureRecursiveSourceSteps leaves depth scope)
        (fun _ => SourceAgreementWithin (some (· = {})) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id)) := by
  intro depth
  induction depth with
  | zero =>
    intro program block scope steps shape allPure inherited prior first later position checked
      ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary chunk read
    have purity := allPure first (position ▸ List.mem_append_right prior List.mem_cons_self)
    cases first
    case pure node =>
      cases node
      case named => exact False.elim (pure_named_zero_impossible checked.2)
      all_goals
        exact localLeaves 0 scope steps shape inherited prior _ later position ⟨checked.1,trivial⟩
          owners ordinary read
    all_goals exact False.elim purity
  | succ depth ih =>
    intro program block scope steps shape allPure inherited prior first later position checked
      ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary chunk read
    have purity := allPure first (position ▸ List.mem_append_right prior List.mem_cons_self)
    cases first
    case pure node =>
      cases node
      case named =>
        exact pure_named_successor checked.2 shape
          inputs inherited (pureRecursiveSourceSteps leaves depth) scope prior.length
          (fun {childProgram childBlock} childScope childSteps childShape childPure childInherited =>
            ih (program := childProgram) (block := childBlock) childScope childSteps
              childShape childPure childInherited)
          owners ordinary read
      all_goals
        exact localLeaves (depth+1) scope steps shape inherited prior _ later position ⟨checked.1,trivial⟩
          owners ordinary read
    all_goals exact False.elim purity

#print axioms pureLeafRefinement_of_semantic
#print axioms pureRecursiveSourceSteps_refine
end Qleisli.RuntimeLiteralBody
