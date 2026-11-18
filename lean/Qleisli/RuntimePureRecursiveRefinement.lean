import Qleisli.RuntimePureNamedComposition
import Qleisli.RuntimeExclusiveCoordinates

/-! Recurse through the exact pure-body steps and the original child receipts.
The same ordered refinement is used at every child depth.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Step runBlockCore)
open RuntimeSelectionSteps (Edge)
open Qleisli.RuntimeNamedChildRuns (CheckedStepAt IsPureLiteral OrdinaryAligned PureCallAt PureNodeCallAt RootInputs)
open Qleisli.RuntimePureNamedScope (PureBlock)
open Qleisli.RuntimeCallHistory (SourceAgreementWithin)
open Qleisli.RuntimeExclusiveCoordinates (AccessLeaf PureStepLaw evaluate_pure_access_refines
  pure_step_law_of_occurrence sole_step withIndexedAccess)

def NeedsPureLeaf {dependencies program block} : Step dependencies program block → Prop
  | .pure (.named ..) | .pure (.exclusive ..) => False
  | .pure _ => True
  | _ => False

/-- A pure leaf preserves the actual ordinary state of its caller. -/
theorem pureLeafRefinement_of_semantic_in_frame {dependencies program block}
    (steps : List (Step dependencies program block))
    (certifies : Step dependencies program block → Prop)
    (evaluate : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (callOrdinary : RuntimeOrdinaryBody.State)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    (law : StepRefinement steps (fun step => certifies step ∧ NeedsPureLeaf step) evaluate
      (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement steps (fun step => certifies step ∧ NeedsPureLeaf step) evaluate
      (fun _ => SourceAgreementWithin (some (· = callOrdinary)) inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position checked ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  have same : ordinaryAfter = ordinaryBefore := by
    cases first
    case pure => exact OrdinaryAligned.pure_preserves ordinary
    all_goals exact False.elim checked.2
  refine WithChunkWriteBound.of_trace ?_
  intro writes expected actual outputs agrees executed
  obtain ⟨expectedOutputs,evaluation,paired⟩ :=
    ((law prior first later position checked owners ordinary read).apply writes) agrees.2 executed
  exact ⟨expectedOutputs,evaluation,paired.imp (fun _ _ relation => ⟨same.trans agrees.1,relation⟩)⟩

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
      (inherited.map (fun holds id => ¬ holds id)) :=
  pureLeafRefinement_of_semantic_in_frame steps certifies evaluate {} inputs inherited law

/-- Pure named children recurse at their written occurrence. The child
operator receives the same original source history in each spectator column. -/
private noncomputable def pureAtDepth {dependencies}
    (children leaves : ScopedSourceSteps dependencies) : ScopedSourceSteps dependencies :=
  fun scope prior step source => match step with
    | .pure (.named ..) => evaluateActualPureNamed children scope prior.length step source
    | step => leaves scope prior step source

noncomputable def pureRecursiveSourceStepsAt {dependencies}
    (leaves : Nat → ScopedSourceSteps dependencies) : Nat → ScopedSourceSteps dependencies
  | 0 => withIndexedAccess (leaves 0)
  | depth+1 => withIndexedAccess (pureAtDepth (pureRecursiveSourceStepsAt leaves depth) (leaves (depth+1)))

private theorem pure_node_with_access_refines {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root}
    {next : RuntimePureBody.BlockRunner artifact root mode} {origin program block}
    (evaluate : ScopedSourceSteps root.dependencies) (callOrdinary : RuntimeOrdinaryBody.State)
    (inputs : List Nat) (scope : List Edge)
    (prior : List (Step root.dependencies program block)) (node : RuntimePureBody.Node root.dependencies program block)
    (inherited : Option (Nat → Prop))
    (localLaw : ∀ (atScope : List Edge) (inner : RuntimePureBody.Node root.dependencies program block), AccessLeaf inner →
      CheckedStepAt next origin (.pure inner) ∧ PureCallAt next origin callOrdinary (.pure inner) →
      PureStepLaw inner (evaluate atScope prior (.pure inner)) inputs (some (· = callOrdinary)) inherited)
    (checked : CheckedStepAt next origin (.pure node) ∧ PureCallAt next origin callOrdinary (.pure node)) :
    PureStepLaw node (withIndexedAccess evaluate scope prior (.pure node)) inputs (some (· = callOrdinary)) inherited := by
  let certifies (inner : RuntimePureBody.Node root.dependencies program block) :=
    CheckedStepAt next origin (.pure inner) ∧ PureCallAt next origin callOrdinary (.pure inner)
  exact evaluate_pure_access_refines (fun atScope => evaluate atScope) prior inputs (some (· = callOrdinary))
    inherited certifies
    (fun _ _ _ _ valid => ⟨valid.1.1,valid.1.2.1,PureNodeCallAt.ordinary_aligned valid.1.2.2.2,
      valid.1.2.2.1,PureCallAt.exclusive_inner valid.2⟩)
    localLaw scope node checked

private theorem pure_steps_of_laws {dependencies program block}
    (evaluate : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (callOrdinary : RuntimeOrdinaryBody.State) (inputs : List Nat)
    (steps : List (Step dependencies program block)) (inherited : Option (Nat → Prop))
    (allPure : ∀ first ∈ steps, IsPureLiteral first)
    (certifies : Step dependencies program block → Prop)
    (localLaw : ∀ (prior : List (Step dependencies program block)) (node : RuntimePureBody.Node dependencies program block),
      certifies (.pure node) →
      PureStepLaw node (evaluate prior (.pure node)) inputs (some (· = callOrdinary)) inherited) :
    StepRefinement steps certifies evaluate
      (fun _ => SourceAgreementWithin (some (· = callOrdinary)) inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position checked ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary chunk read
  have purity := allPure first (position ▸ List.mem_append_right prior List.mem_cons_self)
  cases first
  case pure node => exact localLaw prior node checked [] (.pure node) [] rfl trivial owners ordinary read
  all_goals exact False.elim purity

/-- Refine one pure occurrence at its actual prefix in the enclosing block.
Each named callback supplies its own checked pure child block. -/
theorem pureRecursiveSourceStepAt_refine_in_frame {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root}
    (leaves : Nat → ScopedSourceSteps root.dependencies) (inputs : List Nat) (origin : RootInputs)
    (callOrdinary : RuntimeOrdinaryBody.State) (limit : Nat)
    (admit : ∀ {program}, RuntimeInterval.Block root.dependencies program → Prop)
    (admitsPure : ∀ {program} {block : RuntimeInterval.Block root.dependencies program}, PureBlock block → admit block)
    (localLeaves : ∀ depth, depth ≤ limit → ∀ {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)), admit block →
      ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root mode depth) origin step ∧ NeedsPureLeaf step)
        (leaves depth scope) (fun _ => SourceAgreementWithin (some (· = callOrdinary)) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id))) :
    ∀ depth, depth ≤ limit → ∀ {program block} (scope : List Edge)
      (prior : List (Step root.dependencies program block)) (node : RuntimePureBody.Node root.dependencies program block),
      admit block → ∀ inherited,
      CheckedStepAt (runBlockCore artifact root mode depth) origin (.pure node) ∧
        PureCallAt (runBlockCore artifact root mode depth) origin callOrdinary (.pure node) →
      PureStepLaw node (pureRecursiveSourceStepsAt leaves depth scope prior (.pure node))
        inputs (some (· = callOrdinary)) inherited := by
  intro depth
  induction depth with
  | zero =>
    intro within program block scope prior node admitted inherited checked
    refine pure_node_with_access_refines (leaves 0) callOrdinary inputs scope prior node inherited ?_ checked
    intro atScope inner leaf valid
    cases inner
    case named => exact False.elim (pure_named_zero_impossible valid.2)
    case exclusive => exact False.elim leaf
    all_goals
      exact pure_step_law_of_occurrence _ (before := prior) (after := []) (evaluate := leaves 0 atScope) rfl
        (localLeaves 0 within atScope _ admitted inherited) ⟨valid.1,trivial⟩
  | succ depth ih =>
    intro within program block scope prior node admitted inherited checked
    refine pure_node_with_access_refines (pureAtDepth (pureRecursiveSourceStepsAt leaves depth) (leaves (depth+1)))
      callOrdinary inputs scope prior node inherited ?_ checked
    intro atScope inner leaf valid
    cases inner
    case named =>
      intro earlier first later position _ ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary chunk read
      have same := sole_step position
      subst first
      exact pure_named_successor_in_frame valid.2
        inputs inherited (pureRecursiveSourceStepsAt leaves depth) atScope prior.length
        (fun childScope childSteps childShape childPure childInherited =>
          pure_steps_of_laws (pureRecursiveSourceStepsAt leaves depth childScope) callOrdinary inputs
            childSteps childInherited childPure _ (fun childPrior childNode childChecked =>
              ih (Nat.le_trans (Nat.le_succ depth) within) childScope childPrior childNode
                (admitsPure childShape) childInherited childChecked))
        owners ordinary read
    case exclusive => exact False.elim leaf
    all_goals
      exact pure_step_law_of_occurrence _ (before := prior) (after := []) (evaluate := leaves (depth+1) atScope) rfl
        (localLeaves (depth+1) within atScope _ admitted inherited) ⟨valid.1,trivial⟩

theorem pureRecursiveSourceStepsAt_refine_in_frame {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root}
    (leaves : Nat → ScopedSourceSteps root.dependencies) (inputs : List Nat) (origin : RootInputs)
    (callOrdinary : RuntimeOrdinaryBody.State) (limit : Nat)
    (localLeaves : ∀ depth, depth ≤ limit → ∀ {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)), PureBlock block →
      ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root mode depth) origin step ∧ NeedsPureLeaf step)
        (leaves depth scope) (fun _ => SourceAgreementWithin (some (· = callOrdinary)) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id))) :
    ∀ depth, depth ≤ limit → ∀ {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)), PureBlock block →
      (∀ first ∈ steps, IsPureLiteral first) → ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root mode depth) origin step ∧
          PureCallAt (runBlockCore artifact root mode depth) origin callOrdinary step)
        (pureRecursiveSourceStepsAt leaves depth scope)
        (fun _ => SourceAgreementWithin (some (· = callOrdinary)) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id)) := by
  intro depth within program block scope steps shape allPure inherited
  apply pure_steps_of_laws (pureRecursiveSourceStepsAt leaves depth scope) callOrdinary inputs steps inherited allPure
  intro prior node checked
  exact pureRecursiveSourceStepAt_refine_in_frame leaves inputs origin callOrdinary limit
    (fun block => PureBlock block) (fun pure => pure) localLeaves depth within scope prior node shape inherited checked

theorem pureRecursiveSourceStepsAt_refine {artifact : Artifact} {root : Validity.Root}
    {mode : RuntimePureBody.ExecutionMode artifact root}
    (leaves : Nat → ScopedSourceSteps root.dependencies) (inputs : List Nat) (origin : RootInputs) (limit : Nat)
    (localLeaves : ∀ depth, depth ≤ limit → ∀ {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)), PureBlock block →
      ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root mode depth) origin step ∧ NeedsPureLeaf step)
        (leaves depth scope) (fun _ => SourceAgreementWithin (some (· = {})) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id))) :
    ∀ depth, depth ≤ limit → ∀ {program block} (scope : List Edge) (steps : List (Step root.dependencies program block)), PureBlock block →
      (∀ first ∈ steps, IsPureLiteral first) → ∀ inherited,
      StepRefinement steps
        (fun step => CheckedStepAt (runBlockCore artifact root mode depth) origin step ∧
          PureCallAt (runBlockCore artifact root mode depth) origin {} step)
        (pureRecursiveSourceStepsAt leaves depth scope)
        (fun _ => SourceAgreementWithin (some (· = {})) inherited inputs)
        (inherited.map (fun holds id => ¬ holds id)) :=
  pureRecursiveSourceStepsAt_refine_in_frame leaves inputs origin {} limit localLeaves

/-- Use one shared leaf evaluator at every level. -/
noncomputable abbrev pureRecursiveSourceSteps {dependencies}
    (leaves : ScopedSourceSteps dependencies) : Nat → ScopedSourceSteps dependencies :=
  pureRecursiveSourceStepsAt (fun _ => leaves)

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
  exact pureRecursiveSourceStepsAt_refine (fun _ => leaves) inputs origin depth
    (fun fuel _ => localLeaves fuel) depth (Nat.le_refl _)

#print axioms pureLeafRefinement_of_semantic_in_frame
#print axioms pureLeafRefinement_of_semantic
#print axioms pureRecursiveSourceStepAt_refine_in_frame
#print axioms pureRecursiveSourceStepsAt_refine_in_frame
#print axioms pureRecursiveSourceStepsAt_refine
#print axioms pureRecursiveSourceSteps_refine
end Qleisli.RuntimeLiteralBody
