import Qleisli.RuntimePureProviderNative
import Qleisli.RuntimeLiteralConditionalRefinement

/-! Follow the original pure provider's actual source flow and checked return
order through the shared semantic action and named-call recursion.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open QleisliKernel.Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run)
open RuntimePureBody (runBlockCore)
open RuntimeSelectionSteps (Edge)
open Qleisli.RuntimeNamedChildRuns (CheckedStepAt PureCallAt)
open Qleisli.RuntimeCallHistory (SourceAgreementWithin)

/-- The literal pure provider, its original source calls and its written
return preserve the operator and visible/hidden history on the same input. -/
theorem original_pure_provider_refinement {artifact root owner name signature program request bindings}
    {body : @SourceRuntimeTrace.Body artifact.sources owner name signature}
    (checked : @RuntimePureBody.Checked artifact root owner name signature body program request bindings)
    (inputs : List Nat) (scope : List Edge)
    (sourceInitial : SourceHistory) (initial : History) (results : List History)
    (executed : let block := checked.result.prepared.block
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run root.dependencies block.fuel events initial) = some results) :
    let block := checked.result.prepared.block
    let source := SourceRuntimeScope.Subject.whole body
    let initialHistory : RuntimeStructuralAction.SourceState :=
      ⟨bindings,body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners,
        body.checked.summary.nextOwner⟩
    (∀ input : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (RuntimePureBody.reordered source.initialRoles block.entry initialHistory.bindings) input →
      SourceAgreementWithin (some (· = {})) none inputs block.entry
        {initialHistory with bindings := input.bindings} {} sourceInitial initial) →
    ∃ ownerEnd : RuntimeStructuralAction.SourceState,
    ∃ last : RuntimeInterval.Checked block block.operations.length 0,
      RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
      ∃ returned : RuntimeOwnerMap.Checked source.outputRoles last.after,
        RuntimeInterval.Computed (RuntimePureBody.reordered source.outputRoles last.after ownerEnd.bindings) returned ∧
        checked.result.history = {ownerEnd with bindings := returned.bindings} ∧
        ∃ expected,
          runSourceHistories (pureRecursiveSourceSteps recursiveBodyLeaves 127 scope) []
            checked.result.steps [sourceInitial] = some expected ∧
          List.Forall₂ (SourceAgreementWithin (some (· = {})) none inputs last.after
              checked.result.history checked.result.ordinary)
            (expected.map (returnHistory returned.bindings)) results := by
  intro block source history starts
  obtain ⟨entry,entryRead,finish,flow,returned,facts⟩ :=
    RuntimeNamedChildRuns.original_pure_body checked
  obtain ⟨last,lastRead,output,outputRead,outputHistory⟩ := returned
  let origin := RuntimeBranchCondition.rootEntries (.root body)
  let next := runBlockCore artifact root (.fresh .strict) 127
  have laws := pureRecursiveSourceSteps_refine (mode := .fresh .strict)
    recursiveBodyLeaves inputs origin
    (fun depth {program block} atStep steps _ inherited =>
      pureBodyLeaves_refine atStep inputs inherited steps
        (CheckedStepAt (runBlockCore artifact root (.fresh .strict) depth) origin))
    127 scope checked.result.steps (Qleisli.RuntimePureProviderNative.checked_pure_shape checked) facts.allPure none
  have ordinaryLaw := laws.of_scoped_certifies (fun step present checkedStep =>
    (show CheckedStepAt next origin step ∧ PureCallAt next origin {} step from
      ⟨checkedStep,facts.calls step present⟩))
  obtain ⟨expected,evaluated,paired⟩ :=
    refineFlow flow last sourceInitial initial
      (pureRecursiveSourceSteps recursiveBodyLeaves 127 scope)
      (fun _ => SourceAgreementWithin (some (· = {})) none inputs)
      executed ordinaryLaw (starts entry entryRead)
  refine ⟨finish,last,lastRead,output,outputRead,outputHistory,expected,evaluated,?_⟩
  have finishReturned : ∀ {sourceHistory actual},
      SourceAgreementWithin (some (· = {})) none inputs last.before finish checked.result.ordinary sourceHistory actual →
      SourceAgreementWithin (some (· = {})) none inputs last.after
        {finish with bindings := output.bindings} checked.result.ordinary
        (returnHistory output.bindings sourceHistory) actual := by
    intro sourceHistory actual agrees
    have atExit : SourceAgreementWithin (some (· = {})) none inputs last.after finish checked.result.ordinary
        sourceHistory actual :=
      (Qleisli.RuntimeOwnerTransitionAction.empty_state last).symm ▸ agrees
    exact ⟨atExit.1,sparse_return_refines inputs output outputRead atExit.2⟩
  rw [List.forall₂_map_left_iff,outputHistory]
  exact paired.imp (fun _ _ agrees => finishReturned agrees)

#print axioms original_pure_provider_refinement
end Qleisli.RuntimeLiteralBody
