import Qleisli.RuntimeNamedChildRuns

/-! Named-boundary source-state continuity for the actual body reader.
The proof follows the real loop, its original source queries and its unchanged
work counter. It supplies no logical action, encoding equality or new acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedSourceFlow
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody

/-- Every successful actual iteration retains its original entry read, the
complete ordered step list, and the actual final source-return read. The named
state invariant includes actual primitive and selection maps but asserts no
physical action for any step constructor. -/
theorem step_flow (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (next : BlockRunner artifact root execution) (outputBoundary : OutputBoundary)
    (pureNext : RuntimeNamedChildRuns.PurePreservesOrdinary next)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (sourcePlan : execution.queries.BodyData source request)
    (initialHistory : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockStep artifact root execution next .runtimeBody outputBoundary source path program request
        sourcePlan initialHistory ordinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Run {initialHistory with bindings := initial.bindings} result.1.steps last ∧
        Returned block source.outputRoles last result.1.history := by
  obtain ⟨initial,initialRead,last,flow,returned⟩ :=
    RuntimeNamedChildRuns.step_flow artifact root execution next outputBoundary pureNext source path program request
      sourcePlan initialHistory ordinary block result checked
  exact ⟨initial,initialRead,last,flow.source,returned⟩

/-- The same property holds for the actual fuelled recursion, for every
successful original work budget. Recursive child results remain the actual
loop's results; there is no alternate traversal or reset of exact work. -/
theorem core_flow (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (fuel : Nat) (outputBoundary : OutputBoundary)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (sourcePlan : execution.queries.BodyData source request)
    (initialHistory : RuntimeStructuralAction.SourceState) (ordinary : RuntimeOrdinaryBody.State)
    (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (checked : RuntimeInterval.Computed
      (runBlockCore artifact root execution fuel .runtimeBody outputBoundary source path program request
        sourcePlan initialHistory ordinary block) result) :
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles block.entry initialHistory.bindings) initial ∧
      ∃ last, Run {initialHistory with bindings := initial.bindings} result.1.steps last ∧
        Returned block source.outputRoles last result.1.history := by
  cases fuel with
  | zero =>
    obtain ⟨work,left,ran⟩ := checked
    cases ran
  | succ fuel =>
    exact step_flow artifact root execution (runBlockCore artifact root execution fuel) outputBoundary
      (RuntimeNamedChildRuns.core_pure_preserves_ordinary artifact root execution fuel) source path program request sourcePlan initialHistory ordinary block result checked

/-- The retained successful traversal of this original project body supplies
its own entry/return reads and state chain. A producer-supplied success or an
assumed equality between adjacent source maps is not a premise. -/
theorem original_body {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) :
    let source := SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let initialHistory := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    ∃ initial : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
      RuntimeInterval.Computed (reordered source.initialRoles body.checked.native.block.entry initialHistory.bindings) initial ∧
      ∃ last, Run {initialHistory with bindings := initial.bindings} body.checked.result.steps last ∧
        Returned body.checked.native.block source.outputRoles last body.checked.result.history := by
  exact core_flow artifact body.root
    (.planned (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root))
    128 .rootOrder (.whole prepared.source.body) (.root prepared.source.body) body.root.program request
    prepared.planned.plan _ body.checked.initial.ssa body.checked.native.block
    (body.checked.result,body.checked.receipts) body.checked.traversed

#print axioms step_flow
#print axioms core_flow
#print axioms original_body
end Qleisli.RuntimeNamedSourceFlow
