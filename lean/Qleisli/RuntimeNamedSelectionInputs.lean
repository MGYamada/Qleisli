import Qleisli.RuntimeNamedBodyFlow
import Qleisli.RuntimeNamedPrimitiveInputs

/-! Original input and return history for the actual named selection child.
The same common loop supplies the selection's complete input map, including
spectators and zero-width owners. No code equation or new acceptance is supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSelectionInputs
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody

def NodeInput (carriers : List Semantics.CarrierInterface.Owner)
    {dependencies program block} (node : @Node dependencies program block) : Prop :=
  match node with
  | .selection (codes := codes) .. =>
    RuntimeForestCode.carrierOwners codes.owners.before.bindings = carriers
  | _ => True

/-- Keep the original final source return, including any written reorder.
The actual selection after-map is the predecessor of that same return. -/
def NodeReturn (roles : List RuntimeOwnerMap.Owner) (returned : RuntimeStructuralAction.SourceState)
    {dependencies program block} (node : @Node dependencies program block) : Prop :=
  match node with
  | .selection (codes := codes) .. =>
    ∃ entry : RuntimeStructuralAction.SourceState,
      entry.bindings = codes.owners.before.bindings ∧
      RuntimeNamedSourceFlow.Returned block roles
        {entry with bindings := codes.owners.transport.after.bindings} returned
  | _ => True

/-- This actual run starts with the real ordered parameter construction.
Only a selection node receives a complete carrier assertion from NodeInput. -/
theorem child_source (artifact : Artifact) (root : Validity.Root)
    (execution : ExecutionMode artifact root) (fuel : Nat)
    {rootOwner rootName owner name : String}
    (source : SourceTypes.SourceRuntimeScope.Subject artifact.sources owner name)
    (path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name)
    (program : Semantics.Observation.Program) (request : Context)
    (plan : execution.queries.BodyData source request)
    (carriers : List Semantics.CarrierInterface.Owner) (assigned : RuntimeOwnerMap.Map)
    (inputRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings source.initialRoles carriers) assigned)
    (initial : RuntimeStructuralAction.SourceState) (sameBindings : initial.bindings = assigned)
    (ordinary : RuntimeOrdinaryBody.State) (block : RuntimeInterval.Block root.dependencies program)
    (result : BlockResult root.dependencies program block × List execution.Receipt)
    (read : RuntimeInterval.Computed (runBlockCore artifact root execution (fuel+1)
      .runtimeBody .localScope source path program request plan initial ordinary block) result)
    (node : Node root.dependencies program block) (emitted : result.1.steps = [.pure node]) :
    NodeInput carriers node ∧ NodeReturn source.outputRoles result.1.history node := by
  obtain ⟨ordered,orderedRead,last,flow,returned⟩ :=
    RuntimeNamedChildRuns.core_flow artifact root execution fuel .localScope source path program request plan initial ordinary block result read
  have roles := RuntimeNamedPrimitiveInputs.bindings_roles inputRead
  have sameMap := RuntimeNamedPrimitiveInputs.reordered_original roles ordered
    (by simpa only [sameBindings] using orderedRead)
  have sourceFlow := flow.source
  rw [emitted] at sourceFlow
  cases sourceFlow with
  | cons aligned rest =>
    cases rest
    cases node with
    | primitive _ _ => trivial
    | structural _ => trivial
    | basis | computed | certifiedComputed | workspace => trivial
    | named _ _ _ _ _ _ => trivial
    | operation _ _ _ _ _ _ _ _ _ _ => trivial
    | rectangularOperation _ => trivial
    | transform => trivial
    | selection frame selectorBits targetBits retained restricted inputCode outputCode labels expected logical equations codes layouts =>
      constructor
      · change RuntimeForestCode.carrierOwners codes.owners.before.bindings = carriers
        rw [← aligned.1,sameMap]
        exact RuntimeBoundaryOwnerEvidence.bindings_carriers inputRead
      · refine ⟨{initial with bindings := ordered.bindings},aligned.1,?_⟩
        rw [← aligned.2]
        exact returned

def NamedSource {dependencies program block} (step : @Step dependencies program block) : Prop :=
  match step with
  | .named (childHistory := history) _ _ body _ boundary _ (.cons (.pure node) .nil) =>
    NodeInput (RuntimeForestCode.carrierOwners boundary.input.ordered) node ∧
      NodeReturn (SourceTypes.SourceRuntimeScope.Subject.whole body).outputRoles history node
  | _ => True

/-- The child read and original argument binding belong to this exact named
call. No caller-provided equality of source or encoding maps is assumed. -/
theorem actual_named_source {artifact root execution fuel program block step}
    (call : @RuntimeNamedChildRuns.ChildRun artifact root execution
      (runBlockCore artifact root execution (fuel+1)) program block step) :
    NamedSource step := by
  cases call with
  | @named start count inputs caller before ordinary event scope body bodyRead
      rootOwner rootName path request plan assigned result receipts boundary beforeInput afterInput afterChild inputRead childRead =>
    cases emitted : result.steps with
    | nil => trivial
    | cons first rest =>
      cases rest with
      | cons second rest =>
        cases first
        case pure node => cases node <;> trivial
        all_goals trivial
      | nil =>
        cases first
        case pure node =>
          simp only [NamedSource,Steps.ofList,List.foldr_cons,List.foldr_nil]
          have actual := child_source artifact root execution fuel (.whole body) path scope.program request plan
            _ assigned ⟨beforeInput,afterInput,inputRead⟩ _ rfl scope.visible.ssa scope.prepared.block
            (result,receipts) ⟨afterInput,afterChild,childRead⟩ node emitted
          rw [RuntimeNamedPrimitiveInputs.named_input_carriers scope boundary] at actual
          exact actual
        all_goals trivial

def OccurrenceSource {dependencies program block step}
    (held : @RuntimeNamedThreeOccurrence.Middle dependencies program block step) : Prop :=
  match held with
  | .named (body := body) (childHistory := history) (boundary := boundary) node _ =>
    NodeInput (RuntimeForestCode.carrierOwners boundary.input.ordered) node ∧
      NodeReturn (SourceTypes.SourceRuntimeScope.Subject.whole body).outputRoles history node

theorem actual_occurrence_source {artifact root execution fuel program block step}
    (held : @RuntimeNamedThreeOccurrence.Middle root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (runBlockCore artifact root execution (fuel+1)) step) :
    OccurrenceSource held := by
  cases held
  exact actual_named_source call

/-- The real middle child of the original body supplies both source links.
No span coverage or matrix equality is introduced by this administrative law. -/
theorem original_middle_source {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps) :
    OccurrenceSource view.centerSelection :=
  actual_occurrence_source view.centerSelection
    (RuntimeNamedSourceFlow.original_child_runs body view).2.1

#print axioms child_source
#print axioms actual_named_source
#print axioms actual_occurrence_source
#print axioms original_middle_source
end Qleisli.RuntimeNamedSelectionInputs
