import Qleisli.RuntimeNamedThreeFlow
import Qleisli.RuntimeBoundaryOwnerEvidence
import QleisliKernel.Qirf.RuntimeNamedPrimitiveOccurrence

/-! Input carriers of the actual original named primitive calls. Source owner
identities, complete basis trees and ordered physical ports follow the real
callee recursion and parameter binding. These administrative and input-code
laws do not compose whole-function output codes, actions or observing histories.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedPrimitiveInputs
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody
open RuntimeNamedChildRuns (ChildRun)

private theorem mapped_roles (roles : List Semantics.SourceOwners.Owner)
    (owners : List Semantics.CarrierInterface.Owner) (lengths : roles.length = owners.length)
    (assigned : RuntimeOwnerMap.Map) (work left : Nat)
    (ran : (((roles.zip owners).mapM fun pair =>
      if _same : pair.1.basis = pair.2.basis then
        pure (⟨pair.1,pair.2.port⟩ : RuntimeOwnerMap.Binding)
      else throw .request) : WorkM RuntimeOwnerMap.Map).run work = (.ok assigned,left)) :
    assigned.map (·.owner) = roles := by
  induction roles generalizing owners assigned work left with
  | nil =>
    have empty : owners = [] := List.eq_nil_of_length_eq_zero lengths.symm
    subst owners
    have same : assigned = [] := (pure_success _ _ _ _ ran).1
    subst assigned
    rfl
  | cons role roles ih =>
    cases owners with
    | nil => cases lengths
    | cons owner owners =>
      simp only [List.zip_cons_cons,List.mapM_cons] at ran
      obtain ⟨first,middle,head,rest⟩ := bind_success _ _ _ _ _ ran
      obtain ⟨tail,last,tailRead,returned⟩ := bind_success _ _ _ _ _ rest
      have same : assigned = first::tail := (pure_success _ _ _ _ returned).1
      subst assigned
      split at head
      · have sameFirst : first = ⟨role,owner.port⟩ := (pure_success _ _ _ _ head).1
        rw [sameFirst,List.map_cons,ih owners (Nat.succ.inj lengths) tail middle last tailRead]
      · cases head

theorem bindings_roles {roles owners assigned}
    (read : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings roles owners) assigned) :
    assigned.map (·.owner) = roles := by
  obtain ⟨work,left,ran⟩ := read
  unfold RuntimeSourceBoundary.bindings at ran
  obtain ⟨_,a,_charge,h⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨_,b,count,mapped⟩ := bind_success _ _ _ _ _ h
  exact mapped_roles roles owners (beq_iff_eq.mp (guard_success _ _ _ _ count).1) assigned b left mapped

theorem reordered_original {roles state assigned}
    (rolesRead : assigned.map RuntimeOwnerMap.Binding.owner = roles)
    (checked : RuntimeOwnerMap.Checked roles state)
    (read : RuntimeInterval.Computed (reordered roles state assigned) checked) :
    checked.bindings = assigned := by
  subst roles
  exact RuntimeNamedSourceFlow.reordered_self read

private theorem one_primitive {dependencies program block before after start count input output role kind}
    {action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (binding : RuntimePrimitiveSource.Checked action)
    (flow : RuntimeNamedSourceFlow.Run before [.pure (.primitive action binding)] after) :
    before = binding.history ∧ after = binding.after := by
  cases flow with
  | cons first rest =>
    cases rest
    exact first

/-- The real child input construction and recursion determine the primitive's
complete input carriers. Reordering the same original owner identities is
proved to preserve the assigned map; no encoding equation is assumed. -/
theorem child_primitive_carriers (artifact : Artifact) (root : Validity.Root)
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
    {start count input output role kind}
    (action : RuntimePrimitiveAction.Checked block start count input output role kind)
    (binding : RuntimePrimitiveSource.Checked action)
    (emitted : result.1.steps = [.pure (.primitive action binding)]) :
    RuntimeForestCode.carrierOwners binding.history.bindings = carriers := by
  obtain ⟨ordered,orderedRead,last,flow,_returned⟩ :=
    RuntimeNamedChildRuns.core_flow artifact root execution fuel .localScope source path program request plan initial ordinary block result read
  have roles := bindings_roles inputRead
  have sameMap := reordered_original roles ordered (by simpa only [sameBindings] using orderedRead)
  rw [emitted] at flow
  have starts := one_primitive binding flow.source
  have sameHistory := congrArg RuntimeStructuralAction.SourceState.bindings starts.1
  change ordered.bindings = binding.history.bindings at sameHistory
  rw [← sameHistory,sameMap]
  exact RuntimeBoundaryOwnerEvidence.bindings_carriers inputRead

theorem primitive_basis {dependencies program block start count input output role kind}
    {action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (binding : RuntimePrimitiveSource.Checked action) (carrier : Semantics.CarrierInterface.Owner)
    (same : RuntimeForestCode.carrierOwners binding.history.bindings = [carrier]) :
    role.basis = carrier.basis := by
  obtain ⟨work,left,ran⟩ := binding.inputPort.original
  unfold RuntimePrimitiveSource.rolePorts at ran
  obtain ⟨ordered,middle,orderRead,_returned⟩ := bind_success _ _ _ _ _ ran
  have facts := RuntimeSelectionPartition.order_values binding.frame.bindings [role] ordered ⟨work,middle,orderRead⟩
  cases ordered with
  | nil => cases facts.2
  | cons first rest =>
    have sameOwner : first.owner = role := (List.cons.inj facts.2).1
    have present : (⟨first.port,first.owner.basis⟩ : Semantics.CarrierInterface.Owner) ∈
        RuntimeForestCode.carrierOwners binding.frame.bindings :=
      List.mem_map.mpr ⟨first,facts.1 List.mem_cons_self,rfl⟩
    have frameCarriers := (congrArg RuntimeForestCode.carrierOwners binding.sameHistory).trans same
    rw [frameCarriers] at present
    have sameCarrier := List.mem_singleton.mp present
    simpa only [sameOwner] using congrArg Semantics.CarrierInterface.Owner.basis sameCarrier

private theorem zipped_carriers (bindings : RuntimeOwnerMap.Map) :
    ((bindings.map (·.port)).zip (bindings.map (·.owner))).map
        (fun (port,role) => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) =
      RuntimeForestCode.carrierOwners bindings := by
  induction bindings with
  | nil => rfl
  | cons first rest ih =>
    simpa only [List.map_cons,List.zip_cons_cons,RuntimeForestCode.carrierOwners,List.cons.injEq,true_and] using ih

theorem named_input_carriers
    {dependencies program block start count inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value) :
    (scope.selected.zip event.inputOwners).map
        (fun (port,role) => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) =
      RuntimeForestCode.carrierOwners boundary.input.ordered := by
  have ordered := RuntimeSelectionPartition.order_values before.bindings event.inputOwners
    boundary.input.ordered boundary.input.orderRead
  rw [RuntimeNamedFrameAxes.mixed_bound_ports scope boundary,← ordered.2]
  exact zipped_carriers boundary.input.ordered

/-- A property of the actual stored named child: when it is exactly one
primitive, its source history retains the caller's full ordered input carriers.
Other child shapes acquire no assertion from this projection. -/
def NamedPrimitiveInput {dependencies program block} (step : Step dependencies program block) : Prop :=
  match step with
  | .named _ _ _ _ boundary _ (.cons (.pure (.primitive _ binding)) .nil) =>
    RuntimeForestCode.carrierOwners binding.history.bindings =
      RuntimeForestCode.carrierOwners boundary.input.ordered
  | _ => True

theorem actual_named_input {artifact root execution fuel program block step}
    (call : @ChildRun artifact root execution (runBlockCore artifact root execution (fuel+1)) program block step) :
    NamedPrimitiveInput step := by
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
          cases node
          case primitive action binding =>
            simp only [NamedPrimitiveInput,Steps.ofList,List.foldr_cons,List.foldr_nil]
            have actual := child_primitive_carriers artifact root execution fuel (.whole body) path scope.program request plan
              _ assigned ⟨beforeInput,afterInput,inputRead⟩ _ rfl scope.visible.ssa scope.prepared.block
              (result,receipts) ⟨afterInput,afterChild,childRead⟩ action binding emitted
            exact actual.trans (named_input_carriers scope boundary)
          all_goals trivial
        all_goals trivial

def OccurrenceInput {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) : Prop :=
  match held with
  | .named (role := role) (boundary := boundary) (action := action) _ _ =>
    action.interval.selected.map (fun port => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) =
      RuntimeForestCode.carrierOwners boundary.input.ordered

theorem occurrence_input {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (aligned : NamedPrimitiveInput step) : OccurrenceInput held := by
  cases held with
  | named original bound =>
    have basis := primitive_basis original ⟨bound.binding.port,bound.binding.owner.basis⟩
      (by simpa only [NamedPrimitiveInput,bound.singleton,RuntimeForestCode.carrierOwners,List.map_singleton] using aligned)
    simp only [OccurrenceInput,bound.entry,basis,bound.singleton,RuntimeForestCode.carrierOwners,List.map_singleton]

theorem actual_occurrence_input {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : ChildRun artifact root execution (runBlockCore artifact root execution (fuel+1)) step) :
    OccurrenceInput held := occurrence_input held (actual_named_input call)

/-- The actual original pre/post calls now supply their primitive input-code
carrier equalities. They retain full type trees and ports, independently of
equal widths, and require no assumed matrix equation or inverse capability. -/
theorem original_pre_post_inputs {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps) :
    OccurrenceInput view.prePrimitive ∧ OccurrenceInput view.postPrimitive := by
  obtain ⟨pre,_center,post⟩ := RuntimeNamedSourceFlow.original_child_runs body view
  exact ⟨actual_occurrence_input view.prePrimitive pre,actual_occurrence_input view.postPrimitive post⟩

#print axioms original_pre_post_inputs
#print axioms actual_named_input
#print axioms child_primitive_carriers
end Qleisli.RuntimeNamedPrimitiveInputs
