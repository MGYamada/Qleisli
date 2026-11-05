import QleisliKernel.Qirf.RuntimeClosedProvider
import QleisliKernel.Qirf.SourceDutyProviderFresh

/-! Attach a closed, explicitly applied Basis/Nat provider at the root of a
written arm operand to the native terminal already reached by its original
formal supply. The source occurrence and the native body keep their original
arguments, dependency graph, ports, effect and action.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeAppliedProvider
open QleisliKernel Finite SourceTypes
open RuntimeInterval (Computed)
open RuntimeClosedProvider (Native)
open RuntimeNativeSubject (Cursor)

private def directEvent {sources caller} : SourceRuntimeContext.Event sources caller → Bool
  | .phase _ | .primitive _ => true
  | _ => false

/-- There is exactly one original node, with explicit scalar actuals and no
original Op child or local path premise. Non-leaves keep their full tree. -/
def singleton (description : GenericOperation.Description) : Bool :=
  match description.root,description.nodes with
  | 0,[.provider _ _ bases naturals [] []] => !bases.isEmpty || !naturals.isEmpty
  | _,_ => false

section
variable {artifact catalogue record invocation context description graph implementations references prepared root requested checked}
    (demand : @GenericDutyQueue.Demand artifact.sources catalogue record invocation)
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked)

structure Checked where
  leaf : singleton demand.transported.subject.description = true
  view : SourceDutySlots.View demand.transported.subject.description
  atRoot : view.index = demand.transported.subject.description.root ∧ view.path = []
  provider : SourceDutySlots.Provider demand view
  applied : SourceDutyProviderApplied.Checked provider
  sourceRead : Computed (SourceDutyProviderApplied.read provider) applied
  slot : Native cursor
  identity : SourceDutyProviderFresh.Identity provider slot.provider.header.original.supplied.provider
  supplier : slot.provider.header.original.supplied.context = .source provider.supplier.origin.state.owner
  noPremises : applied.application.target.header.premises.isEmpty = true ∧
    applied.application.target.header.access.isEmpty = true
  nativeNode : cursor.node = .provider provider.owner provider.name provider.bases provider.naturals []
  direct : slot.provider.header.original.body.checked.events.all directEvent = true
  noMeaning : cursor.binding.record.occurrence.result.requirements.isEmpty = true
  effect : cursor.binding.record.occurrence.result.effect = provider.expectedEffect
  ports : provider.signature.inputs = [cursor.value.input] ∧ provider.signature.outputs = [cursor.value.output]
  paths : RuntimeClosedProvider.covers cursor.binding.record.occurrence.result.paths cursor.binding.record.demand = true
  action : cursor.value.action = slot.actual.action

private def read (leaf : singleton demand.transported.subject.description = true) : WorkM (Checked demand cursor) := do
  let views ← SourceDutySlots.readViews demand.transported.subject.description ⟨false,false,false⟩
  let [view] := views | throw .request
  if atRoot : view.index = demand.transported.subject.description.root ∧ view.path = [] then
    match status : view.status with
    | .conditional .. => throw .request
    | .closed closed =>
      let provider ← SourceDutySlots.readProvider demand view closed status
      let applied ← NaturalAffine.witness (SourceDutyProviderApplied.read provider)
      let slot ← RuntimeClosedProvider.nativeAt cursor
      let header := slot.provider.header.original
      let identity ← SourceDutyProviderFresh.readIdentity provider header.supplied.provider
      let original := applied.val.application.target.header
      let cells := RuntimeStructuredRoot.argumentFields ⟨provider.bases,provider.naturals,[]⟩ +
        RuntimeStructuredRoot.argumentFields {operations := [("",⟨[cursor.node],0⟩)]}
      let names := provider.owner.utf8ByteSize + provider.name.utf8ByteSize +
        provider.supplier.origin.state.owner.utf8ByteSize +
        (match header.supplied.context with | .external => 0 | .source name => name.utf8ByteSize)
      exactWork (Exact.charge (32*(cells+names+header.body.checked.events.length+
        Raw.OwnerFlow.fields (((provider.signature.inputs ++ provider.signature.outputs ++
          [cursor.value.input,cursor.value.output]).zipIdx).map fun (b,i) => ⟨i,b⟩)+1)))
      let metadata := cursor.binding.record.occurrence.result
      if sourceMatch : header.supplied.context = .source provider.supplier.origin.state.owner ∧
          (original.premises.isEmpty = true ∧ original.access.isEmpty = true) ∧
          cursor.node = .provider provider.owner provider.name provider.bases provider.naturals [] then
        if nativeMatch : header.body.checked.events.all directEvent = true ∧ metadata.requirements.isEmpty = true ∧
            metadata.effect = provider.expectedEffect ∧
            (provider.signature.inputs = [cursor.value.input] ∧ provider.signature.outputs = [cursor.value.output]) ∧
            RuntimeClosedProvider.covers metadata.paths cursor.binding.record.demand = true then
          let ⟨supplier,premises,node⟩ := sourceMatch
          let ⟨body,noMeaning,effect,ports,paths⟩ := nativeMatch
          exactWork (Exact.charge (cursor.value.action.entries.length+slot.actual.action.entries.length+1))
          if action : cursor.value.action = slot.actual.action then
            return ⟨leaf,view,atRoot,provider,applied.val,by with_reducible exact applied.property,
              slot,identity,supplier,premises,node,body,noMeaning,effect,ports,paths,action⟩
          else throw .equation
        else throw .request
      else throw .request
  else throw .request

/-- Unsupported source/slot correlations retain a residual. A failed
comparison spends its actual work. Arithmetic, equation and capacity failures
propagate and no other source candidate is tried. -/
def read? : WorkM (Option (Checked demand cursor)) := fun work =>
  if leaf : singleton demand.transported.subject.description = true then
    let (value,left) := (read demand cursor leaf).run work
    match value with
    | .ok proof => (.ok (some proof),left)
    | .error .request => (.ok none,left)
    | .error error => (.error error,left)
  else (.ok none,work)
end
end QleisliKernel.Qirf.RuntimeAppliedProvider
