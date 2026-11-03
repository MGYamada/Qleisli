import QleisliKernel.Qirf.RuntimeCallerInterval
import QleisliKernel.Qirf.RuntimeNamedBoundary
import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimeNamedSelectionSource

/-! Original named-call transport around an independently checked selection.
The caller and callee keep their actual signatures and source coordinates. A
literal child scope excludes caller spectators; its canonical input roles are
derived only from the genuine original arguments. A checked child action is
required separately before the returned owner map can cross this boundary.
This bounded whole-call adapter grants no public gate or execution authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedSelectionBoundary
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.SourceRuntimeValues (valueOwners owners)
abbrev Position := SourceSequence.Position
abbrev Map := RuntimeOwnerMap.Map
abbrev SourceState := RuntimeStructuralAction.SourceState

structure Prepared {artifact : Artifact} {caller name : String}
    {signature : SourceRuntimeContext.Signature artifact.sources caller name}
    (body : @SourceRuntimeTrace.Body artifact.sources caller name signature)
    (root : Validity.Root) (position : Position) (runtime : RuntimeFamily.Request)
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller)
    (callee : SourceRuntimeTrace.Body event.target.signature) where
  originalCall : body.checked.events = [.named event]
  calleeRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) callee
  callerName : event.target.callerName = name
  callOffset : position.offset = event.call.calleeOffset
  visibleEffect : event.effect = .unitary
  covers : position.start = 0 ∧ position.count = root.program.operations.length
  ports : RuntimeCallerInterval.Ports body root position runtime
  before : SourceState
  beforeRead : before = ⟨ports.initial.bindings,
    (RuntimeSourceBoundary.summary body).parameterValues.flatMap valueOwners,
    (RuntimeSourceBoundary.summary body).nextOwner⟩
  completeSourceFrame : (event.held ++ event.inputOwners ++ owners event.remaining).Perm
    (before.bindings.map (·.owner))
  inputs : Map
  inputRead : RuntimeInterval.Computed (RuntimeOwnerMap.order event.inputOwners before.bindings) inputs
  frame : RuntimeCallInterval.Checked ports.block.block position.start position.count (inputs.map (·.port.token))
  initial : Map
  initialRead : RuntimeInterval.Computed (RuntimeSourceBoundary.bindings
    (callee.checked.summary.parameterValues.flatMap valueOwners)
    ((frame.selected.zip event.inputOwners).map fun (port,role) =>
      (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner))) initial

/-- Caller syntax locates the original call; it supplies no child equation.
The callee argument must retain the actual readNamedBody execution, including
its original static actuals, supplier context and result-value correspondence.
Source frames and caller-visible effects are checked before the local scope.
-/
def prepare {artifact : Artifact} {caller name : String}
    {signature : SourceRuntimeContext.Signature artifact.sources caller name}
    (body : @SourceRuntimeTrace.Body artifact.sources caller name signature)
    (root : Validity.Root) (position : Position) (runtime : RuntimeFamily.Request)
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller)
    (originalCall : body.checked.events = [.named event])
    (callee : SourceRuntimeTrace.Body event.target.signature)
    (calleeRead : RuntimeInterval.Computed (SourceRuntimeTrace.readNamedBody event) callee) :
    WorkM (Prepared body root position runtime event callee) := do
  let roles := event.held ++ event.inputOwners ++ owners event.remaining
  exactWork (Exact.charge (16*(position.offset+position.start+position.count+
    event.target.callerName.utf8ByteSize+name.utf8ByteSize+1)+
    64*(Raw.OwnerFlow.fields roles+(event.arguments.map SourceRuntimeValues.valueFields).sum+1)*
      (roles.length+1)^2))
  if valid : event.target.callerName = name ∧ position.offset = event.call.calleeOffset ∧
      event.effect = .unitary ∧ position.start = 0 ∧ position.count = root.program.operations.length then
    let ports ← RuntimeCallerInterval.read body root position runtime
    let before : SourceState := ⟨ports.initial.bindings,
      (RuntimeSourceBoundary.summary body).parameterValues.flatMap valueOwners,
      (RuntimeSourceBoundary.summary body).nextOwner⟩
    if completeSourceFrame : (event.held ++ event.inputOwners ++ owners event.remaining).Perm
        (before.bindings.map (·.owner)) then
      let inputs ← NaturalAffine.witness (RuntimeOwnerMap.order event.inputOwners before.bindings)
      let frame ← RuntimeCallInterval.read ports.block.block position.start position.count
        (inputs.val.map (·.port.token))
      let initial ← NaturalAffine.witness (RuntimeSourceBoundary.bindings
        (callee.checked.summary.parameterValues.flatMap valueOwners)
        ((frame.selected.zip event.inputOwners).map fun (port,role) =>
          (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)))
      return ⟨originalCall,calleeRead,valid.1,valid.2.1,valid.2.2.1,valid.2.2.2,ports,before,rfl,
        completeSourceFrame,inputs.val,by with_reducible exact inputs.property,frame,initial.val,
        by with_reducible exact initial.property⟩
    else throw .request
  else throw .request

/-- Reuse the same original source preparation which discovered all child
providers and Meaning references before the enclosing fresh graph read. -/
def prepareSource {artifact owner name arguments source request references}
    (named : @RuntimeNamedSelectionSource.Prepared artifact owner name arguments source request references)
    (root : Validity.Root) (runtime : RuntimeFamily.Request) :
    WorkM (Prepared source.body root named.position runtime named.event named.callee) :=
  prepare source.body root named.position runtime named.event named.original named.callee named.calleeRead

structure Checked {artifact owner name arguments source request references}
    (named : @RuntimeNamedSelectionSource.Prepared artifact owner name arguments source request references)
    (root : Validity.Root) (runtime : RuntimeFamily.Request)
    (prepared : Prepared source.body root named.position runtime named.event named.callee)
    (child : RuntimeSelectionMeaning.LocalChecked named.selection root prepared.frame.prepared prepared.initial) where
  childRead : RuntimeInterval.Computed
    (RuntimeSelectionMeaning.readAt named.selection root prepared.frame.prepared prepared.initial) child
  boundary : RuntimeNamedBoundary.Checked prepared.frame.interval (prepared.inputs.map (·.port.token))
    named.event prepared.before child.history child.retired child.value
  sameAfter : boundary.after.bindings.Perm prepared.ports.moved.after.bindings
  returned : RuntimeCallerInterval.Return prepared.ports

/-- Only an actual same-root checked selection may return through this call.
Its source-ordered canonical result is transported by the existing named
boundary, including every held/spectator owner and original value argument.
The complete caller result is then checked with the ordinary typed boundary.
All callee root-actual/header duties, including the distinct supplied-Op prefix,
and global catalogue duties remain obligations of the enclosing reader. Arm
provider occurrences cannot stand in for those prefix occurrences. This result
is not a public acceptance decision.
-/
def finish {artifact owner name arguments source request references}
    (named : @RuntimeNamedSelectionSource.Prepared artifact owner name arguments source request references)
    (root : Validity.Root) (runtime : RuntimeFamily.Request)
    (prepared : Prepared source.body root named.position runtime named.event named.callee)
    (child : RuntimeSelectionMeaning.LocalChecked named.selection root prepared.frame.prepared prepared.initial)
    (childRead : RuntimeInterval.Computed
      (RuntimeSelectionMeaning.readAt named.selection root prepared.frame.prepared prepared.initial) child) :
    WorkM (Checked named root runtime prepared child) := do
  let boundary ← RuntimeNamedBoundary.read prepared.frame.interval (prepared.inputs.map (·.port.token))
    named.event prepared.before child.history child.retired child.value
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (boundary.after.bindings.map (·.owner))+
    Raw.OwnerFlow.fields (prepared.ports.moved.after.bindings.map (·.owner))+1)*
    (boundary.after.bindings.length+prepared.ports.moved.after.bindings.length+1)^2))
  if sameAfter : boundary.after.bindings.Perm prepared.ports.moved.after.bindings then
    let returned ← RuntimeCallerInterval.finish prepared.ports
    return ⟨childRead,boundary,sameAfter,returned⟩
  else throw .request

/-- The existing named node receives the genuine checked child node. This
does not fabricate a common-body run, discharge separate original duties or
turn the local boundary into an execution handle. -/
def Checked.node {artifact owner name arguments source request references named root runtime prepared child}
    (checked : @Checked artifact owner name arguments source request references named root runtime prepared child) :
    RuntimePureBody.Node root.dependencies root.program prepared.ports.block.block :=
  .named named.event prepared.frame named.callee prepared.calleeRead prepared.frame.prepared.block
    checked.boundary (RuntimePureBody.Nodes.ofList [child.node])

end QleisliKernel.Qirf.RuntimeNamedSelectionBoundary
