import QleisliKernel.Qirf.RuntimeDutyInvocation
import QleisliKernel.Qirf.RuntimeNativeSubject

/-! Bind a selected native formal to the caller's original mixed argument and
the exact first simultaneous substitution in the original duty transport.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeFormalActual
open QleisliKernel Finite SourceTypes GenericOperation GenericOperationSubstitute GenericDutyQueue
open QleisliKernel.Semantics.SymbolicBasis (Parameter)

private def firstStep {sources app rest original result}
    (transport : @GenericDutyQueue.Transport sources (app :: rest) original result) :
    GenericOperationSubstitute.Checked app original :=
  match transport with | .step _ _ _ checked _ => checked

def substitution {sources catalogue record} {parent : @Invocation sources catalogue record}
    {app : ApplicationAt catalogue record} {target : GenericDutyQueue.Target app}
    (demand : Demand (.call parent app target)) :
    GenericOperationSubstitute.Checked app.original ⟨demand.source.original.subject,demand.source.original.suppliers⟩ :=
  firstStep (rest := parent.applications.reverse) (by
    rw [← Invocation.call_reverse parent app target]
    exact demand.transported.receipt)

structure Choice where
  owner : String
  name : String
  header : StaticHeaders.Formal
  position : Nat
  description : OperationDescription.Description

def readChoice {artifact catalogue context description graph implementations references prepared root requested checked cursor}
    (formal : @RuntimeNativeSubject.Formal artifact catalogue context description graph implementations references prepared root requested checked cursor) :
    WorkM Choice := do
  -- Selection checks reachability twice, filters the nodes and remaps each edge.
  let edges := description.nodes.foldl (fun count node => count + node.children.length) 0
  exactWork (Exact.charge (16*(description.nodes.length+edges+1)^2))
  let some actual := description.select formal.child.cursor.value.index | throw .request
  return ⟨formal.owner,formal.name,formal.header,formal.position,actual⟩

structure Supply {sources caller original}
    (event : SourceRuntimeContext.NamedEvent sources caller) (app : ApplicationSource sources)
    (transfer : GenericOperationSubstitute.Checked app original) (key : Parameter) (native : Choice) where
  step : Step app original
  atRoot : transfer.result.steps[original.description.root]? = some step
  rootIndex : step.index = original.description.root
  genericActual : ActualOperation sources
  selection : FormalSelection step key genericActual
  keyMatches : key = ⟨native.owner,native.name,native.header.ordinal⟩
  opPosition : app.operationActuals.findIdx (·.original == key) = native.position
  mixedHeader : app.target.header.formals[key.ordinal]? = some native.header
  source : SourceOperation.ActualSource event.target.actuals event.target.callerSignature.supply
  atPosition : event.target.operationActuals.sourceActuals[native.position]? = some source
  mixedIndex : source.index.val = key.ordinal
  argument : app.written.arguments[key.ordinal]? = some source.actual.argument
  formal : source.actual.formal = native.header ∧ source.name = native.header.name
  sameActual : source.checked.description = native.description

def readSupply {sources caller original}
    (event : SourceRuntimeContext.NamedEvent sources caller) (app : ApplicationSource sources)
    (transfer : GenericOperationSubstitute.Checked app original) (key : Parameter) (native : Choice) :
    WorkM (Supply event app transfer key native) := do
  exactWork (Exact.charge (16*(transfer.result.steps.length+app.target.header.formals.length+
    event.target.operationActuals.sourceActuals.length+SourceTrace.Meter.tokenFields app.tokens+
    SourceTrace.Meter.tokenFields app.target.envelope.occurrence.header+
    SourceTrace.Meter.tokenFields event.call.call.callee+app.written.arguments.length+
    (app.operationActuals.map fun a => a.original.moduleName.utf8ByteSize+a.original.declarationName.utf8ByteSize+1).sum+
    (app.operationActuals.length+1)*(key.moduleName.utf8ByteSize+key.declarationName.utf8ByteSize+1)+1)))
  match hstep : transfer.result.steps[original.description.root]?,
      found : app.operationActuals.find? (·.original == key), selected : event.target.operationActuals.sourceActuals[native.position]? with
  | some step,some actual,some source =>
    exactWork (Exact.charge (16*(RuntimeStructuredRoot.argumentFields ⟨[],[],[("",source.checked.description),("",native.description)]⟩+
      SourceTrace.Meter.tokenFields source.actual.argument.tokens+native.owner.utf8ByteSize+native.name.utf8ByteSize+
      native.header.name.utf8ByteSize+source.name.utf8ByteSize+1)))
    if rootIndex : step.index = original.description.root then
      if formal : step.node = .formal key then
        if valid : key = ⟨native.owner,native.name,native.header.ordinal⟩ ∧
            app.operationActuals.findIdx (·.original == key) = native.position ∧
            app.target.header.formals[key.ordinal]? = some native.header ∧ source.index.val = key.ordinal ∧
            app.written.arguments[key.ordinal]? = some source.actual.argument ∧
            source.actual.formal = native.header ∧ source.name = native.header.name ∧
            source.checked.description = native.description then
          return ⟨step,hstep,rootIndex,actual,step.formal_selection transfer.context formal found,valid.1,
            valid.2.1,valid.2.2.1,source,selected,valid.2.2.2.1,valid.2.2.2.2.1,
            ⟨valid.2.2.2.2.2.1,valid.2.2.2.2.2.2.1⟩,valid.2.2.2.2.2.2.2⟩
        else throw .request
      else throw .request
    else throw .request
  | _,_,_ => throw .request

def Evidence {sources catalogue record queue rootOwner rootName owner name path invocation}
    (binding : @RuntimeDutyInvocation.Binding sources catalogue queue rootOwner rootName owner name path record invocation)
    (demand : GenericDutyQueue.Demand invocation) (key : Parameter) (native : Choice) : Type :=
  match binding with
  | .root .. => Empty
  | .named (event := event) (application := app) _ _ => Supply event app.original (substitution demand) key native

def read {sources catalogue record queue rootOwner rootName owner name path invocation}
    (binding : @RuntimeDutyInvocation.Binding sources catalogue queue rootOwner rootName owner name path record invocation)
    (demand : GenericDutyQueue.Demand invocation) (key : Parameter) (native : Choice) :
    WorkM (Evidence binding demand key native) := by
  cases binding with
  | root => exact throw .request
  | named => exact readSupply _ _ (substitution demand) key native

end QleisliKernel.Qirf.RuntimeFormalActual
