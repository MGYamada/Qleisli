import QleisliKernel.Qirf.RuntimeDutyInvocation
import QleisliKernel.Qirf.RuntimeNativeSubject

/-! Bind a selected native formal to the caller's original mixed argument and
the exact first simultaneous substitution in the original duty transport.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeFormalActual
open QleisliKernel Finite SourceTypes GenericOperation GenericOperationSubstitute GenericDutyQueue
open QleisliKernel.Semantics.SymbolicBasis (Parameter)

/-- Both projections come from the same stored transport constructor. The
remaining calls start with the entire subject returned by the first reader. -/
structure TransportStep {sources} (app : ApplicationSource sources) (rest : List (ApplicationSource sources))
    (original result : GenericOperationSubstitute.Subject sources) where
  transfer : GenericOperationSubstitute.Checked app original
  tail : GenericDutyQueue.Transport rest transfer.result.subject result

def splitTransport {sources app rest original result}
    (transport : @GenericDutyQueue.Transport sources (app :: rest) original result) :
    TransportStep app rest original result :=
  match transport with | .step _ _ _ checked tail => ⟨checked,tail⟩

theorem splitTransport_original {sources app rest original result}
    (transport : @GenericDutyQueue.Transport sources (app :: rest) original result) :
    GenericDutyQueue.Transport.step app rest original (splitTransport transport).transfer
      (splitTransport transport).tail = transport := by
  cases transport
  rfl

def splitInvocation {sources catalogue record original result} (parent : @Invocation sources catalogue record)
    (app : ApplicationAt catalogue record) (target : GenericDutyQueue.Target app)
    (transport : GenericDutyQueue.Transport (Invocation.call parent app target).applications.reverse original result) :
    TransportStep app.original parent.applications.reverse original result :=
  splitTransport (Invocation.call_reverse parent app target ▸ transport)

def substitution {sources catalogue record} {parent : @Invocation sources catalogue record}
    {app : ApplicationAt catalogue record} {target : GenericDutyQueue.Target app}
    (demand : Demand (.call parent app target)) :
    GenericOperationSubstitute.Checked app.original ⟨demand.source.original.subject,demand.source.original.suppliers⟩ :=
  (splitInvocation parent app target demand.transported.receipt).transfer

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

structure SupplyAt {sources caller original}
    (event : SourceRuntimeContext.NamedEvent sources caller) (app : ApplicationSource sources)
    (transfer : GenericOperationSubstitute.Checked app original) (index : Nat) (key : Parameter) (native : Choice) where
  step : Step app original
  atIndex : transfer.result.steps[index]? = some step
  stepIndex : step.index = index
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

structure Supply {sources caller original}
    (event : SourceRuntimeContext.NamedEvent sources caller) (app : ApplicationSource sources)
    (transfer : GenericOperationSubstitute.Checked app original) (key : Parameter) (native : Choice)
    extends SupplyAt event app transfer original.description.root key native

theorem Supply.atRoot {sources caller original event app transfer key native}
    (supply : @Supply sources caller original event app transfer key native) :
    transfer.result.steps[original.description.root]? = some supply.step := supply.atIndex

theorem Supply.rootIndex {sources caller original event app transfer key native}
    (supply : @Supply sources caller original event app transfer key native) :
    supply.step.index = original.description.root := supply.stepIndex

theorem SupplyAt.returnedStep {sources caller original event app transfer index key native}
    (supply : @SupplyAt sources caller original event app transfer index key native) :
    supply.step.result.subject = ⟨supply.genericActual.subject,supply.genericActual.suppliers⟩ :=
  congrArg NodeResult.subject supply.selection.returned

/-- The next outer call receives exactly the selected caller actual, with
its supplier origins intact. This uses the returned root of the actual fold. -/
theorem Supply.returned {sources caller original event app transfer key native}
    (supply : @Supply sources caller original event app transfer key native) :
    transfer.result.subject = ⟨supply.genericActual.subject,supply.genericActual.suppliers⟩ := by
  have root := transfer.result.returned
  rw [supply.atIndex,Option.map_some] at root
  exact (Option.some.inj root).symm.trans supply.toSupplyAt.returnedStep

def readSupplyAt {sources caller original}
    (event : SourceRuntimeContext.NamedEvent sources caller) (app : ApplicationSource sources)
    (transfer : GenericOperationSubstitute.Checked app original) (index : Nat) (key : Parameter) (native : Choice) :
    WorkM (SupplyAt event app transfer index key native) := do
  exactWork (Exact.charge (16*(transfer.result.steps.length+app.target.header.formals.length+
    event.target.operationActuals.sourceActuals.length+SourceTrace.Meter.tokenFields app.tokens+
    SourceTrace.Meter.tokenFields app.target.envelope.occurrence.header+
    SourceTrace.Meter.tokenFields event.call.call.callee+app.written.arguments.length+
    (app.operationActuals.map fun a => a.original.moduleName.utf8ByteSize+a.original.declarationName.utf8ByteSize+1).sum+
    (app.operationActuals.length+1)*(key.moduleName.utf8ByteSize+key.declarationName.utf8ByteSize+1)+1)))
  match hstep : transfer.result.steps[index]?,
      found : app.operationActuals.find? (·.original == key), selected : event.target.operationActuals.sourceActuals[native.position]? with
  | some step,some actual,some source =>
    exactWork (Exact.charge (16*(RuntimeStructuredRoot.argumentFields ⟨[],[],[("",source.checked.description),("",native.description)]⟩+
      SourceTrace.Meter.tokenFields source.actual.argument.tokens+native.owner.utf8ByteSize+native.name.utf8ByteSize+
      native.header.name.utf8ByteSize+source.name.utf8ByteSize+1)))
    if stepIndex : step.index = index then
      if formal : step.node = .formal key then
        if valid : key = ⟨native.owner,native.name,native.header.ordinal⟩ ∧
            app.operationActuals.findIdx (·.original == key) = native.position ∧
            app.target.header.formals[key.ordinal]? = some native.header ∧ source.index.val = key.ordinal ∧
            app.written.arguments[key.ordinal]? = some source.actual.argument ∧
            source.actual.formal = native.header ∧ source.name = native.header.name ∧
            source.checked.description = native.description then
          return ⟨step,hstep,stepIndex,actual,step.formal_selection transfer.context formal found,valid.1,
            valid.2.1,valid.2.2.1,source,selected,valid.2.2.2.1,valid.2.2.2.2.1,
            ⟨valid.2.2.2.2.2.1,valid.2.2.2.2.2.2.1⟩,valid.2.2.2.2.2.2.2⟩
        else throw .request
      else throw .request
    else throw .request
  | _,_,_ => throw .request

def readSupply {sources caller original}
    (event : SourceRuntimeContext.NamedEvent sources caller) (app : ApplicationSource sources)
    (transfer : GenericOperationSubstitute.Checked app original) (key : Parameter) (native : Choice) :
    WorkM (Supply event app transfer key native) := do
  return ⟨← readSupplyAt event app transfer original.description.root key native⟩

end QleisliKernel.Qirf.RuntimeFormalActual
