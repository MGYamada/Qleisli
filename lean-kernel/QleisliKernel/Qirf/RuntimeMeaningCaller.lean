import QleisliKernel.Qirf.RuntimePreparedOperation
import QleisliKernel.Qirf.RuntimeCallerInterval

/-! A quantum-only caller consisting of a single direct checked operation.
Its original event, provider, Meaning and entire literal caller interval use
one graph root. Other source/catalogue duties and the runtime dispatcher
remain the enclosing checker's obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeMeaningCaller
open QleisliKernel Finite SourceTypes

structure Checked {artifact owner name arguments source request references order}
    (prepared : @RuntimePreparedOperation.Prepared artifact owner name arguments source request references)
    (fresh : RuntimePreparedOperation.Fresh prepared order) (runtime : RuntimeFamily.Request) where
  operation : RuntimePreparedOperation.Checked prepared fresh.root
  original : RuntimeInterval.Computed (RuntimePreparedOperation.read prepared fresh.root) operation
  covers : prepared.position.start = 0 ∧ prepared.position.count = fresh.root.program.operations.length
  unchangedOwners : prepared.event.operation.graph.root.input = prepared.event.operation.graph.root.output ∧
    prepared.event.allocated = [] ∧ prepared.event.consumed = []
  block : RuntimeInterval.Prepared fresh.root.dependencies fresh.root.program
  inputs : RuntimeSourceBoundary.Inputs source.body block runtime.inputStorage
  interval : RuntimeInterval.Checked block.block prepared.position.start prepared.position.count
  initial : RuntimeOwnerMap.Checked (inputs.owners.bindings.map (·.owner)) interval.before
  sameInitial : initial.bindings = inputs.owners.bindings
  moved : RuntimeOwnerTransition.Checked interval initial.bindings
  node : RuntimePureBody.Node fresh.root.dependencies fresh.root.program block.block
  callerAction : RuntimeInterval.Computed (RuntimePureBody.operationNode block.block prepared.position
    prepared.event.inputOwners initial.bindings moved.after.bindings operation.subject.action) node
  finalBindings : RuntimeOwnerMap.Map
  finalOrder : RuntimeInterval.Computed (RuntimeOwnerMap.order
    (SourceRuntimeValues.valueOwners source.body.checked.summary.value) moved.after.bindings) finalBindings
  quantumOnly : runtime.inputRows = [[]] ∧ RuntimeFamily.inputValues runtime = [] ∧
    RuntimeFamily.outputValues runtime = []
  boundary : RuntimeStructuredRoot.Boundary source.body fresh.root block runtime
  boundaryRead : RuntimeInterval.Computed
    (RuntimeStructuredRoot.readBoundary source.body fresh.root block finalBindings runtime) boundary

def read {artifact owner name arguments source request references order}
    (prepared : @RuntimePreparedOperation.Prepared artifact owner name arguments source request references)
    (fresh : RuntimePreparedOperation.Fresh prepared order) (runtime : RuntimeFamily.Request) :
    WorkM (Checked prepared fresh runtime) := do
  let position := prepared.position
  let event := prepared.event
  let root := fresh.root
  if covers : position.start = 0 ∧ position.count = root.program.operations.length then
    if unchanged : event.operation.graph.root.input = event.operation.graph.root.output ∧
        event.allocated = [] ∧ event.consumed = [] then
      let operation ← NaturalAffine.witness (RuntimePreparedOperation.read prepared root)
      let ports ← RuntimeCallerInterval.read source.body root position runtime
      let node ← NaturalAffine.witness (RuntimePureBody.operationNode ports.block.block position event.inputOwners
        ports.initial.bindings ports.moved.after.bindings operation.val.subject.action)
      let returned ← RuntimeCallerInterval.finish ports
      return ⟨operation.val,by with_reducible exact operation.property,covers,unchanged,
        ports.block,ports.inputs,ports.interval,ports.initial,ports.sameInitial,ports.moved,
        node.val,by with_reducible exact node.property,returned.finalBindings,returned.finalOrder,
        returned.quantumOnly,returned.boundary,returned.boundaryRead⟩
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeMeaningCaller
