import QleisliKernel.Qirf.RuntimePreparedOperation
import QleisliKernel.Qirf.RuntimeStructuredRoot

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
      let block ← RuntimeInterval.prepare root.dependencies root.program
      let inputs ← RuntimeSourceBoundary.readInputs source.body block runtime.inputStorage
      let interval ← RuntimeInterval.check block.block position.start position.count
      let assigned := inputs.owners.bindings
      let initial ← RuntimeOwnerMap.checkBindings (assigned.map (·.owner)) interval.before assigned
      let moved ← RuntimeOwnerTransition.read interval initial.val.bindings
      let node ← NaturalAffine.witness (RuntimePureBody.operationNode block.block position event.inputOwners
        initial.val.bindings moved.after.bindings operation.val.subject.action)
      let finalBindings ← NaturalAffine.witness (RuntimeOwnerMap.order
        (SourceRuntimeValues.valueOwners source.body.checked.summary.value) moved.after.bindings)
      let boundary ← NaturalAffine.witness (RuntimeStructuredRoot.readBoundary source.body root block finalBindings.val runtime)
      if quantumOnly : runtime.inputRows = [[]] ∧ RuntimeFamily.inputValues runtime = [] ∧
          RuntimeFamily.outputValues runtime = [] then
        return ⟨operation.val,by with_reducible exact operation.property,covers,unchanged,
          block,inputs,interval,initial.val,initial.property,moved,node.val,by with_reducible exact node.property,
          finalBindings.val,by with_reducible exact finalBindings.property,quantumOnly,
          boundary.val,by with_reducible exact boundary.property⟩
      else throw .request
    else throw .request
  else throw .request

end QleisliKernel.Qirf.RuntimeMeaningCaller
