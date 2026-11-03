import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.Qirf.RuntimeStructuredRoot

/-! Original input and output storage for a quantum caller's checked interval.
The caller supplies the separately verified source operation or selection.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeCallerInterval
open QleisliKernel Finite SourceTypes

structure Ports {sources owner name signature} (body : @SourceRuntimeTrace.Body sources owner name signature)
    (root : Validity.Root) (position : SourceSequence.Position) (runtime : RuntimeFamily.Request) where
  block : RuntimeInterval.Prepared root.dependencies root.program
  inputs : RuntimeSourceBoundary.Inputs body block runtime.inputStorage
  interval : RuntimeInterval.Checked block.block position.start position.count
  initial : RuntimeOwnerMap.Checked (inputs.owners.bindings.map (·.owner)) interval.before
  sameInitial : initial.bindings = inputs.owners.bindings
  moved : RuntimeOwnerTransition.Checked interval initial.bindings

def read {sources owner name signature} (body : @SourceRuntimeTrace.Body sources owner name signature)
    (root : Validity.Root) (position : SourceSequence.Position) (runtime : RuntimeFamily.Request) :
    WorkM (Ports body root position runtime) := do
  let block ← RuntimeInterval.prepare root.dependencies root.program
  let inputs ← RuntimeSourceBoundary.readInputs body block runtime.inputStorage
  let interval ← RuntimeInterval.check block.block position.start position.count
  let assigned := inputs.owners.bindings
  let initial ← RuntimeOwnerMap.checkBindings (assigned.map (·.owner)) interval.before assigned
  let moved ← RuntimeOwnerTransition.read interval initial.val.bindings
  return ⟨block,inputs,interval,initial.val,initial.property,moved⟩

structure Return {sources owner name signature body root position runtime}
    (ports : @Ports sources owner name signature body root position runtime) where
  finalBindings : RuntimeOwnerMap.Map
  finalOrder : RuntimeInterval.Computed (RuntimeOwnerMap.order
    (SourceRuntimeValues.valueOwners body.checked.summary.value) ports.moved.after.bindings) finalBindings
  quantumOnly : runtime.inputRows = [[]] ∧ RuntimeFamily.inputValues runtime = [] ∧ RuntimeFamily.outputValues runtime = []
  boundary : RuntimeStructuredRoot.Boundary body root ports.block runtime
  boundaryRead : RuntimeInterval.Computed (RuntimeStructuredRoot.readBoundary body root ports.block finalBindings runtime) boundary

def finish {sources owner name signature body root position runtime}
    (ports : @Ports sources owner name signature body root position runtime) : WorkM (Return ports) := do
  let finalBindings ← NaturalAffine.witness (RuntimeOwnerMap.order
    (SourceRuntimeValues.valueOwners body.checked.summary.value) ports.moved.after.bindings)
  let boundary ← NaturalAffine.witness (RuntimeStructuredRoot.readBoundary body root ports.block finalBindings.val runtime)
  if quantumOnly : runtime.inputRows = [[]] ∧ RuntimeFamily.inputValues runtime = [] ∧
      RuntimeFamily.outputValues runtime = [] then
    return ⟨finalBindings.val,by with_reducible exact finalBindings.property,quantumOnly,
      boundary.val,by with_reducible exact boundary.property⟩
  else throw .request

end QleisliKernel.Qirf.RuntimeCallerInterval
