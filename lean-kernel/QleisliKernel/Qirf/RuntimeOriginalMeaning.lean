import QleisliKernel.Qirf.RuntimeSourceOperationMarkers
import QleisliKernel.SourceTypes.GenericOperation

/-! Check the Meaning from the original queue duty using the reference bodies
of the written native assertion on its already validated dependency root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOriginalMeaning
open QleisliKernel Finite SourceTypes

structure Checked {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (asserted : @RuntimeSourceOperationMarkers.Assertion artifact catalogue context description graph implementations references prepared
      root requested caller scope checked marker target) (duty : GenericOperation.Duty artifact.sources) where
  request : SourceMeaning.Request artifact.sources
  original : duty.requirement = .meaning request
  written : RuntimeSourceOperationMarkers.MeaningOriginal marker request
  meaning : SourceMeaningAction.Prepared artifact catalogue request.meaning
  preparedRead : RuntimeInterval.Computed
    (SourceMeaningAction.prepare artifact catalogue request.meaning asserted.requirement.meaning.requests) meaning
  sameRows : meaning.rows = asserted.requirement.meaning.rows
  sameRoots : meaning.roots = asserted.requirement.meaning.roots
  specification : SourceMeaningAction.Checked meaning root
  evaluated : RuntimeInterval.Computed (SourceMeaningAction.read meaning root) specification
  input : asserted.child.input = request.meaning.graph.input
  output : asserted.child.output = request.meaning.graph.output
  action : asserted.child.action = specification.action

def read {artifact catalogue context description graph implementations references prepared root requested caller scope checked marker target}
    (asserted : @RuntimeSourceOperationMarkers.Assertion artifact catalogue context description graph implementations references prepared
      root requested caller scope checked marker target) (duty : GenericOperation.Duty artifact.sources) :
    WorkM (Checked asserted duty) := do
  match original : duty.requirement with
  | .access _ => throw .request
  | .meaning request =>
    let written ← RuntimeSourceOperationMarkers.readMeaningOriginal marker request
    let native := asserted.requirement.meaning
    let meaning ← NaturalAffine.witness (SourceMeaningAction.prepare artifact catalogue request.meaning native.requests)
    let rows := meaning.val.rows
    let roots := meaning.val.roots
    let rowBytes (values : List SourceRows.Row) := values.foldl (fun n row => n+row.1.utf8ByteSize+row.2.utf8ByteSize+1) 0
    exactWork (Exact.charge (16*(rowBytes rows+rowBytes native.rows+roots.length+native.roots.length+1)))
    if same : rows = native.rows ∧ roots = native.roots then
      let specification ← NaturalAffine.witness (SourceMeaningAction.read meaning.val root)
      exactWork (Exact.charge (16*(Raw.OwnerFlow.fields [⟨0,asserted.child.input⟩,⟨0,asserted.child.output⟩,
        ⟨0,request.meaning.graph.input⟩,⟨0,request.meaning.graph.output⟩]+1)))
      if ports : asserted.child.input = request.meaning.graph.input ∧ asserted.child.output = request.meaning.graph.output then
        exactWork (Exact.charge (asserted.child.action.entries.length+specification.val.action.entries.length+1))
        if action : asserted.child.action = specification.val.action then
          return ⟨request,original,written,meaning.val,by with_reducible exact meaning.property,same.1,same.2,
            specification.val,by with_reducible exact specification.property,ports.1,ports.2,action⟩
        else throw .equation
      else throw .request
    else throw .request

end QleisliKernel.Qirf.RuntimeOriginalMeaning
