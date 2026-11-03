import QleisliKernel.Qirf.RawTrace
import QleisliKernel.Qirf.SourceArmExecution

/-! Shared original-body checking against an actual realized arm program.
This continuation is not wired into source/transport admission. Bodies with
selections still need their recursive arm equations; general calls retain the
common source reader's unfinished scope. No handle or capability is issued.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceArmBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Qirf.PureInterval

def noSelections {sources owner} (events : List (SourceTypes.SourceTrace.Event sources owner)) : Bool :=
  events.all fun event => match event with
    | .primitive _ | .phase _ => true
    | .selection .. | .named _ | .operation _ => false

structure Checked {artifact order extra roots owner selector target profile}
    (root : Witness (Validity.checkRootFromRoots artifact order extra roots profile))
    (bound : SourceArm.Bound artifact owner selector target)
    (realized : SourceArm.Realized artifact root.val.receipts bound)
    (positions : List SourceSequence.Position) where
  source : Witness (SourceTypes.SourceTrace.readWithSignature bound.signature)
  completeActions : noSelections source.val.checked.result.events = true
  body : Witness (RawTrace.check source.val.checked root.val.dependencies
    realized.receipt.input.implementation positions)

/-- Check the original bound declaration and actual entry implementation under
the same root dependencies. No source text, signature, body or receipt is
reconstructed, and an unsupported source action refuses without fallback. -/
def check {artifact order extra roots owner selector target profile}
    (root : Witness (Validity.checkRootFromRoots artifact order extra roots profile))
    (bound : SourceArm.Bound artifact owner selector target)
    (realized : SourceArm.Realized artifact root.val.receipts bound)
    (positions : List SourceSequence.Position) : WorkM (Checked root bound realized positions) := do
  let source ← SourceTypes.NaturalAffine.witness
    (SourceTypes.SourceTrace.readWithSignature bound.signature)
  exactWork (Exact.charge (source.val.checked.result.events.length+1))
  if completeActions : noSelections source.val.checked.result.events = true then
    let body ← SourceTypes.NaturalAffine.witness (RawTrace.check source.val.checked
      root.val.dependencies realized.receipt.input.implementation positions)
    return ⟨source,completeActions,body⟩
  else throw .request

theorem Checked.originalSignature {artifact order extra roots owner selector target profile}
    {root : Witness (Validity.checkRootFromRoots artifact order extra roots profile)}
    {bound : SourceArm.Bound artifact owner selector target}
    {realized : SourceArm.Realized artifact root.val.receipts bound} {positions}
    (checked : Checked root bound realized positions) :
    checked.source.val.checked.signature = bound.signature :=
  checked.source.val.originalSignature

end QleisliKernel.Qirf.SourceArmBody
