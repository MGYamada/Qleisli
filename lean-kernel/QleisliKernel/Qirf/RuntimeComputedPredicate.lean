import QleisliKernel.Qirf.SourceMeaningOrdinary
import QleisliKernel.Qirf.RuntimeInterval

/-! Reconstruct the physical predicate table from the original total
ordinary body and the exact nominal carrier. The separate use-body and
cleanup checks still determine whether a computed operation is valid.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeComputedPredicate
open QleisliKernel Finite SourceTypes

private def readTable {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller)
    (body : SourceRuntimeTrace.Body event.predicate.target.signature)
    (layout : Semantics.FiniteCarrier.Layout) : WorkM (List Nat) := do
  let [parameter] := body.checked.summary.parameterValues | throw .request
  let [(basis,.input 0)] := SourceRuntimeValues.ordinary parameter | throw .request
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields [⟨0,basis⟩,⟨0,event.input.basis⟩]+1)))
  guard (basis == event.input.basis) .request
  let length := 2^layout.bits
  let value := body.checked.summary.value
  exactWork (Exact.charge (32*(length+layout.labels.length*(SourceRuntimeValues.valueFields value+1)+1)))
  let entries ← layout.labels.zipIdx.foldlM (init := Array.replicate length 0) fun entries (label,ordinal) => do
    let assigned := SourceMeaningOrdinary.valuation [(0,ordinal)]
    let result ← lift ((SourceRuntimeOrdinary.extract assigned value).mapError fun _ => .request)
    let [.ordinary [.bit] result] := result | throw .request
    if valid : label < entries.size then
      return entries.set label result valid
    else throw .request
  return entries.toList

structure Source {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller) where
  body : SourceRuntimeTrace.Body event.predicate.target.signature
  original : RuntimeInterval.Computed (SourceRuntimeTrace.readComputedPredicateBody event) body
  layout : Semantics.FiniteCarrier.Layout
  originalLayout : RuntimeInterval.Computed (FiniteCarrier.read event.input.basis) layout
  table : List Nat
  computed : RuntimeInterval.Computed (readTable event body layout) table

/-- Only the canonical logical codes are evaluated. The physical table has a
fixed zero value at each padding code. -/
def readSource {sources caller} (event : SourceRuntimeContext.ComputedEvent sources caller) :
    WorkM (Source event) := do
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readComputedPredicateBody event)
  let layout ← NaturalAffine.witness (FiniteCarrier.read event.input.basis)
  let table ← NaturalAffine.witness (readTable event body.val layout.val)
  return ⟨body.val,by with_reducible exact body.property,layout.val,by with_reducible exact layout.property,
    table.val,by with_reducible exact table.property⟩

def checkTable {sources caller} {event : SourceRuntimeContext.ComputedEvent sources caller}
    (original : Source event) (table : List Nat) : WorkM (PLift (table = original.table)) := do
  exactWork (Exact.charge (8*(table.length+original.table.length+1)))
  if same : table = original.table then return ⟨same⟩
  else throw .equation

end QleisliKernel.Qirf.RuntimeComputedPredicate
