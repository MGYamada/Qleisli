import QleisliKernel.SourceTypes.RuntimeGenericAnalysis
import QleisliKernel.SourceTypes.GenericTypeTrace

/-! Exact original self-call decrease receipts. Closed specialization descent
is a separate check and cannot replace the original guarded affine proof.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRecursion
open Finite

def Aligned {sources owner name targetOwner targetName}
    (original : OrdinarySignature.Original sources owner name) (scope : List String)
    (callee : List LocatedToken) (target : OrdinarySignature.Original sources targetOwner targetName)
    (receipt : GenericTypeTrace.Recursion sources) : Prop :=
  receipt.state.owner = owner ∧ receipt.state.name = name ∧
  receipt.state.prepared.original.envelope.source = original.source ∧
  receipt.state.prepared.original.envelope.declaration = original.declaration ∧
  receipt.scope = scope ∧ receipt.callee = callee ∧
  receipt.owner = targetOwner ∧ receipt.name = targetName ∧
  receipt.target.envelope.source = target.source ∧
  receipt.target.envelope.declaration = target.declaration ∧
  receipt.target.envelope.occurrence.header = target.occurrence.header ∧
  receipt.target.envelope.occurrence.body = target.occurrence.body ∧
  receipt.target.envelope.occurrence.openBrace = target.occurrence.openBrace ∧
  receipt.target.envelope.occurrence.closeBrace = target.occurrence.closeBrace

instance {sources owner name targetOwner targetName original scope callee target receipt} :
    Decidable (@Aligned sources owner name targetOwner targetName original scope callee target receipt) := by
  unfold Aligned
  infer_instance

structure Matched {sources owner name targetOwner targetName}
    {original : OrdinarySignature.Original sources owner name}
    (generic : RuntimeGenericAnalysis.Checked original) (scope : List String) (callee : List LocatedToken)
    (target : OrdinarySignature.Original sources targetOwner targetName) where
  receipt : GenericTypeTrace.Recursion sources
  originalMember : receipt ∈ generic.recursiveCalls
  aligned : Aligned original scope callee target receipt

inductive Checked {sources owner name targetOwner targetName}
    {original : OrdinarySignature.Original sources owner name}
    (generic : RuntimeGenericAnalysis.Checked original) (scope : List String) (callee : List LocatedToken)
    (target : OrdinarySignature.Original sources targetOwner targetName) where
  | other (different : (owner,name) ≠ (targetOwner,targetName))
  | self (runtime : original.parsedHeader.ordinaryOnly = false)
      (receipt : Matched generic scope callee target)

def read {sources owner name targetOwner targetName}
    {original : OrdinarySignature.Original sources owner name}
    (generic : RuntimeGenericAnalysis.Checked original) (scope : List String) (callee : List LocatedToken)
    (target : OrdinarySignature.Original sources targetOwner targetName) :
    WorkM (Checked generic scope callee target) := do
  if same : (owner,name) = (targetOwner,targetName) then
    if runtime : original.parsedHeader.ordinaryOnly = false then
      let found ← generic.recursiveCalls.attach.foldlM (fun found candidate => do
        match found with
        | some _ => pure found
        | none =>
          exactWork (Exact.charge (32*(original.source.utf8ByteSize+target.source.utf8ByteSize+
            (scope.map String.utf8ByteSize).sum+
            (callee.map fun token => token.text.utf8ByteSize+4).sum+1)))
          if aligned : Aligned original scope callee target candidate.val then
            pure (some (⟨candidate.val,candidate.property,aligned⟩ : Matched generic scope callee target))
          else pure none) (none : Option (Matched generic scope callee target))
      let some receipt := found | throw .request
      return .self runtime receipt
    else throw .request
  else return .other same

end QleisliKernel.SourceTypes.SourceRecursion
