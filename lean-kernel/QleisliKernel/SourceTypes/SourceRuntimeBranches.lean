import QleisliKernel.SourceTypes.SourceRuntimeValues

/-! Exact ordinary-block exit and quantum phi metadata. A name alone cannot
restore a moved outer owner: original parameter/binder origins stay distinct.
No source owner permutation or producer-selected branch is guessed here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeBranches
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues

private def sameBinding (first second : Cell) : Bool :=
  first.name == second.name && first.origin == second.origin

/-- Local ordinary shadows end at the block. Live local quantum bindings must
be returned or explicitly discharged; even an identically named local cannot
stand in for its moved outer binding. -/
def outer (before after : Environment) : Except String Environment := do
  if after.any (fun cell => !(valueOwners cell.value).isEmpty &&
      !(before.any (sameBinding cell))) then throw "branch leaves a local quantum owner at block exit"
  before.foldlM (fun result original => do
    if (valueOwners original.value).isEmpty then return result ++ [original]
    match after.find? (sameBinding original) with
    | none => return result
    | some current =>
      if current.value != original.value then throw "branch changes an outer binding without an explicit result"
      return result ++ [original]) []

structure Phi where
  output : Semantics.SourceOwners.Owner
  thenOwner : Semantics.SourceOwners.Owner
  elseOwner : Semantics.SourceOwners.Owner
  thenType : thenOwner.basis = output.basis
  elseType : elseOwner.basis = output.basis
  deriving DecidableEq, Repr

instance : BEq Phi where
  beq first second := decide (first = second)

def merge (condition : Expression) (thenValue elseValue : Value) (nextOrdinal : Nat) :
    Except String (Value × List Phi) := do
  if thenValue.length != elseValue.length then throw "branch result tuple shape"
  (thenValue.zip elseValue).foldlM (fun (value,phis) (left,right) => do
    match left,right with
    | .owner first,.owner second =>
      if same : first.basis = second.basis then
        let output : Semantics.SourceOwners.Owner := ⟨nextOrdinal+phis.length,first.basis⟩
        return (value ++ [.owner output],phis ++ [⟨output,first,second,rfl,same.symm⟩])
      else throw "branch owner nominal type"
    | .ordinary first a,.ordinary second b =>
      if first != second then throw "branch ordinary nominal type"
      return (value ++ [.ordinary first (.choose condition a b)],phis)
    | .tuple first,.tuple second =>
      if first != second then throw "branch result tuple arity"
      return (value ++ [.tuple first],phis)
    | _,_ => throw "branch complete runtime type shape") ([],[])

def retired (before remaining : Environment) : List Semantics.SourceOwners.Owner :=
  let retained := owners remaining
  (owners before).filter fun owner => !retained.contains owner

end QleisliKernel.SourceTypes.SourceRuntimeBranches
