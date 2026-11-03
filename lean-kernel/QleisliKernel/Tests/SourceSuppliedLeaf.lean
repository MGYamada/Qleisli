import QleisliKernel.SourceTypes.QuantumSignature

/-! The real supplied graph reader keeps private caller context, original
actuals and zero-power children. Its catalogue leaf branch performs the common
provider check; this source metadata grants no native body or path evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceSuppliedLeaf
open QleisliKernel QleisliKernel.SourceTypes Finite Semantics.FiniteCarrier

private def off := "#![no_implicit_prelude] "
private def sources : Sources := #[
  ("a",off ++ "unitary fn hidden(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}" ++
    "pub unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{hidden(q)}" ++
    "pub unitary fn withOp[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}"),
  ("b",off ++ "pub unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{q}")]
private def leaf := OperationDescription.provider "a" "hidden" [] [] []

private def read (owner : String) (shared : Bool) (description : OperationDescription.Description) :
    WorkM (Semantics.Raw.Effect × List StaticOperation.Context × Nat × Basis) := do
  let catalogue ← GenericCatalogue.read sources
  let signature ← QuantumSignature.readWithArguments sources owner "caller"
    {naturals := [("n",0)]} (.source owner) (some catalogue)
  let arguments := if shared then signature.operations else {signature.operations with catalogue := none}
  let supply : StaticOperation.Supply signature.instantiation := ⟨signature.context,arguments⟩
  let data ← StaticOperation.readSuppliedData supply.data description
  return (data.root.effect,data.contexts,(data.results.filterMap (·.provider)).length,data.root.input)

#guard ((read "a" true leaf).run 10000000).1.toOption == some (.unitary,[.source "a"],1,[.bit])
#guard ((read "a" false leaf).run 10000000).1.toOption == some (.unitary,[.source "a"],1,[.bit])
#guard (match (read "b" true leaf).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (read "a" true (OperationDescription.provider "a" "hidden" [] [("n",0)] [])).run 10000000 with
  | (.error .request,_) => true | _ => false)

private def zero := leaf.unary (fun index => .power index 0)
#guard !StaticOperation.isFreshLeaf zero
#guard ((read "a" true zero).run 10000000).1.toOption ==
  some (.unitary,[.source "a",.source "a"],1,[.bit])

private def unused : WorkM (Nat × Nat × Basis) := do
  let catalogue ← GenericCatalogue.read sources
  let signature ← QuantumSignature.readWithArguments sources "a" "withOp"
    {operations := [("U",leaf)]} (.source "a") (some catalogue)
  let checked ← StaticOperation.checkWithSupply signature.supply leaf
  return (signature.operations.actuals.length,checked.results.length,checked.root.input)
#guard (unused.run 10000000).1.toOption == some (1,1,[.bit])

end QleisliKernel.Tests.SourceSuppliedLeaf
