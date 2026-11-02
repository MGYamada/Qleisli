import QleisliKernel.SourceTypes.StaticSelection
import QleisliKernel.SourceTypes.PhaseApplication

/-! Small original per-node supplying-context regressions. Metadata receipts
retain private-source forwarding and host/public boundaries; provider bodies,
Meaning equations and native implementation/control checks remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.OperationReceipts
open SourceTypes Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def sources : Sources := #[
  ("a","#![no_implicit_prelude] use b::bridge; unitary fn private_keep(q:Q<Bit>)->Q<Bit>{q} " ++
    "pub observe fn observed(q:Q<Bit>)->Q<Bit>{q} pub unitary fn caller(q:Q<Bit>)->Q<Bit>{bridge[private_keep](q)}"),
  ("b","#![no_implicit_prelude] use c::last; pub unitary fn bridge[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> " ++
    "requires Applicable(U){last[U,1](q)}"),
  ("c","#![no_implicit_prelude] pub unitary fn last[const U:Op<Bit>,const unused:Nat](q:Q<Bit>)->Q<Bit> " ++
    "requires Applicable(U){U(q)}") ]

private def forward : Option (List StaticOperation.Context × List (String × Bool) × Bool) :=
  let action : WorkM (List StaticOperation.Context × List (String × Bool) × Bool) := do
    let caller ← QuantumSignature.readWithArguments sources "a" "caller" {}
    let naturals ← PhaseApplication.prepareWithSignature caller
    let call ← adapt (CallSyntax.read caller.original.occurrence.body)
    let written ← adapt (StaticApplication.readSyntax call.call.callee)
    let candidate ← CallName.read sources "a" ["q"] written.callee
    let first ← QuantumSignature.selectInstance caller naturals.helpers.val naturals.environment ["q"]
      written candidate naturals.generic
    let bridge := first.signature
    let naturals ← PhaseApplication.prepareWithSignature bridge
    let call ← adapt (CallSyntax.read bridge.original.occurrence.body)
    let written ← adapt (StaticApplication.readSyntax call.call.callee)
    let candidate ← CallName.read sources "b" ["U","q"] written.callee
    let second ← QuantumSignature.selectInstance bridge naturals.helpers.val naturals.environment ["U","q"]
      written candidate naturals.generic
    let last := second.signature
    let naturals ← PhaseApplication.prepareWithSignature last
    let call ← adapt (CallSyntax.read last.original.occurrence.body)
    let checked ← SourceOperation.read last.toChecked naturals.helpers.val naturals.environment
      ["U","unused","q"] call.call.callee naturals.generic none (some last.supply)
    let providers := checked.graph.providers.map fun provider => (provider.moduleName,provider.internalInference)
    pure (checked.graph.contexts,providers,first.operationActuals.rows.any (·.1 == "a"))
  (action.run 10000000).1.toOption

-- Every forwarding layer keeps the original private leaf checked in a, even
-- though the two original lexical formal occurrences belong to b and c.
#guard forward = some ([.source "a",.source "b",.source "c"],[("a",true)],true)

private def hostAccepts (providerName : String) : Bool :=
  let description := OperationDescription.provider "a" providerName [] [] []
  ((QuantumSignature.readWithArguments sources "c" "last"
    {naturals := [("unused",1)],operations := [("U",description)]}).run 10000000).1.isOk

-- Host actuals remain external; neither original module privacy nor a public
-- Observe annotation can be laundered by a selected declaration's module.
#guard hostAccepts "private_keep" = false
#guard hostAccepts "observed" = false

private def mismatchedInstance : Bool :=
  let action : WorkM Unit := do
    let description := OperationDescription.provider "a" "private_keep" [] [] []
    let signature ← QuantumSignature.readWithArguments sources "c" "last"
      {naturals := [("unused",1)],operations := [("U",description)]} (.source "a")
    let changed := OperationDescription.formal "c" "last" [] [("unused",2)] [("U",description)] 0
    let _ ← StaticOperation.checkWithSupply signature.supply changed
    pure ()
  (action.run 10000000).1.isOk

-- Even an unused Nat actual belongs to the exact original instance receipt.
#guard mismatchedInstance = false

end QleisliKernel.Tests.OperationReceipts
