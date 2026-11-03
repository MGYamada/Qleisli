import QleisliKernel.SourceTypes.GenericDutyQueue

/-! Canonical lookup reuse preserves original instances and actual maps.
These source-only controls do not discharge duties or issue native decisions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericDutyPrepared
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite

private def resolutionFresh {sources catalogue owner name original} :
    (entry : GenericCatalogue.Entry (@GenericCatalogue.Checked.toRuntimeChecked sources catalogue) original) →
      @GenericDutyQueue.Resolution sources catalogue owner name original entry → Bool
  | _,.fresh .. | _,.indexed .. => true
  | _,.retained .. => false

private def fresh {sources catalogue record application}
    (target : @GenericDutyQueue.Target sources catalogue record application) : Bool :=
  resolutionFresh target.entry target.resolution

private def repeated : WorkM (List Bool × List (List Int) × List Nat) := do
  let source := "#![no_implicit_prelude]\n" ++
    "unitary fn leaf[const n:Nat](q:Q<Bit>)->Q<Bit> requires n>=1{q}\n" ++
    "unitary fn first(q:Q<Bit>)->Q<Bit>{leaf[1](q)}\n" ++
    "unitary fn second(q:Q<Bit>)->Q<Bit>{leaf[2](q)}"
  let catalogue ← GenericCatalogue.read #[("main",source)]
  let queue ← GenericDutyQueue.read catalogue
  let provenance := queue.prepared.records.flatMap fun row => row.value.calls.map (fun call => fresh call.target)
  let actuals := queue.prepared.records.flatMap fun row => row.value.calls.map fun call =>
    call.application.original.naturalActuals.map (·.constant)
  let roots := queue.items.filterMap fun item => match item with
    | .call invocation _ _ => some invocation.id.root
    | _ => none
  pure (provenance,actuals,roots)

-- The second application borrows exactly the first indexed-selection receipt.
-- Its own Nat map and root/call occurrence remain distinct.
#guard repeated.run 10000000 |>.1.toOption == some ([true,false],[[1],[2]],[1,2])

private def differentModules : WorkM (List Bool × Nat) := do
  let sources : Sources := #[
    ("main","#![no_implicit_prelude]\n" ++
      "unitary fn caller(q:Q<Bit>)->Q<Bit>{let q=left::leaf(q);right::leaf(q)}"),
    ("left","#![no_implicit_prelude]\npub unitary fn leaf(q:Q<Bit>)->Q<Bit>{q}"),
    ("right","#![no_implicit_prelude]\npub unitary fn leaf(q:Q<Bit>)->Q<Bit>{q}")]
  let catalogue ← GenericCatalogue.read sources
  let queue ← GenericDutyQueue.read catalogue
  let provenance := queue.prepared.records.flatMap fun row => row.value.calls.map (fun call => fresh call.target)
  let targets := queue.prepared.records.flatMap fun row => row.value.calls.map (fun call => call.target.entry.index.val)
  pure (provenance,targets.eraseDups.length)

-- Equal declaration spellings in different original modules are separate keys.
#guard differentModules.run 10000000 |>.1.toOption == some ([true,true],2)

end QleisliKernel.Tests.GenericDutyPrepared
