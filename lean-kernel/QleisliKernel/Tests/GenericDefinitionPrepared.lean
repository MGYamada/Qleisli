import QleisliKernel.SourceTypes.GenericCatalogue

/-! Original setup reuse retains fresh body/call obligations. These controls
check source metadata only, without native admission or a larger work budget.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericDefinitionPrepared
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite

private def read (source : String) : WorkM (GenericCatalogue.Checked #[("main",source)]) :=
  GenericCatalogue.read #[("main",source)]

private def repeated : WorkM (Nat × Bool × Nat) := do
  let catalogue ← read ("#![no_implicit_prelude]\n" ++
    "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
    "unitary fn caller(q:Q<Bit>)->Q<Bit>{let q=keep(q);keep(q)}")
  let some caller := catalogue.records.find? (·.name == "caller") | throw .request
  pure (catalogue.records.length,catalogue.records.all (·.prepared.isSome),
    (GenericCatalogue.bodyApplications caller).length)

-- Setup is shared, while both written call occurrences remain present.
#guard repeated.run 10000000 |>.1.toOption == some (2,true,2)

private def actuals : WorkM (List (List Int)) := do
  let catalogue ← read ("#![no_implicit_prelude]\n" ++
    "unitary fn leaf[const n:Nat](q:Q<Bit>)->Q<Bit> requires n>=1{q}\n" ++
    "unitary fn caller(q:Q<Bit>)->Q<Bit>{let q=leaf[1](q);leaf[2](q)}")
  let some caller := catalogue.records.find? (·.name == "caller") | throw .request
  pure ((GenericCatalogue.bodyApplications caller).map fun application =>
    application.naturalActuals.map (·.constant))

-- Simultaneous actual substitution is independent for each use of one setup.
#guard actuals.run 10000000 |>.1.toOption == some [[1],[2]]

private def accepts (source : String) : Bool := (read source).run 10000000 |>.1.toOption.isSome

-- A previous successful call cannot supply the later call's numeric premise.
#guard !accepts ("#![no_implicit_prelude]\n" ++
  "unitary fn leaf[const n:Nat](q:Q<Bit>)->Q<Bit> requires n>=1{q}\n" ++
  "unitary fn caller(q:Q<Bit>)->Q<Bit>{let q=leaf[1](q);leaf[0](q)}")

-- Even an unused original body must typecheck with its opaque Basis formal.
#guard !accepts ("#![no_implicit_prelude]\n" ++
  "unitary fn bad[const A:Basis](q:Q<A>)->Q<A>{h(q)}\n" ++
  "fn caller(u:Unit)->Unit{u}")

private def externalObserve : Bool :=
  let sources : Sources := #[
    ("main","#![no_implicit_prelude]\nuse helper::conservative;\n" ++
      "unitary fn ignore[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q}\n" ++
      "unitary fn caller(q:Q<Bit>)->Q<Bit>{ignore[conservative](q)}"),
    ("helper","#![no_implicit_prelude]\npub observe fn conservative(q:Q<Bit>)->Q<Bit>{q}")]
  (GenericCatalogue.read sources).run 10000000 |>.1.toOption.isSome

-- The original external public effect bounds even an unused supplied actual.
#guard !externalObserve

-- Duplicate original modules still fail before any prepared table is usable.
#guard !((GenericCatalogue.read #[("main","#![no_implicit_prelude]\nfn caller(u:Unit)->Unit{u}"),
  ("main","#![no_implicit_prelude]\nfn caller(u:Unit)->Unit{u}")]).run 10000000).1.toOption.isSome

end QleisliKernel.Tests.GenericDefinitionPrepared
