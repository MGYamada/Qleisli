import QleisliKernel.SourceTypes.GenericCatalogue

/-! Small whole-original inventory studies. Unused declarations participate in
typing/effect inference but grant no selected dependency coverage. No finite
Meaning equation, basis injection or native provider body is certified here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericCatalogue
open SourceTypes Finite

private def program (source : String) : Sources := #[("main","#![no_implicit_prelude] " ++ source)]

private def view (sources : Sources) :
    Option (List (String × String) × Semantics.Raw.Effect × Bool × List String) :=
  let action : WorkM (List (String × String) × Semantics.Raw.Effect × Bool × List String) := do
    let catalogue ← SourceTypes.GenericCatalogue.read sources
    let original ← OrdinarySignature.readOriginalEnvelope sources "main" "root"
    let projection ← SourceTypes.GenericCatalogue.project catalogue.toRuntimeChecked original
    pure (catalogue.records.map (·.id),projection.inferredEffect,projection.quantumUse,
      (projection.sourceRows.map (·.1)).eraseDups)
  (action.run 10000000).1.toOption

#guard view (program "fn unused[const A:Basis](q:Q<A>)->Q<A>{q} pub unitary fn root(q:Q<Bit>)->Q<Bit>{q}") =
  some ([("main","unused"),("main","root")],.unitary,true,["main"])
#guard view (program "fn unused[const A:Basis](q:Q<A>)->Q<A>{h(q)} pub unitary fn root(q:Q<Bit>)->Q<Bit>{q}") = none

#guard view #[
    ("main","#![no_implicit_prelude] pub unitary fn root(q:Q<Bit>)->Q<Bit>{q}"),
    ("other","#![no_implicit_prelude] pub classical fn unused(x:Bit)->Bit{x}") ] =
  some ([("main","root"),("other","unused")],.unitary,true,["main"])

#guard view (program "static fn bad(n:Nat)->Nat{n-1} pub unitary fn root(q:Q<Bit>)->Q<Bit>{q}") = none
#guard view (program "struct Bad{field:Missing} pub unitary fn root(q:Q<Bit>)->Q<Bit>{q}") = none
#guard view (program "use absent::missing;pub unitary fn root(q:Q<Bit>)->Q<Bit>{q}") = none
#guard view (program "pub unitary fn root(q:Q<Bit>)->Q<Bit>{q} trailing") = none
#guard view (program "pub unitary fn root(q:Q<Bit>)->Q<Bit>{q} junk;") = none

-- Header-only same-module reference permission is sharpened only by an
-- independently checked original body, and cannot hide actual observation.
#guard (view (program ("observe fn keep(q:Q<Bit>)->Q<Bit>{q} meaning Identity:Bit=reference(keep);" ++
    "pub unitary fn root(q:Q<Bit>)->Q<Bit>{q}"))).map (fun (_,effect,quantum,rows) => (effect,quantum,rows)) =
  some (.unitary,true,["main"])
#guard view (program ("observe fn bad(q:Q<Bit>)->Q<Bit>{let m=measure_z(q);let u=unit(());basis u as _ {m}}" ++
    "meaning Wrong:Bit=reference(bad);pub unitary fn root(q:Q<Bit>)->Q<Bit>{q}")) = none

end QleisliKernel.Tests.GenericCatalogue
