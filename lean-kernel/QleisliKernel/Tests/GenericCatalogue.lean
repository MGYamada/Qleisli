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

private def cachedCandidate (sources : Sources) (name : String) (scope : List String := []) :
    Option (String × List (String × String)) :=
  let action : WorkM (String × List (String × String)) := do
    let actual ← sources.toList.mapM SourceTypes.GenericCatalogue.readModule
    let modules ← SourceTypes.GenericCatalogue.readModules sources actual
    let tokens ← lift ((lexLocated name).mapError fun _ => .request)
    let candidate ← CallName.readWithModules sources (some modules) "main" scope tokens
    let kind := match candidate.decision with
      | .lexical .. => "lexical"
      | .named .. => "named"
      | .prelude .. => "prelude"
      | .primitive .. => "primitive"
    pure (kind,CallName.sourceRows candidate)
  (action.run 10000000).1.toOption

-- Reuse cannot turn a changed policy, declaration spelling or row into the
-- previous query. Dependency rows remain the exact queried originals only.
private def off := "#![no_implicit_prelude] "
private def keep := "pub unitary fn h(q:Q<Bit>)->Q<Bit>{q}"
private def changedBody := "pub unitary fn h(q:Q<Bit>)->Q<Bit>{global_phase_eighth(q)}"

#guard cachedCandidate #[("main",off)] "h" = some ("primitive",[("main",off)])
#guard cachedCandidate #[("main","")] "h" = none
#guard cachedCandidate #[("main",off ++ keep)] "h" = some ("named",[("main",off ++ keep)])
#guard cachedCandidate #[("main",off ++ changedBody)] "h" =
    some ("named",[("main",off ++ changedBody)])
#guard cachedCandidate #[("main",off ++ "pub unitary fn g(q:Q<Bit>)->Q<Bit>{q}")] "h" =
    some ("primitive",[("main",off ++ "pub unitary fn g(q:Q<Bit>)->Q<Bit>{q}")])
#guard cachedCandidate #[("other",off)] "h" = none
#guard cachedCandidate #[("main",off ++ keep)] "h" ["h"] = some ("lexical",[])
#guard cachedCandidate #[("main",off ++ "enum h{A,B}")] "h" ["h"] = some ("lexical",[])

-- Imports still run the existing original resolver with its visibility and
-- reexport route; the prepared table grants no additional lookup authority.
#guard cachedCandidate #[("main",off ++ "use leaf::h;"),("leaf",off ++ keep)] "h" =
    some ("named",[("main",off ++ "use leaf::h;"),("leaf",off ++ keep)])
#guard cachedCandidate #[("main",off ++ "use leaf::h;"),("leaf",off ++ "unitary fn h(q:Q<Bit>)->Q<Bit>{q}")] "h" = none
#guard cachedCandidate #[("main",""),("std::prelude","pub use leaf::h;"),("leaf",off ++ keep)] "h" = none

private def preparationAccepts (original changed : Sources) : Bool :=
  let action : WorkM Unit := do
    let actual ← original.toList.mapM SourceTypes.GenericCatalogue.readModule
    let _ ← SourceTypes.GenericCatalogue.readModules changed actual
    pure ()
  (action.run 10000000).1.isOk

#guard preparationAccepts #[("main",off ++ keep)] #[("main",off ++ keep)]
#guard !preparationAccepts #[("main",off ++ keep)] #[("main",off ++ changedBody)]
#guard !preparationAccepts #[("main",off ++ keep)] #[("main",keep)]
#guard !preparationAccepts #[("main",off ++ keep)] #[("other",off ++ keep)]
#guard !preparationAccepts #[("main",off)] #[("main",off),("main",off)]

end QleisliKernel.Tests.GenericCatalogue
