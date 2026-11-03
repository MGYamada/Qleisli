import QleisliKernel.SourceTypes.SourceTrace
import QleisliKernel.Qirf.SourcePendingMeaning

/-! Fresh source-tree checking may share its exact audited definition world.
These controls retain original target/reference identity, public visibility and
effect boundaries. No IR, body matrix or accepted handle is inferred here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceBodyRecheck
open QleisliKernel QleisliKernel.SourceTypes Finite

private def off := "#![no_implicit_prelude] "
private def sources (selected : String := "leaf") (leafHeader : String := "pub unitary")
    (shadow : Bool := false) : Sources := #[
  ("main",off ++ "use lib::leaf;use other::second;pub unitary fn root(" ++
    (if shadow then "leaf" else "q") ++ ":Q<Bit>)->Q<Bit>{" ++
    selected ++ "(" ++ (if shadow then "leaf" else "q") ++ ")}"),
  ("lib",off ++ leafHeader ++ " fn leaf(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}"),
  ("other",off ++ "pub unitary fn second(q:Q<Bit>)->Q<Bit>{q}"),
  ("spare",off ++ "pub unitary fn unused(q:Q<Bit>)->Q<Bit>{q}")]

private def view (data : Sources) (shared : Bool := true) :
    WorkM (Bool × Semantics.Raw.Effect × List SourceEffectClosure.DefId × List String) := do
  let catalogue ← GenericCatalogue.read data
  let _ ← Qirf.SourcePendingMeaning.read catalogue
  let signature ← QuantumSignature.readWithArguments data "main" "root" {} .external
    (if shared then some catalogue else none)
  let body ← SourceTrace.readWithSignature signature
  let (retained,references) := match body.checked.generic with
    | .fresh checked => (false,checked.root.outcome.references)
    | .catalogued _ _ checked => (true,checked.root.outcome.references)
  return (retained,body.checked.generic.inferredEffect,references,
    (body.checked.sourceRows.map (·.1)).eraseDups)

private def honest (shared : Bool) : WorkM Bool := do
  let (retained,effect,references,rows) ← view (sources) shared
  return retained == shared && effect == .unitary && references.contains ("lib","leaf") &&
    !references.contains ("other","second") && rows.contains "main" && rows.contains "lib" &&
    !rows.contains "spare"

#guard (honest true |>.run 10000000).1.toOption == some true
#guard (honest false |>.run 10000000).1.toOption == some true

private def changedReference : WorkM Bool := do
  let (retained,effect,references,rows) ← view (sources "second")
  return retained && effect == .unitary && references.contains ("other","second") &&
    !references.contains ("lib","leaf") && rows.contains "other" && !rows.contains "spare"
#guard (changedReference.run 10000000).1.toOption == some true

-- An actual pure body cannot sharpen an imported public Observe boundary.
#guard (match (view (sources "leaf" "pub observe")).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (view (sources "leaf" "unitary")).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (view (sources "leaf" "pub")).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (view (sources "leaf" "pub unitary" true)).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (view ((sources).push ("bad",off ++
    "pub unitary fn bad(q:Q<Bit>)->Bit{measure_z(q)}"))).run 10000000 with
  | (.error .request,_) => true | _ => false)

private def genericCold : WorkM Bool := do
  let data : Sources := #[("main",off ++
    "pub unitary fn root[const n:Nat](q:Q<Bit>)->Q<Bit>{q}")]
  let catalogue ← GenericCatalogue.read data
  let signature ← QuantumSignature.readWithArguments data "main" "root" {naturals := [("n",0)]}
    .external (some catalogue)
  let body ← SourceTrace.readWithSignature signature
  return match body.checked.generic with | .fresh _ => true | .catalogued .. => false
#guard (genericCold.run 10000000).1.toOption == some true

end QleisliKernel.Tests.SourceBodyRecheck
