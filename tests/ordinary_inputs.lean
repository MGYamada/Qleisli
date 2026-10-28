import QleisliKernel.Tests.OrdinaryInputs

/-! Execute all bounded controls against actual compiled definitions. These
observations are conformance tests, not kernel proofs of their Boolean results.
Generic signature/domain/history postconditions remain proved in the production
modules. Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

open QleisliKernel QleisliKernel.SourceTypes

private def importSources : Sources := #[
  ("main","use facade::Tri; pub fn f(value:Tri)->Tri {value}"),
  ("facade","pub use leaf::Tri;"),
  ("leaf","pub enum Tri {A,B,C}"),
  ("unused","pub static fn width()->Nat {2}")]

private def path (sources : Sources) (caller : String) (tokens : List String) :
    Option (List (String × String)) :=
  match (ResolutionProvenance.read sources caller tokens).run 1000000 with
  | (.ok result,_) => some (ResolutionProvenance.sourceRows result)
  | _ => none

private def typeRows (sources : Sources) (caller : String) (tokens : List String) :
    Option (List (String × String)) :=
  match (typeExpressionWithSources sources caller tokens).run 10000000 with
  | (.ok result,_) => some result.sourceRows
  | _ => none

private def importControls : List (String × Bool) := [
  ("unqualified original occurrence retains both import hops and terminal bytes",
    path importSources "main" ["Tri"] == some (importSources.toList.take 3)),
  ("qualified lookup retains its actual path without inventing the caller row",
    path importSources "main" ["facade","::","Tri"] ==
      some (importSources.toList.drop 1 |>.take 2)),
  ("local terminal lookup retains the original source",
    path importSources "leaf" ["Tri"] == some [importSources[2]!]),
  ("missing intermediary refuses",
    (path #[importSources[0]!,importSources[2]!] "main" ["Tri"]).isNone),
  ("private reexport refuses",
    (path #[importSources[0]!, ("facade","use leaf::Tri;"),importSources[2]!]
      "main" ["Tri"]).isNone),
  ("cyclic reexport refuses",
    (path #[importSources[0]!, ("facade","pub use leaf::Tri;"),
      ("leaf","pub use facade::Tri;")] "main" ["Tri"]).isNone),
  ("type read retains actual import rows and excludes validated unused helpers",
    typeRows importSources "main" ["Tri"] == some (importSources.toList.take 3)),
  ("builtin type grants no source row coverage",
    typeRows importSources "main" ["Bit"] == some []),
  ("tuple read retains each original occurrence",
    typeRows importSources "main" ["(","Tri",",","Tri",")"] ==
      some ((importSources.toList.take 3) ++ (importSources.toList.take 3))),
  ("recursive public record field retains its own original import path",
    let sources : Sources := #[
      ("main","use packet::Packet; pub fn f(value:Packet)->Packet {value}"),
      ("packet","use facade::Tri; pub struct Packet {pub value:Tri}"),
      importSources[1]!,importSources[2]!]
    typeRows sources "main" ["Packet"] ==
      some ([sources[0]!,sources[1]!,sources[1]!,sources[2]!,sources[3]!])),
  ("zero-width nominal type retains its import path",
    let sources : Sources := #[
      ("main","use facade::Empty; pub fn f(value:Empty)->Empty {value}"),
      ("facade","pub use leaf::Empty;"),("leaf","pub struct Empty {}")]
    typeRows sources "main" ["Empty"] == some sources.toList)]

def main : IO Unit := do
  let controls := QleisliKernel.Tests.OrdinaryInputs.controls
  let failures := controls.filter (fun control => !control.2)
  unless controls.length == 20 && failures.isEmpty do
    throw (IO.userError ("ordinary input/history controls failed: " ++
      String.intercalate "; " (failures.map (·.1))))
  IO.println "passed 20 complete input/all-history controls; at most one qubit"
  let failures := importControls.filter (fun control => !control.2)
  unless importControls.length == 11 && failures.isEmpty do
    throw (IO.userError ("ordinary original-type import controls failed: " ++
      String.intercalate "; " (failures.map (·.1))))
  IO.println "passed 11 original-type import/row controls; zero qubits"
