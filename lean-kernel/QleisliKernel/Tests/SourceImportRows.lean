import QleisliKernel.SourceTypes.SourceImportRows
import QleisliKernel.Qirf.SourcePendingMeaning

/-! Small selected import closures retain exact original query receipts and
exclude unrelated audited modules. These are source-only controls, with no
accepted handle or altered quantum/work profile.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceImportRows
open SourceTypes Finite

private def off := "#![no_implicit_prelude] "
private def main := off ++ "use bridge::keep;pub unitary fn route(q:Q<Bit>)->Q<Bit>{keep(q)}"
private def bridge := off ++ "pub use leaf::keep;"
private def leaf := off ++ "pub unitary fn keep(q:Q<Bit>)->Q<Bit>{q}"
private def spare := off ++ "pub unitary fn unused(q:Q<Bit>)->Q<Bit>{q}"
private def sources : Sources := #[("main",main),("bridge",bridge),("leaf",leaf),("spare",spare)]

private def read (sources : Sources) (seeds : List SourceTypes.SourceRows.Row) :
    WorkM (List String × List String) := do
  let catalogue ← GenericCatalogue.read sources
  let _ ← Qirf.SourcePendingMeaning.read catalogue
  let checked ← SourceTypes.SourceImportRows.read catalogue seeds
  return (checked.rows.map (·.1),checked.modules.map (·.owner))

#guard ((read sources [("main",main)]).run 10000000).1.toOption ==
  some (["main","bridge","leaf"],["main","bridge","leaf"])
#guard ((read sources [("leaf",leaf)]).run 10000000).1.toOption == some (["leaf"],["leaf"])
#guard ((read sources []).run 10000000).1.toOption == some ([],[])
#guard ((read sources [("main",main),("main",main)]).run 10000000).1.toOption ==
  some (["main","bridge","leaf"],["main","bridge","leaf"])

-- Full original source identity and the real import visibility gates remain.
#guard (match (read sources [("main",main ++ " ")]).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (read #[("main",main),("bridge",bridge),("spare",spare)] [("main",main)]).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (read #[("main",main),("bridge",bridge),
    ("leaf",off ++ "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}"),("spare",spare)] [("main",main)]).run 10000000 with
  | (.error .request,_) => true | _ => false)

-- An unrelated original body is still audited; absence from relevance cannot
-- hide its invalid original effect.
#guard (match (read (sources.push ("bad",off ++
    "pub unitary fn bad(q:Q<Bit>)->Bit{measure_z(q)}")) [("main",main)]).run 10000000 with
  | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.SourceImportRows
