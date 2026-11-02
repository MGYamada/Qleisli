import QleisliKernel.SourceTypes.SourceMeaning

/-! Original Meaning graph reuse preserves lexical and external visibility.
This prepares requests only; no Meaning equation or native result is checked.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceMeaningPrepared
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite

private def sources : Sources := #[("main","#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
  "meaning Identity:Bit=reference(keep);\n" ++
  "pub meaning PublicIdentity:Bit=reference(keep);"),
  ("other","#![no_implicit_prelude]\nfn unused()->Unit{()}")]

private def inspect (caller : String) (scope tokens : List String) : WorkM (String × String × Nat) := do
  let prepared ← SourceMeaning.prepare sources [("main","Identity"),("main","PublicIdentity")]
  let selected ← SourceMeaning.select sources caller scope tokens (some prepared)
  pure (selected.root.owner,selected.root.name,selected.meaning.graph.references.length)

#guard (inspect "main" [] ["Identity"]).run 10000000 |>.1.toOption == some ("main","Identity",1)

-- The original name decision remains fresh; a lexical binder can block it.
#guard (match (inspect "main" ["Identity"] ["Identity"]).run 10000000 with
  | (.error .request,_) => true | _ => false)

-- An internally prepared private graph supplies no external lookup authority.
#guard (match (inspect "other" [] ["main","::","Identity"]).run 10000000 with
  | (.error .request,_) => true | _ => false)

-- Public external selection still takes its fresh graph/visibility path.
#guard (inspect "other" [] ["main","::","PublicIdentity"]).run 10000000
  |>.1.toOption == some ("main","PublicIdentity",1)

end QleisliKernel.Tests.SourceMeaningPrepared
