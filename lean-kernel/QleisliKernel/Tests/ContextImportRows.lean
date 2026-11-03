import QleisliKernel.Tests.ContextSectorData

/-! Existing contextual phase checks with an authentic consulted prelude import.
The original main/IR/owner positions remain unchanged. Added source rows must
be reached by real import queries; unrelated rows still refuse at the graph.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.ContextImportRows
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open ContextSectorTests

private def helper := "#![no_implicit_prelude] pub unitary fn extra(q:Q<Bit>)->Q<Bit>{q}"
private def prelude := "pub use helper::extra;"
private def related : Artifact := {artifact with
  sources := #[("main",text),("std::prelude",prelude),("helper",helper)]}

private def result (data : Artifact) : Except Finite.Error Nat :=
  ((ContextSector.check data order "main" "route" positions requests).run 13000000).1.map (·.locals.length)

#guard (result related).toOption == some 2
#guard (match result {related with sources := related.sources.push ("unrelated",helper)} with
  | .error .invalid => true | _ => false)
#guard (match result {related with sources := #[("main",text),("std::prelude",prelude)]} with
  | .error .request => true | _ => false)
#guard (match result {related with sources := #[("main",text),("std::prelude",prelude),
    ("helper","#![no_implicit_prelude] unitary fn extra(q:Q<Bit>)->Q<Bit>{q}")]} with
  | .error .request => true | _ => false)
#guard (match result {related with programs := related.programs.set! 0 (main 4 2)} with
  | .error .equation => true | _ => false)

end QleisliKernel.Tests.ContextImportRows
