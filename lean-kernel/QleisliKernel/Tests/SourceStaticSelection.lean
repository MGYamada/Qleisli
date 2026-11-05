import QleisliKernel.SourceTypes.SourceRuntimeContext
import QleisliKernel.SourceTypes.SourceStaticSelection
import QleisliKernel.Tests.SourceTraceOriginals

/-! Actual original caller Nat comparisons and helper routes. These are
selection-preparation tests; the default body reader still requires independent
both-arm original typing/effect/decrease obligations before static traversal.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceStaticSelection
open QleisliKernel QleisliKernel.SourceTypes

private def prepare (source : String) (n : Nat) := do
  let sources := #[("main",source)] ++ SourceTraceOriginals.bundled
  let signature ← SourceRuntimeContext.readSignature sources "main" "route" {naturals := [("n",n)]}
  let naturals ← signature.naturals
  let written ← Finite.lift ((SourceStaticControlSyntax.read signature.original.occurrence.body).mapError fun _ => .request)
  let checked ← SourceStaticSelection.read sources "main" naturals (signature.staticNames ++ ["q"]) written
  return (checked.selected,checked.rows.any fun row => row.1 == "main")

private def body := "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0{phase[1,n](q)}else{q}}"
#guard ((prepare body 0).run 2000000000).1.toOption = some (false,false)
#guard ((prepare body 2).run 2000000000).1.toOption = some (true,false)
#guard ((prepare (body.replace "n>0" "n*n>0") 2).run 2000000000).1.toOption.isNone
#guard ((prepare (body.replace "n>0" "q==0") 0).run 2000000000).1.toOption.isNone

private def helper := "static fn next[const k:Nat]()->Nat{k+1}" ++
  "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static next[n]()>1{q}else{q}}"
#guard ((prepare helper 0).run 2000000000).1.toOption = some (false,true)
#guard ((prepare helper 1).run 2000000000).1.toOption = some (true,true)

#print axioms QleisliKernel.SourceTypes.SourceStaticSelection.read
end QleisliKernel.Tests.SourceStaticSelection
