import QleisliKernel.SourceTypes.SourceComputedSyntax

/-! Original computed scope headers, reference names, binders and body slices.
No syntax result supplies owner typing, exact clean release or logical evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceComputedSyntax
open QleisliKernel.SourceTypes

private def read (source : String) : Except String (Sigma SourceComputedSyntax.Checked) := do
  let tokens ← lexLocated source
  return ⟨tokens,← SourceComputedSyntax.read tokens⟩

#guard (read "with_computed(q,p){|aux|z(aux)}").isOk
#guard (read "with_computed(q,lib::p,logical){|data,aux|(data,z(aux))}").isOk
#guard (read "with_computed(f(q),p){|aux|let b=h(aux);h(b)}").isOk
#guard (read "with_computed(q,p){|aux|z(aux)}").toOption.map
  (fun written => written.2.parts.body.map (·.text)) = some ["z","(","aux",")"]
#guard (read "with_computed(q,p,logical){|data,aux|(data,aux)}").toOption.map
  (fun written => written.2.parts.data.map (·.text)) = some (some "data")
#guard (read "with_computed(q,p[2]){|aux|aux}").toOption.isNone
#guard (read "with_computed(q,p,logical()){|data,aux|(data,aux)}").toOption.isNone
#guard (read "with_computed(q,p){|data,aux|aux}").toOption.isNone
#guard (read "with_computed(q,p,logical){|aux|aux}").toOption.isNone
#guard (read "with_computed(q,p,logical){|same,same|(same,same)}").toOption.isNone
#guard (read "with_computed(q,p,){|aux|aux}").toOption.isNone
#guard (read "with_computed(q,p){|aux|aux} trailing").toOption.isNone

#print axioms QleisliKernel.SourceTypes.SourceComputedSyntax.read
end QleisliKernel.Tests.SourceComputedSyntax
