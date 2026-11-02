import QleisliKernel.Qirf.RuntimePureBody

/-! Fresh original named bodies against actual local Raw fragments.
Small role/phase faults stay structurally valid Raw; the source continuation
must independently reject them. No v5 handle or full-profile claim is issued.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimePureBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes QleisliKernel.Finite

private def text := "#![no_implicit_prelude]\nunitary fn change(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){(b,h(a))}\npub unitary fn main(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){change(a,b)}"
private def sources : Sources := #[("main",text)]
private def program (wrongRole wrongReturn : Bool) : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.gate .h (if wrongRole then 1 else 0) 2)],
    if wrongReturn then [2,if wrongRole then 0 else 1] else [if wrongRole then 0 else 1,2],[],.unitary⟩

private def checked (wrongRole wrongReturn : Bool) : WorkM Nat := do
  let signature ← SourceRuntimeContext.readSignature sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let childSignature ← SourceRuntimeContext.readSignature sources "main" "change" {}
  let child ← SourceRuntimeTrace.readBodyWithSignature childSignature
  let some call := body.checked.events.head? | throw .request
  let some action := child.checked.events.head? | throw .request
  let context : RuntimeContextRequest.Context := .mk
    [⟨call.offset,0,1⟩] [] [(⟨call.offset,0,1⟩,.mk [⟨action.offset,0,1⟩] [] [] [] [])] [] []
  let initial : RuntimeOwnerMap.Map := [⟨⟨0,[.bit]⟩,⟨0,[0],1⟩⟩,⟨⟨1,[.bit]⟩,⟨1,[1],1⟩⟩]
  let result ← Qirf.RuntimePureBody.check body [] (program wrongRole wrongReturn) context initial
  return result.result.actions.length

#guard (checked false false).run 10000000 |>.1.toOption == some 1
#guard (match (checked true false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (checked false true).run 10000000 with | (.error _,_) => true | _ => false)

end QleisliKernel.Tests.RuntimePureBody
