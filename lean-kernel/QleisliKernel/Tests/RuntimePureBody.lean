import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.Qirf.RuntimePureComposition
import QleisliKernel.Tests.ArmBody

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
  let artifact : Qirf.Artifact := ⟨#[program wrongRole wrongReturn],#[],sources,0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let childSignature ← SourceRuntimeContext.readSignature sources "main" "change" {}
  let child ← SourceRuntimeTrace.readBodyWithSignature childSignature
  let some call := body.checked.events.head? | throw .request
  let some action := child.checked.events.head? | throw .request
  let context : RuntimeContextRequest.Context := .mk
    [⟨call.offset,0,1⟩] [] [(⟨call.offset,0,1⟩,.mk [⟨action.offset,0,1⟩] [] [] [] [])] [] []
  let initial : RuntimeOwnerMap.Map := [⟨⟨0,[.bit]⟩,⟨0,[0],1⟩⟩,⟨⟨1,[.bit]⟩,⟨1,[1],1⟩⟩]
  let root ← Validity.checkRootFromRoots artifact #[0] [("main",text)] [0]
  let result ← Qirf.RuntimePureBody.check artifact root body root.program context initial
  let _ ← RuntimePureComposition.prepare artifact root body context initial result
  return result.result.actions.length

#guard (checked false false).run 10000000 |>.1.toOption == some 1
#guard (match (checked true false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (checked false true).run 10000000 with | (.error _,_) => true | _ => false)

private def selected (exponent : Nat) : WorkM Nat := do
  let artifact := ArmBody.artifact exponent
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let sign ← SourceRuntimeContext.readSignature artifact.sources "main" "sign" {}
  let sign ← SourceRuntimeTrace.readBodyWithSignature sign
  let some phase := sign.checked.events.head? | throw .request
  let some event := body.checked.events.head? | throw .request
  let position : SourceSequence.Position := ⟨event.offset,0,3⟩
  let site : RuntimeContextRequest.Site := ⟨ArmBody.interface,ArmBody.interface,position,[⟨3,4⟩,⟨1,2⟩]⟩
  let context : RuntimeContextRequest.Context := .mk [position] [site] [] []
    [(.function 1,.mk [⟨phase.offset,0,1⟩] [] [] [] []),(.function 0,.mk [] [] [] [] [])]
  let headers ← RuntimeBodyDiscovery.readHeaders artifact "main" "route" {} context
  let fresh ← RuntimeBodyDiscovery.prepare ArmBody.order headers
  let prepared ← RuntimeInterval.prepare fresh.root.dependencies fresh.root.program
  let actualBody := headers.source.body
  let inputs ← RuntimeSourceBoundary.readInputs actualBody prepared
    ((ArmBody.interface).inputs.map fun owner => [.quantum owner])
  let actual ← Qirf.RuntimePureBody.check artifact fresh.root actualBody fresh.root.program context inputs.owners.bindings
  let _ ← RuntimePureComposition.prepare artifact fresh.root actualBody context inputs.owners.bindings actual
  return actual.result.actions.length

#guard (selected 4).run 10000000 |>.1.toOption == some 1
-- The whole main, arm, specification and control agree on the wrong phase.
-- Every original provider body is nevertheless traversed, so this refuses.
#guard (match (selected 0).run 10000000 with | (.error .equation,_) => true | _ => false)

end QleisliKernel.Tests.RuntimePureBody
