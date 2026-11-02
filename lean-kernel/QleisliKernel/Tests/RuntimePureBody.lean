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

private def structural (text : String) (inputs : List Semantics.Raw.Port)
    (operations : List Semantics.Raw.Op) (outputs : List Nat) : WorkM (List Nat × List Nat × List Nat) := do
  let text := "#![no_implicit_prelude]\n" ++ text
  let sources : Sources := #[("main",text)]
  let program : Semantics.Observation.Program := ⟨inputs,[],operations.map .pure,outputs,[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],sources,0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let roles := body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let initial := (roles.zip inputs).map fun (owner,port) => (⟨owner,port⟩ : RuntimeOwnerMap.Binding)
  let context : RuntimeContextRequest.Context := .mk
    (body.checked.events.zipIdx.map fun (event,index) => ⟨event.offset,index,1⟩) [] [] [] []
  let root ← Validity.checkRootFromRoots artifact #[0] [("main",text)] [0]
  let checked ← Qirf.RuntimePureBody.check artifact root body root.program context initial
  let _ ← RuntimePureComposition.prepare artifact root body context initial checked
  return (checked.result.history.issued.map (·.ordinal),checked.result.retired.map (·.ordinal),
    checked.result.bindings.map (·.owner.ordinal))

private def splitJoin (wrongBoundary wrongOrder : Bool) := structural
  "pub unitary fn main(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{let (u,b)=split(q);join(u,h(b))}"
  [⟨0,[0],1⟩] [.split 0 1 2 (if wrongBoundary then 1 else 0),.gate .h 2 3,
    .join (if wrongOrder then 3 else 1) (if wrongOrder then 1 else 3) 4] [4]

-- The original owner 0 is replaced by 1,2,3. The same literal intervals retain
-- that complete history while H acts only on the original Bit component.
#guard (splitJoin false false).run 10000000 |>.1.toOption == some ([0,1,2,3],[0,1,2],[3])
#guard (match (splitJoin true false).run 10000000 with | (.error .invalid,_) => true | _ => false)
#guard (match (splitJoin false true).run 10000000 with | (.error .request,_) => true | _ => false)

-- Releasing a zero-width owner does not undo its scalar phase or issued ID.
private def releaseRecreate (exponent : Nat) := structural
  "pub unitary fn main(u:Q<Unit>)->Q<Unit>{let u=global_phase_eighth(u);finish(u);unit(())}"
  [⟨0,[],0⟩] [.applyUnitary 0 1 [⟨[],.monomial [] [0] [exponent]⟩],.unpackUnit 1,.packUnit 2] [2]

#guard (releaseRecreate 1).run 10000000 |>.1.toOption == some ([0,1],[0],[1])
#guard (match (releaseRecreate 0).run 10000000 with | (.error .equation,_) => true | _ => false)

private def namedStructural (omitH wrongJoin wrongReturn : Bool) : WorkM (List Nat × List Nat × List Nat) := do
  let text := "#![no_implicit_prelude]\nunitary fn rebuild(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{let (u,b)=split(q);join(u,h(b))}\npub unitary fn main(s:Q<Unit>,q:Q<(Unit,Bit)>)->(Q<(Unit,Bit)>,Q<Unit>){(rebuild(q),s)}"
  let operations : List Semantics.Raw.Op := [.split 1 2 3 0] ++ (if omitH then [] else [.gate .h 3 4]) ++
    [.join (if wrongJoin then (if omitH then 3 else 4) else 2)
      (if wrongJoin then 2 else (if omitH then 3 else 4)) 5]
  let program : Semantics.Observation.Program := ⟨[⟨0,[],0⟩,⟨1,[0],1⟩],[],operations.map .pure,
    (if wrongReturn then [0,5] else [5,0]),[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let callee ← SourceRuntimeTrace.readBodyWithSignature
    (← SourceRuntimeContext.readSignature artifact.sources "main" "rebuild" {})
  let some call := body.checked.events.head? | throw .request
  let [split,h,join] := callee.checked.events | throw .request
  let hCount := if omitH then 0 else 1
  let callPosition : SourceSequence.Position := ⟨call.offset,0,2+hCount⟩
  let context : RuntimeContextRequest.Context := .mk [callPosition] [] [(callPosition,
    .mk [⟨split.offset,0,1⟩,⟨h.offset,1,hCount⟩,⟨join.offset,1+hCount,1⟩] [] [] [] [])] [] []
  let roles := body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let initial := (roles.zip program.inputs).map fun (owner,port) => (⟨owner,port⟩ : RuntimeOwnerMap.Binding)
  let root ← Validity.checkRootFromRoots artifact #[0] [("main",text)] [0]
  let checked ← Qirf.RuntimePureBody.check artifact root body root.program context initial
  let _ ← RuntimePureComposition.prepare artifact root body context initial checked
  return (checked.result.history.issued.map (·.ordinal),checked.result.retired.map (·.ordinal),
    checked.result.bindings.map (·.owner.ordinal))

-- The callee's canonical owners are distinct from the caller's zero-width
-- spectator, and its source return order is not the native live-list order.
#guard (namedStructural false false false).run 10000000 |>.1.toOption == some ([0,1,2,3,4],[1,2,3],[4,0])
#guard (match (namedStructural true false false).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (namedStructural false true false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (namedStructural false false true).run 10000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.RuntimePureBody
