import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimeBodyDiscovery

/-! One original named call in a selected static arm uses the ordinary named
body/context boundary. The caller, static parent and callee retain distinct
source offsets. These controls grant no wire/handle or general compound route.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStaticNamed
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def source := "#![no_implicit_prelude]\n" ++
  "unitary fn leaf(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "pub unitary fn route[const n:Nat](u:Q<Unit>,q:Q<Bit>)->(Q<Bit>,Q<Unit>){\n" ++
  "    let q=if static n==0{q}else{leaf(q)};\n    (q,u)\n}\n"

private def namedEffects {dependencies program block} :
    RuntimePureBody.Node dependencies program block → List (Option Semantics.Raw.Effect)
  | .named _ _ body _ _ _ => [body.checked.signature.original.parsedHeader.effect]
  | _ => []

private def namedNaturals {dependencies program block} :
    RuntimePureBody.Node dependencies program block → List (List (String × Nat))
  | .named _ _ body _ _ _ => [body.checked.signature.arguments.naturals]
  | _ => []

private def actual (n exponent : Nat) (wrongOwner parentAsCall callerAsCallee publicObserve genericLeaf : Bool) :
    WorkM (List Nat × List Nat × List Nat × Nat × List (Option Semantics.Raw.Effect) × List (List (String × Nat))) := do
  let text := if publicObserve then source.replace "unitary fn leaf" "pub observe fn leaf" else source
  let text := if genericLeaf then
    (text.replace "fn leaf(q" "fn leaf[const m:Nat](q").replace "else{leaf(q)}" "else{leaf[0](q)}" else text
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let bit : Semantics.Raw.Port := ⟨1,[0],1⟩
  let operations : List Semantics.Observation.Op := if n == 0 then [] else
    [.pure (.applyUnitary (if wrongOwner then 0 else 1) 2
      [if wrongOwner then ⟨[],.monomial [] [0] [exponent]⟩ else ⟨[],.monomial [0] [0,1] [0,exponent]⟩])]
  let outputs := if n == 0 then [1,0] else if wrongOwner then [1,2] else [2,0]
  let program : Semantics.Observation.Program := ⟨[unit,bit],[],operations,outputs,[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  -- Untrusted proposal data; discovery independently checks all three origins.
  let tokens ← lift ((lexLocated text).mapError fun _ => Error.request)
  let some keyword := tokens.find? (·.text == "if") | throw .request
  let some writtenCall := tokens.reverse.find? (·.text == "leaf") | throw .request
  let some writtenPhase := tokens.find? (·.text == "phase") | throw .request
  let parent : SourceSequence.Position := ⟨keyword.span.startByte,0,operations.length⟩
  let callPosition : SourceSequence.Position :=
    ⟨if parentAsCall then parent.offset else writtenCall.span.startByte,0,operations.length⟩
  let childPosition : SourceSequence.Position :=
    ⟨if callerAsCallee then writtenCall.span.startByte else writtenPhase.span.startByte,0,operations.length⟩
  let calls := if n == 0 then [] else
    [(callPosition,RuntimeContextRequest.Context.mk [childPosition] [] [] [] [])]
  let context : RuntimeContextRequest.Context := .mk [parent] [] calls [] []
  let headers ← RuntimeBodyDiscovery.readHeaders artifact "main" "route" {naturals := [("n",n)]} context
  let fresh ← RuntimeBodyDiscovery.prepare #[0] headers
  let body := headers.source.body
  let prepared ← RuntimeInterval.prepare fresh.root.dependencies fresh.root.program
  let inputs ← RuntimeSourceBoundary.readInputs body prepared
    [[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨bit,[.bit]⟩]]
  let checked ← RuntimePureBody.checkPrepared artifact fresh.root body fresh.root.program context inputs.owners.bindings prepared
  return (checked.result.history.issued.map (·.ordinal),checked.result.bindings.map (·.owner.ordinal),
    checked.result.bindings.map (·.port.token),checked.result.actions.length,
    checked.result.actions.flatMap namedEffects,checked.result.actions.flatMap namedNaturals)

#guard (actual 0 4 false false false false false).run 10000000 |>.1.toOption == some ([0,1],[1,0],[1,0],0,[],[])
#guard (actual 1 4 false false false false false).run 10000000 |>.1.toOption == some ([0,1],[1,0],[2,0],1,[some .unitary],[[]])
#guard (match (actual 1 0 false false false false false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (actual 1 4 true false false false false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (actual 1 4 false true false false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 4 false false true false false).run 10000000 with | (.error .request,_) => true | _ => false)

-- The typed Basis/Nat continuation retains even this unused original actual
-- in the same body that the ordinary named reader actually checked.
#guard (actual 1 4 false false false false true).run 10000000 |>.1.toOption ==
  some ([0,1],[1,0],[2,0],1,[some .unitary],[[ ("m",0) ]])

-- Same-original-module inference is precise, while the callee's exported
-- Observe annotation stays intact in the retained original named body.
#guard (actual 1 4 false false false true false).run 10000000 |>.1.toOption == some ([0,1],[1,0],[2,0],1,[some .observe],[[]])

private def externalObserve : WorkM Unit := do
  let text := "#![no_implicit_prelude]\n" ++
    "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0{q}else{other::leaf(q)}}"
  let other := "#![no_implicit_prelude]\npub observe fn leaf(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}"
  let program : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text),("other",other)],0,none⟩
  let _ ← RuntimeBodyDiscovery.readSource artifact "main" "route" {naturals := [("n",0)]}
  pure ()

-- Neither static inactivity nor pure external body code sharpens its public
-- effect. This fails original family checking before a native graph exists.
#guard (match externalObserve.run 10000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.RuntimeStaticNamed
