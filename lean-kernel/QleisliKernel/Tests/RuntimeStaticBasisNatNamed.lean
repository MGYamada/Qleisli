import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimeBodyDiscovery

/-! Closed Basis/Nat static calls retain their original mixed formal ordinals,
unused actuals, helper routes, full owner forests and source result order.
The same original named reader retains both owners, output permutation, exact
actuals and premises. One physical qubit plus a Unit spectator; fixed 10M.
These controls supply no new wire route, native handle or final composition.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStaticBasisNatNamed
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def source := "#![no_implicit_prelude]\nuse helpers::next;\n" ++
  "unitary fn leaf[const A:Basis,const j:Nat,const k:Nat,const unused:Nat](a:Q<A>,q:Q<Bit>)->(Q<Bit>,Q<A>)\n" ++
  "requires k>=1,unused>=1 { let q=phase[j,k](q); (q,a) }\n" ++
  "pub unitary fn route[const n:Nat](u:Q<Unit>,q:Q<Bit>)->(Q<Bit>,Q<Unit>){\n" ++
  "    static let denominator=next[0]();\n" ++
  "    if static n==0{(q,u)}else{leaf[type(Unit),1,denominator,1](u,q)}\n}\n"

private def helper := "#![no_implicit_prelude]\npub static fn next[const n:Nat]()->Nat{n+1}\n"

private inductive Fault where
  | none | denominator | premise | unusedActual | missingActual | zeroBasis | parentOffset | childOffset | publicObserve
  deriving BEq

private def text (fault : Fault) : String :=
  if fault == .denominator then source.replace "next[0]()" "next[1]()"
  else if fault == .premise then source.replace "requires k>=1" "requires k>=2"
  else if fault == .unusedActual then source.replace "1,denominator,1]" "1,denominator,0]"
  else if fault == .missingActual then source.replace "1,denominator,1]" "1,denominator]"
  else if fault == .zeroBasis then source.replace "type(Unit)" "type(Bits<0>)"
  else if fault == .publicObserve then source.replace "unitary fn leaf" "pub observe fn leaf"
  else source

private def sourceCalls (n : Nat) : WorkM (Bool × Nat × Option (List (String × Nat) × List (String × Nat) × Bool)) := do
  let sources := #[("main",source),("helpers",helper)]
  let signature ← SourceRuntimeContext.readSignature sources "main" "route" {naturals := [("n",n)]}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.staticConditional event _] := body.checked.events | throw .request
  let selected ← SourceRuntimeTrace.readStaticSource event
  let metadata ← match selected.result.events with
    | [] => pure none
    | [.named call] => pure (some
        (call.target.actuals.actuals.map (fun actual => (actual.formal.name,actual.formal.ordinal)),
          call.target.signature.arguments.naturals,
          decide (call.target.signature.arguments.bases = [("A",[.unit])])))
    | _ => throw .request
  return (event.selection.selected,selected.result.events.length,metadata)

private def namedActuals {dependencies program block} : RuntimePureBody.Node dependencies program block →
    List (List (String × Nat) × Bool × Option Semantics.Raw.Effect)
  | .named _ _ body _ _ _ => [(body.checked.signature.arguments.naturals,
      decide (body.checked.signature.arguments.bases = [("A",[.unit])]),
      body.checked.signature.original.parsedHeader.effect)]
  | _ => []

private def actual (n exponent : Nat) (fault : Fault) (wrongOwner wrongOrder : Bool) :
    WorkM (List Nat × List Nat × List Nat × Nat × List (List (String × Nat) × Bool × Option Semantics.Raw.Effect) × Bool) := do
  let current := text fault
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let bit : Semantics.Raw.Port := ⟨1,[0],1⟩
  let operations : List Semantics.Observation.Op := if n == 0 then [] else
    [.pure (.applyUnitary (if wrongOwner then 0 else 1) 2
      [if wrongOwner then ⟨[],.monomial [] [0] [exponent]⟩ else ⟨[],.monomial [0] [0,1] [0,exponent]⟩])]
  let outputs := if n == 0 then [1,0] else if wrongOwner then [1,2] else if wrongOrder then [0,2] else [2,0]
  let program : Semantics.Observation.Program := ⟨[unit,bit],[],operations,outputs,[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",current),("helpers",helper)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {naturals := [("n",n)]}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.staticConditional event _] := body.checked.events | throw .request
  let selected ← SourceRuntimeTrace.readStaticSource event
  let parent : SourceSequence.Position := ⟨event.written.parts.keyword.span.startByte,0,operations.length⟩
  let calls ← match selected.result.events with
    | [] => pure []
    | [.named call] => do
      let leaf ← SourceRuntimeTrace.readNamedBody call
      let [.phase phase] := leaf.checked.events | throw .request
      let position : SourceSequence.Position :=
        ⟨if fault == .parentOffset then parent.offset else call.call.calleeOffset,0,operations.length⟩
      let child : SourceSequence.Position :=
        ⟨if fault == .childOffset then call.call.calleeOffset else phase.call.calleeOffset,0,operations.length⟩
      pure [(position,RuntimeContextRequest.Context.mk [child] [] [] [] [])]
    | _ => throw .request
  let context : RuntimeContextRequest.Context := .mk [parent] [] calls [] []
  let headers ← RuntimeBodyDiscovery.readHeaders artifact "main" "route" {naturals := [("n",n)]} context
  let fresh ← RuntimeBodyDiscovery.prepare #[0] headers
  let prepared ← RuntimeInterval.prepare fresh.root.dependencies fresh.root.program
  let inputs ← RuntimeSourceBoundary.readInputs headers.source.body prepared
    [[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨bit,[.bit]⟩]]
  let checked ← RuntimePureBody.checkPrepared artifact fresh.root headers.source.body fresh.root.program context
    inputs.owners.bindings prepared
  return (checked.result.history.issued.map (·.ordinal),checked.result.bindings.map (·.owner.ordinal),
    checked.result.bindings.map (·.port.token),checked.result.actions.length,
    checked.result.actions.flatMap namedActuals,headers.discovered.rows.any (fun row => row.1 == "helpers"))

private def expected (k : Nat) (effect : Option Semantics.Raw.Effect := some .unitary) :
    List Nat × List Nat × List Nat × Nat × List (List (String × Nat) × Bool × Option Semantics.Raw.Effect) × Bool :=
  ([0,1],[1,0],[2,0],1,[([("j",1),("k",k),("unused",1)],true,effect)],true)

private def refused {α : Type} (action : WorkM α) : Bool :=
  match action.run 10000000 with
  | (.error .request,_) | (.error .invalid,_) | (.error .equation,_) => true
  | _ => false

-- These original source reads and exact mixed ordinal/actual observations were
-- already positive in the preserved first observer, before native eligibility.
#guard (sourceCalls 0).run 10000000 |>.1.toOption == some (true,0,none)
#guard (sourceCalls 1).run 10000000 |>.1.toOption == some (false,1,
  some ([("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true))

#guard (actual 0 4 .none false false).run 10000000 |>.1.toOption == some ([0,1],[1,0],[1,0],0,[],true)
#guard (actual 1 4 .none false false).run 10000000 |>.1.toOption == some (expected 1)
#guard (match (actual 1 0 .none false false).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard refused (actual 1 4 .none true false)
#guard refused (actual 1 4 .none false true)

-- The original helper-backed actual changes the exact callee phase. Matching
-- source/IR S succeeds; reusing the previous Z body cannot stand for k=2.
#guard (actual 1 2 .denominator false false).run 10000000 |>.1.toOption == some (expected 2)
#guard (match (actual 1 4 .denominator false false).run 10000000 with | (.error .equation,_) => true | _ => false)

-- Original premise, actual completeness and exact zero-width type failures
-- are checked even when the host instance selects the other static arm.
#guard (match (actual 0 4 .premise false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 0 4 .unusedActual false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 0 4 .missingActual false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 0 4 .zeroBasis false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 4 .parentOffset false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 4 .childOffset false false).run 10000000 with | (.error .request,_) => true | _ => false)

-- Precise same-original-module inference preserves the callee's public
-- annotation. It is not a permission to sharpen an external public boundary.
#guard (actual 1 4 .publicObserve false false).run 10000000 |>.1.toOption == some (expected 1 (some .observe))

end QleisliKernel.Tests.RuntimeStaticBasisNatNamed
