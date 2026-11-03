import QleisliKernel.Qirf.RuntimeBodyGraph

/-! Closed Basis/Nat observing static-call controls over the same runtime loop.
The caller forwards its original opaque Basis formal and preserves a distinct
Unit spectator. A=Unit has one physical qubit; A=Bit has two for the genuine
equal-width consumed-owner mutant. Each real body graph uses fixed 10M work.
No result below is a native execution handle or a full instrument proof.
Strict positive guards retain the complete first experiment and fixed budget.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStaticBasisNatObserving
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def source := "#![no_implicit_prelude]\nuse helpers::next;\n" ++
  "observe fn read[const A:Basis,const j:Nat,const k:Nat,const unused:Nat](a:Q<A>,q:Q<Bit>)->(Bit,Q<A>)\n" ++
  "requires k>=1,unused>=1 { let q=phase[j,k](q); (measure_z(q),a) }\n" ++
  "pub observe fn route[const A:Basis,const n:Nat](u:Q<Unit>,a:Q<A>,q:Q<Bit>)->(Bit,Q<A>,Q<Unit>){\n" ++
  "    static let denominator=next[0]();\n" ++
  "    let (b,r)=if static n==0{read[A,1,denominator,1](a,q)}else{read[A,1,denominator,1](a,q)};\n" ++
  "    (b,r,u)\n}\n"

private def helper := "#![no_implicit_prelude]\npub static fn next[const n:Nat]()->Nat{n+1}\n"

private inductive Fault where
  | none | inverted | missingMeasurement | parentOffset | childOffset | otherArm | unitaryHeader | unusedElse | denominator
  deriving BEq

private def text (fault : Fault) : String :=
  if fault == .unitaryHeader then source.replace "pub observe fn route" "pub unitary fn route"
  else if fault == .unusedElse then
    source.replace "else{read[A,1,denominator,1](a,q)}" "else{read[A,1,denominator,0](a,q)}"
  else if fault == .denominator then source.replace "next[0]()" "next[1]()"
  else source

private def arguments (n : Nat) (twoBits : Bool) : StaticTypes.Arguments :=
  {bases := [("A",if twoBits then [.bit] else [.unit])],naturals := [("n",n)]}

private def historyCounts {sources : Sources} {owner name : String}
    {signature : SourceRuntimeContext.Signature sources owner name}
    {dependencies : List Semantics.Finite.Dependency} {program : Semantics.Observation.Program}
    {body : SourceRuntimeTrace.Body signature} {prepared : RuntimeInterval.Prepared dependencies program}
    {runtime : RuntimeFamily.Request} {inputs : RuntimeSourceBoundary.Inputs body prepared runtime.inputStorage}
    {initial : RuntimeOrdinaryInputs.Checked body prepared runtime inputs}
    {ssa : RuntimeOrdinaryBody.State} {bindings : RuntimeOwnerMap.Map} : Nat →
    ({assignments : List (List Bool)} →
      @RuntimeOrdinaryHistories.Rows sources owner name signature dependencies program body prepared runtime inputs
        initial ssa bindings assignments → List Nat) :=
  Nat.rec (fun {_} _ => []) (fun _ next {_} rows => match rows with
    | .nil => [] | .cons head tail => head.histories.length :: next tail)

private def sourceCalls (n : Nat) (twoBits : Bool) :
    WorkM (Bool × List Nat × Nat × List (String × Nat) × List (String × Nat) × Bool) := do
  let sources := #[("main",source),("helpers",helper)]
  let signature ← SourceRuntimeContext.readSignature sources "main" "route" (arguments n twoBits)
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.staticConditional event _] := body.checked.events | throw .request
  let selected ← SourceRuntimeTrace.readStaticSource event
  let [.named call] := selected.result.events | throw .request
  return (event.selection.selected,selected.result.consumed.map (·.ordinal),selected.result.nextOrdinal,
    call.target.actuals.actuals.map (fun actual => (actual.formal.name,actual.formal.ordinal)),
    call.target.signature.arguments.naturals,decide (call.target.signature.arguments.bases = (arguments n twoBits).bases))

private def namedActuals {dependencies program block} (basis : Semantics.FiniteCarrier.Basis) :
    RuntimePureBody.Step dependencies program block → List (List (String × Nat) × Bool × Option Semantics.Raw.Effect)
  | .named _ _ body _ _ _ _ _ => [(body.checked.signature.arguments.naturals,
      decide (body.checked.signature.arguments.bases = [("A",basis)]),body.checked.signature.original.parsedHeader.effect)]
  | _ => []

private def actual (n exponent : Nat) (twoBits wrongConsumed : Bool) (fault : Fault) :
    WorkM (List Nat × List Nat × Nat × List Nat × List Nat × List (Nat × Nat) × List Nat × Bool × Bool ×
      List (List (String × Nat) × Bool × Option Semantics.Raw.Effect) × Nat × Nat) := do
  let current := text fault
  let basis : Semantics.FiniteCarrier.Basis := if twoBits then [.bit] else [.unit]
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let a : Semantics.Raw.Port := ⟨1,if twoBits then [0] else [],if twoBits then 1 else 0⟩
  let q : Semantics.Raw.Port := ⟨2,[if twoBits then 1 else 0],1⟩
  let chosen := if wrongConsumed then a else q
  let returned := if wrongConsumed then q else a
  let output := if fault == .inverted then 5 else 4
  -- applyUnitary's circuit uses local port coordinates. The separate corrected
  -- first observer verifies both two-Bit Raw candidates with this local axis.
  let operations : List Semantics.Observation.Op :=
    [.pure (.applyUnitary chosen.token 3
      [⟨[],.monomial [0] [0,1] [0,exponent]⟩])] ++
    (if fault == .missingMeasurement then [.discard 3,.constant false 4] else [.measure 3 4]) ++
    (if fault == .inverted then [.not 4 5] else [])
  let program : Semantics.Observation.Program := ⟨[unit,a,q],[],operations,[returned.token,0],[output],.observe⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",current),("helpers",helper)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" (arguments n twoBits)
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.staticConditional event _] := body.checked.events | throw .request
  let selected ← SourceRuntimeTrace.readStaticSource event
  let [.named call] := selected.result.events | throw .request
  let callee ← SourceRuntimeTrace.readNamedBody call
  let [.phase phase,.primitive measured] := callee.checked.events | throw .request
  let [inactive] := (if event.selection.selected then event.elseCalls else event.thenCalls) | throw .request
  let parent : SourceSequence.Position := ⟨event.written.parts.keyword.span.startByte,0,operations.length⟩
  let position : SourceSequence.Position :=
    ⟨if fault == .parentOffset then parent.offset else if fault == .otherArm then inactive else call.call.calleeOffset,
      0,operations.length⟩
  let phasePosition : SourceSequence.Position := ⟨phase.call.calleeOffset,0,1⟩
  let measurePosition : SourceSequence.Position :=
    ⟨if fault == .childOffset then call.call.calleeOffset else measured.call.calleeOffset,1,1⟩
  let context : RuntimeContextRequest.Context := .mk [parent] []
    [(position,.mk [phasePosition,measurePosition] [] [] [] [])] [] []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",signature.parameters.map (·.tree),
      [[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨a,basis⟩],[.quantum ⟨q,[.bit]⟩]],[[]],signature.result.tree,
      [.tuple 3,.ordinary [.bit] (.bit output),.quantum ⟨returned,basis⟩,.quantum ⟨unit,[.unit]⟩],
      .observe,arguments n twoBits⟩
  let checked ← RuntimeBodyGraph.prepareRuntime artifact #[0] "main" "route" (arguments n twoBits) context runtime
  let measurements := checked.derivation.result.ordinary.measurements
  let origin : Semantics.SourceOrdinary.Site := ⟨"main","read",measured.call.calleeOffset⟩
  let callSite : Semantics.SourceOrdinary.Site := ⟨"main","route",call.call.calleeOffset⟩
  return (checked.derivation.result.history.issued.map (·.ordinal),checked.derivation.result.retired.map (·.ordinal),
    checked.derivation.result.history.nextOrdinal,checked.derivation.result.bindings.map (·.owner.ordinal),
    checked.derivation.result.bindings.map (·.port.token),
    measurements.map (fun measurement => (measurement.owner.ordinal,measurement.calls.length)),
    historyCounts ((OrdinaryDomain.assignments checked.initial.domain).length+1) checked.ordinary.rows,
    checked.headers.discovered.rows.any (fun row => row.1 == "helpers"),
    measurements.all (fun measurement => decide (measurement.origin = origin ∧ measurement.calls = [callSite])),
    checked.derivation.result.steps.flatMap (namedActuals basis),
    checked.derivation.result.actions.length,checked.derivation.result.steps.length)

private def expected (k : Nat) :
    List Nat × List Nat × Nat × List Nat × List Nat × List (Nat × Nat) × List Nat × Bool × Bool ×
      List (List (String × Nat) × Bool × Option Semantics.Raw.Effect) × Nat × Nat :=
  ([0,1,2],[2],3,[1,0],[1,0],[(2,1)],[2],true,true,
    [([("j",1),("k",k),("unused",1)],true,some .observe)],0,1)

private def refused {α : Type} (action : WorkM α) : Bool :=
  match action.run 10000000 with
  | (.error .request,_) | (.error .invalid,_) | (.error .equation,_) => true
  | _ => false

-- Exact original mixed ordinals, forwarded Basis and consumed roles already
-- succeeded in the first observer, independently of runtime continuation.
#guard (sourceCalls 0 false).run 10000000 |>.1.toOption == some (true,[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)
#guard (sourceCalls 1 false).run 10000000 |>.1.toOption == some (false,[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)
#guard (sourceCalls 1 true).run 10000000 |>.1.toOption == some (false,[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)

-- Every correct route must run the complete common body/history gate under the
-- original budget. A work-limit refusal cannot satisfy a positive guard.
#guard (actual 0 4 false false .none).run 10000000 |>.1.toOption == some (expected 1)
#guard (actual 1 4 false false .none).run 10000000 |>.1.toOption == some (expected 1)
#guard (match (actual 1 4 false false .inverted).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (actual 1 0 false false .none).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (actual 1 2 false false .denominator).run 10000000 |>.1.toOption == some (expected 2)
#guard (match (actual 1 4 false false .denominator).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (actual 1 4 false false .missingMeasurement).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 4 false false .parentOffset).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 4 false false .childOffset).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 4 false false .otherArm).run 10000000 with | (.error .request,_) => true | _ => false)

-- Original inactive-arm premises and effects remain mandatory.
#guard (match (actual 0 4 false false .unusedElse).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 4 false false .unitaryHeader).run 10000000 with | (.error .request,_) => true | _ => false)

-- Two distinct Bit owners may have the same width. Only the original q role
-- is consumed; a still-valid Raw mutant measuring a must not change that map.
#guard (actual 1 4 true false .none).run 10000000 |>.1.toOption == some (expected 1)
#guard refused (actual 1 4 true true .none)

end QleisliKernel.Tests.RuntimeStaticBasisNatObserving
