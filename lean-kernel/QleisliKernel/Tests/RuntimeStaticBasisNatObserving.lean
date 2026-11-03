import QleisliKernel.Qirf.RuntimeBodyGraph

/-! Closed Basis/Nat observing static-call controls over the same runtime loop.
The caller forwards its original opaque Basis formal and preserves a distinct
Unit spectator. A=Unit has one physical qubit; A=Bit has two for the genuine
equal-width consumed-owner mutant. Each real body graph uses fixed 10M work.
No result below is a native execution handle or a full instrument proof.
The informed first authoring benchmark charged producer source/body reads and
native checking together and exhausted its 10M counter. That failure remains
in the immutable first observers, diagnostics and earlier test commits. These
maintained runtime guards instead test the actual native boundary: plain
untrusted proposal construction precedes REAL prepareRuntime at fresh 10M.
No producer signature, Body, proof, result or work state crosses as authority.
The same source, corrected local IR and strict semantic oracles are retained;
this does not reclassify the combined benchmark as passing. The three original
source-metadata probes below remain separate source-only observations.
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

private structure Payload where
  artifact : Qirf.Artifact
  context : RuntimeContextRequest.Context
  runtime : RuntimeFamily.Request

-- This is the same plain literal payload whose complete recognized fields
-- were compared with the original producer in the independent native-only
-- observer. All twelve producer-success comparisons returned some true; the
-- two invalid-source producer refusals supplied no equality claim. Lexing
-- contributes untrusted byte coordinates only; native reads them independently.
private def literal (n exponent : Nat) (twoBits wrongConsumed : Bool) (fault : Fault) : Except String Payload := do
  let current := text fault
  let basis : Semantics.FiniteCarrier.Basis := if twoBits then [.bit] else [.unit]
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let a : Semantics.Raw.Port := ⟨1,if twoBits then [0] else [],if twoBits then 1 else 0⟩
  let q : Semantics.Raw.Port := ⟨2,[if twoBits then 1 else 0],1⟩
  let chosen := if wrongConsumed then a else q
  let returned := if wrongConsumed then q else a
  let output := if fault == .inverted then 5 else 4
  let operations : List Semantics.Observation.Op :=
    [.pure (.applyUnitary chosen.token 3 [⟨[],.monomial [0] [0,1] [0,exponent]⟩])] ++
    (if fault == .missingMeasurement then [.discard 3,.constant false 4] else [.measure 3 4]) ++
    (if fault == .inverted then [.not 4 5] else [])
  let program : Semantics.Observation.Program := ⟨[unit,a,q],[],operations,[returned.token,0],[output],.observe⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",current),("helpers",helper)],0,none⟩
  let tokens ← lexLocated current
  let some keyword := tokens.find? (·.text == "if") | throw "missing original if"
  let [_declaration,thenCall,elseCall] := tokens.filter (·.text == "read") | throw "original read occurrence count"
  let some phase := tokens.find? (·.text == "phase") | throw "missing original phase"
  let some measure := tokens.find? (·.text == "measure_z") | throw "missing original measurement"
  let selected := if n == 0 then thenCall.span.startByte else elseCall.span.startByte
  let other := if n == 0 then elseCall.span.startByte else thenCall.span.startByte
  let parent : SourceSequence.Position := ⟨keyword.span.startByte,0,operations.length⟩
  let position : SourceSequence.Position :=
    ⟨if fault == .parentOffset then parent.offset else if fault == .otherArm then other else selected,0,operations.length⟩
  let phasePosition : SourceSequence.Position := ⟨phase.span.startByte,0,1⟩
  let measurePosition : SourceSequence.Position :=
    ⟨if fault == .childOffset then selected else measure.span.startByte,1,1⟩
  let context : RuntimeContextRequest.Context := .mk [parent] []
    [(position,.mk [phasePosition,measurePosition] [] [] [] [])] [] []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",[Semantics.RuntimeType.owner [.unit],Semantics.RuntimeType.owner basis,
        Semantics.RuntimeType.owner [.bit]],
      [[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨a,basis⟩],[.quantum ⟨q,[.bit]⟩]],[[]],
      Semantics.RuntimeType.tuple 3 [Semantics.RuntimeType.ordinary [.bit],Semantics.RuntimeType.owner basis,
        Semantics.RuntimeType.owner [.unit]],
      [.tuple 3,.ordinary [.bit] (.bit output),.quantum ⟨returned,basis⟩,.quantum ⟨unit,[.unit]⟩],
      .observe,arguments n twoBits⟩
  return ⟨artifact,context,runtime⟩

private abbrev NativeSummary :=
  List Nat × List Nat × Nat × List Nat × List Nat × List (Nat × Nat) × List Nat × Bool × Bool ×
    List (List (String × Nat) × Bool × Option Semantics.Raw.Effect) × Nat × Nat

private def native (payload : Payload) : WorkM NativeSummary := do
  let checked ← RuntimeBodyGraph.prepareRuntime payload.artifact #[0] "main" "route"
    payload.runtime.staticArguments payload.context payload.runtime
  -- Only inspect the native result and plain request fields after checking.
  let [("A",basis)] := payload.runtime.staticArguments.bases | throw .request
  let [(position,child)] := payload.context.calls | throw .request
  let [_phase,measure] := child.positions | throw .request
  let measurements := checked.derivation.result.ordinary.measurements
  let origin : Semantics.SourceOrdinary.Site := ⟨"main","read",measure.offset⟩
  let callSite : Semantics.SourceOrdinary.Site := ⟨"main","route",position.offset⟩
  return (checked.derivation.result.history.issued.map (·.ordinal),checked.derivation.result.retired.map (·.ordinal),
    checked.derivation.result.history.nextOrdinal,checked.derivation.result.bindings.map (·.owner.ordinal),
    checked.derivation.result.bindings.map (·.port.token),
    measurements.map (fun measurement => (measurement.owner.ordinal,measurement.calls.length)),
    historyCounts ((OrdinaryDomain.assignments checked.initial.domain).length+1) checked.ordinary.rows,
    checked.headers.discovered.rows.any (fun row => row.1 == "helpers"),
    measurements.all (fun measurement => decide (measurement.origin = origin ∧ measurement.calls = [callSite])),
    checked.derivation.result.steps.flatMap (namedActuals basis),
    checked.derivation.result.actions.length,checked.derivation.result.steps.length)

-- The producer is outside this run. Only the real native component starts its
-- own fixed counter, as at the production trust boundary; it resets no state.
private def actual (n exponent : Nat) (twoBits wrongConsumed : Bool) (fault : Fault) :
    Except String (Except Finite.Error NativeSummary × Nat) := do
  let payload ← literal n exponent twoBits wrongConsumed fault
  pure ((native payload).run 10000000)

private def accepted {α : Type} (attempt : Except String (Except Error α × Nat)) : Option α :=
  match attempt with | .ok (.ok value,_) => some value | _ => none

private def expected (k : Nat) : NativeSummary :=
  ([0,1,2],[2],3,[1,0],[1,0],[(2,1)],[2],true,true,
    [([("j",1),("k",k),("unused",1)],true,some .observe)],0,1)

-- Exact original mixed ordinals, forwarded Basis and consumed roles already
-- succeeded in the first observer, independently of runtime continuation.
#guard (sourceCalls 0 false).run 10000000 |>.1.toOption == some (true,[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)
#guard (sourceCalls 1 false).run 10000000 |>.1.toOption == some (false,[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)
#guard (sourceCalls 1 true).run 10000000 |>.1.toOption == some (false,[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)

-- Every correct route runs the complete common native body/history gate at
-- 10M after plain proposal construction. Work-limit refusal cannot pass.
#guard accepted (actual 0 4 false false .none) == some (expected 1)
#guard accepted (actual 1 4 false false .none) == some (expected 1)
#guard (match actual 1 4 false false .inverted with | .ok (.error .equation,_) => true | _ => false)
#guard (match actual 1 0 false false .none with | .ok (.error .equation,_) => true | _ => false)
#guard accepted (actual 1 2 false false .denominator) == some (expected 2)
#guard (match actual 1 4 false false .denominator with | .ok (.error .equation,_) => true | _ => false)
#guard (match actual 1 4 false false .missingMeasurement with | .ok (.error .request,_) => true | _ => false)
#guard (match actual 1 4 false false .parentOffset with | .ok (.error .request,_) => true | _ => false)
#guard (match actual 1 4 false false .childOffset with | .ok (.error .request,_) => true | _ => false)
#guard (match actual 1 4 false false .otherArm with | .ok (.error .request,_) => true | _ => false)

-- Original inactive-arm premises and effects remain mandatory.
#guard (match actual 0 4 false false .unusedElse with | .ok (.error .request,_) => true | _ => false)
#guard (match actual 1 4 false false .unitaryHeader with | .ok (.error .request,_) => true | _ => false)

-- Two distinct Bit owners may have the same width. Only the original q role
-- is consumed; a still-valid Raw mutant measuring a must not change that map.
#guard accepted (actual 1 4 true false .none) == some (expected 1)
#guard (match actual 1 4 true true .none with | .ok (.error .invalid,_) => true | _ => false)

end QleisliKernel.Tests.RuntimeStaticBasisNatObserving
