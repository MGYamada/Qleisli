import QleisliKernel.Qirf.RuntimeBodyGraph

/-! Source-bound selected event composition through the same runtime step.
Both original static arms retain phase followed by an observing Basis/Nat call.
The first native-only observer recovered both source events and Raw-valid
candidates, but the singleton eligibility barrier refused their composition.
These strict controls keep the exact first source and literal request partition,
separate held Unit owners, original actuals/effects and every hidden history.
Each native checker starts with fixed 10M after plain payload construction; no
producer proof, Body or accepted result is supplied. Other source forms, owner
allocation, operation actuals and full instrument composition remain separate.
No native handle, wire or dispatcher is enabled.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStaticEvents
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def source := "#![no_implicit_prelude]\nuse helpers::next;\nobserve fn read[const A:Basis,const j:Nat,const k:Nat,const unused:Nat](a:Q<A>,q:Q<Bit>)->(Bit,Q<A>)\nrequires k>=1,unused>=1 { let q=phase[j,k](q); (measure_z(q),a) }\npub observe fn route[const A:Basis,const n:Nat](u:Q<Unit>,a:Q<A>,q:Q<Bit>)->(Bit,Q<A>,Q<Unit>){\n    static let denominator=next[0]();\n    let (b,r)=if static n==0{\n        let q=phase[1,2](q);\n        read[A,1,denominator,1](a,q)\n    }else{\n        let q=phase[1,2](q);\n        read[A,1,denominator,1](a,q)\n    };\n    (b,r,u)\n}\n"

private def helper := "#![no_implicit_prelude]\npub static fn next[const n:Nat]()->Nat{n+1}\n"

private inductive Fault where
  | none | inverted | missingMeasurement | parentOffset | childOffset | otherArm
  | unitaryHeader | unusedElse | denominator | callOverlap | callShort | outerOffset
  deriving BEq

private def text (fault : Fault) : String :=
  if fault == .unitaryHeader then source.replace "pub observe fn route" "pub unitary fn route"
  else if fault == .unusedElse then
    source.replace "read[A,1,denominator,1](a,q)\n    };" "read[A,1,denominator,0](a,q)\n    };"
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

private def sourceEvents (n : Nat) (twoBits : Bool) :
    WorkM (Bool × List Nat × List Nat × Nat × List (String × Nat) × List (String × Nat) × Bool) := do
  let sources := #[("main",source),("helpers",helper)]
  let signature ← SourceRuntimeContext.readSignature sources "main" "route" (arguments n twoBits)
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.staticConditional event _] := body.checked.events | throw .request
  let selected ← SourceRuntimeTrace.readStaticSource event
  let [.phase phase,.named call] := selected.result.events | throw .request
  return (event.selection.selected,[phase.call.calleeOffset,call.call.calleeOffset],
    selected.result.consumed.map (·.ordinal),selected.result.nextOrdinal,
    call.target.actuals.actuals.map (fun actual => (actual.formal.name,actual.formal.ordinal)),
    call.target.signature.arguments.naturals,
    decide (call.target.signature.arguments.bases = (arguments n twoBits).bases))

private def namedActuals {dependencies program block} (basis : Semantics.FiniteCarrier.Basis) :
    RuntimePureBody.Step dependencies program block → List (List (String × Nat) × Bool × Option Semantics.Raw.Effect)
  | .named _ _ body _ _ _ _ => [(body.checked.signature.arguments.naturals,
      decide (body.checked.signature.arguments.bases = [("A",basis)]),body.checked.signature.original.parsedHeader.effect)]
  | _ => []

private structure Payload where
  artifact : Qirf.Artifact
  context : RuntimeContextRequest.Context
  runtime : RuntimeFamily.Request

/-- These are untrusted literal request fields. Lexing supplies byte locations
only. Native source/body/effect/owner/history checks must independently run. -/
private def literal (n outerExponent callExponent : Nat) (twoBits wrongConsumed : Bool) (fault : Fault) :
    Except String Payload := do
  let current := text fault
  let basis : Semantics.FiniteCarrier.Basis := if twoBits then [.bit] else [.unit]
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let a : Semantics.Raw.Port := ⟨1,if twoBits then [0] else [],if twoBits then 1 else 0⟩
  let q : Semantics.Raw.Port := ⟨2,[if twoBits then 1 else 0],1⟩
  let afterPrefix : Semantics.Raw.Port := ⟨3,q.wires,1⟩
  let chosen := if wrongConsumed then a else afterPrefix
  let returned := if wrongConsumed then afterPrefix else a
  let output := if fault == .inverted then 6 else 5
  let operations : List Semantics.Observation.Op :=
    [.pure (.applyUnitary q.token 3 [⟨[],.monomial [0] [0,1] [0,outerExponent]⟩]),
     .pure (.applyUnitary chosen.token 4 [⟨[],.monomial [0] [0,1] [0,callExponent]⟩])] ++
    (if fault == .missingMeasurement then [.discard 4,.constant false 5] else [.measure 4 5]) ++
    (if fault == .inverted then [.not 5 6] else [])
  let program : Semantics.Observation.Program := ⟨[unit,a,q],[],operations,[returned.token,0],[output],.observe⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",current),("helpers",helper)],0,none⟩
  let tokens ← lexLocated current
  let some keyword := tokens.find? (·.text == "if") | throw "missing original if"
  let [_declaration,thenCall,elseCall] := tokens.filter (·.text == "read") | throw "original read occurrence count"
  let [leafPhase,thenPhase,elsePhase] := tokens.filter (·.text == "phase") | throw "original phase occurrence count"
  let some measure := tokens.find? (·.text == "measure_z") | throw "missing original measurement"
  let selected := if n == 0 then thenCall.span.startByte else elseCall.span.startByte
  let other := if n == 0 then elseCall.span.startByte else thenCall.span.startByte
  let prefixOffset := if n == 0 then thenPhase.span.startByte else elsePhase.span.startByte
  let parent : SourceSequence.Position :=
    ⟨if fault == .outerOffset then prefixOffset else keyword.span.startByte,0,operations.length⟩
  let position : SourceSequence.Position :=
    ⟨if fault == .parentOffset then keyword.span.startByte else if fault == .otherArm then other else selected,
      if fault == .callOverlap then 0 else 1,
      if fault == .callShort then 1 else if fault == .callOverlap then operations.length else operations.length-1⟩
  let phasePosition : SourceSequence.Position := ⟨leafPhase.span.startByte,0,1⟩
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

private def observe (n outerExponent callExponent : Nat) (twoBits wrongConsumed : Bool) (fault : Fault) :
    Except String (Except Finite.Error NativeSummary × Nat) := do
  let payload ← literal n outerExponent callExponent twoBits wrongConsumed fault
  pure ((native payload).run 10000000)

private def raw (twoBits wrongConsumed : Bool) : Except String (Except Finite.Error Unit × Nat) := do
  let payload ← literal 1 2 4 twoBits wrongConsumed .none
  let some program := payload.artifact.programs[0]? | throw "missing literal program"
  let check : WorkM Unit := do
    let _ ← Raw.Observation.verify [] program
    pure ()
  pure (check.run 10000000)

private def accepted {α : Type} (attempt : Except String (Except Finite.Error α × Nat)) : Option α :=
  match attempt with | .ok (.ok value,_) => some value | _ => none

private def expected (k : Nat) : NativeSummary :=
  ([0,1,2],[2],3,[1,0],[1,0],[(2,1)],[2],true,true,
    [([("j",1),("k",k),("unused",1)],true,some .observe)],1,2)

-- These exact original source offsets and mixed ordinals were observed before
-- changing eligibility or interval partitioning. Source counters are separate.
#guard (sourceEvents 0 false).run 10000000 |>.1.toOption == some (true,[388,411],[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)
#guard (sourceEvents 1 false).run 10000000 |>.1.toOption == some (false,[465,488],[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)
#guard (sourceEvents 1 true).run 10000000 |>.1.toOption == some (false,[465,488],[2],3,
  [("A",0),("j",1),("k",2),("unused",3)],[("j",1),("k",1),("unused",1)],true)

-- A wrong consumed role is a genuine Raw-valid two-Bit mutation.
#guard (match raw true false with | .ok (.ok (),_) => true | _ => false)
#guard (match raw true true with | .ok (.ok (),_) => true | _ => false)

#guard accepted (observe 0 2 4 false false .none) == some (expected 1)
#guard accepted (observe 1 2 4 false false .none) == some (expected 1)
#guard accepted (observe 1 2 4 true false .none) == some (expected 1)
#guard accepted (observe 1 2 2 false false .denominator) == some (expected 2)
#guard (match observe 1 0 4 false false .none with | .ok (.error .equation,_) => true | _ => false)
#guard (match observe 1 2 0 false false .none with | .ok (.error .equation,_) => true | _ => false)
#guard (match observe 1 2 4 false false .inverted with | .ok (.error .equation,_) => true | _ => false)
#guard (match observe 1 2 4 false false .denominator with | .ok (.error .equation,_) => true | _ => false)
#guard (match observe 1 2 4 true true .none with | .ok (.error .invalid,_) => true | _ => false)

-- The exact child context must partition the parent contiguously, retain its
-- own original occurrence and account for the real measurement instruction.
#guard (match observe 1 2 4 false false .callOverlap with | .ok (.error .request,_) => true | _ => false)
#guard (match observe 1 2 4 false false .callShort with | .ok (.error .request,_) => true | _ => false)
#guard (match observe 1 2 4 false false .parentOffset with | .ok (.error .request,_) => true | _ => false)
#guard (match observe 1 2 4 false false .childOffset with | .ok (.error .request,_) => true | _ => false)
#guard (match observe 1 2 4 false false .otherArm with | .ok (.error .request,_) => true | _ => false)
#guard (match observe 1 2 4 false false .outerOffset with | .ok (.error .request,_) => true | _ => false)
#guard (match observe 1 2 4 false false .missingMeasurement with | .ok (.error .request,_) => true | _ => false)

-- Selected execution never erases original inactive-arm or public-effect duties.
#guard (match observe 0 2 4 false false .unusedElse with | .ok (.error .request,_) => true | _ => false)
#guard (match observe 1 2 4 false false .unitaryHeader with | .ok (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.RuntimeStaticEvents
