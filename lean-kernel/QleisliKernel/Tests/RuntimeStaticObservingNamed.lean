import QleisliKernel.Qirf.RuntimeBodyGraph

/-! One original observing named call in a static selected arm uses the same
runtime step, actual SSA and complete lazy-history/output gate. The preserved
first sources contain one Bit owner plus a Unit spectator, or two Bit owners
for the equal-width consumption fault. These controls issue no handle and do
not discharge the remaining quantum/instrument composition obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStaticObservingNamed
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def source := "#![no_implicit_prelude]\n" ++
  "observe fn read(q:Q<Bit>)->Bit{measure_z(q)}\n" ++
  "pub observe fn route[const n:Nat](u:Q<Unit>,q:Q<Bit>)->(Bit,Q<Unit>){\n" ++
  "    let b=if static n==0{read(q)}else{read(q)};\n    (b,u)\n}\n"

private def swapSource := "#![no_implicit_prelude]\n" ++
  "observe fn read(q:Q<Bit>)->Bit{measure_z(q)}\n" ++
  "pub observe fn route[const n:Nat](u:Q<Unit>,a:Q<Bit>,b:Q<Bit>)->(Bit,Q<Bit>,Q<Unit>){\n" ++
  "    let v=if static n==0{read(b)}else{read(b)};\n    (v,a,u)\n}\n"

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

private inductive Fault where
  | none | inverted | spectator | parentOffset | childOffset | unitaryHeader | missingMeasurement | otherArm
  deriving BEq

private structure Observation where
  issued : List Nat
  retired : List Nat
  ordinal : Nat
  owners : List Nat
  tokens : List Nat
  actions : Nat
  steps : Nat
  measuredOwners : List Nat
  callDepths : List Nat
  originalKeys : Bool
  histories : List Nat
  deriving BEq, Repr

private def actual (n : Nat) (fault : Fault) (twoBits wrongConsumed : Bool) : WorkM Observation := do
  let text := if twoBits then swapSource else source
  let text := if fault == .unitaryHeader then text.replace "pub observe fn route" "pub unitary fn route" else text
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let first : Semantics.Raw.Port := ⟨1,[0],1⟩
  let second : Semantics.Raw.Port := ⟨2,[1],1⟩
  let measured := if twoBits && !wrongConsumed then 2 else 1
  let returned := if wrongConsumed then second else first
  let output := if twoBits then 3 else if fault == .inverted then 3 else 2
  let operations : List Semantics.Observation.Op :=
    (if fault == .spectator then [.discard 0] else []) ++
    (if fault == .missingMeasurement then [.discard measured,.constant false output]
      else [.measure measured (if twoBits then 3 else 2)]) ++
    (if fault == .inverted then [.not 2 3] else [])
  let outputs := if twoBits then [returned.token,0] else if fault == .spectator then [] else [0]
  let program : Semantics.Observation.Program :=
    ⟨if twoBits then [unit,first,second] else [unit,first],[],operations,outputs,[output],.observe⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let arguments : StaticTypes.Arguments := {naturals := [("n",n)]}
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" arguments
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.staticConditional event _] := body.checked.events | throw .request
  let selected ← SourceRuntimeTrace.readStaticSource event
  let [.named call] := selected.result.events | throw .request
  let callee ← SourceRuntimeTrace.readNamedBody call
  let [.primitive measurement] := callee.checked.events | throw .request
  let [other] := if event.selection.selected then event.elseCalls else event.thenCalls | throw .request
  let parent : SourceSequence.Position := ⟨event.written.parts.keyword.span.startByte,0,operations.length⟩
  let callPosition : SourceSequence.Position :=
    ⟨if fault == .parentOffset then parent.offset else if fault == .otherArm then other else call.call.calleeOffset,
      0,operations.length⟩
  let measurePosition : SourceSequence.Position :=
    ⟨if fault == .childOffset then call.call.calleeOffset else measurement.call.calleeOffset,
      if fault == .spectator then 1 else 0,1⟩
  let context : RuntimeContextRequest.Context := .mk [parent] []
    [(callPosition,.mk [measurePosition] [] [] [] [])] [] []
  let inputStorage : List Semantics.RuntimeStorage.Value := if twoBits then
    [[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨first,[.bit]⟩],[.quantum ⟨second,[.bit]⟩]]
    else [[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨first,[.bit]⟩]]
  let storage : Semantics.RuntimeStorage.Value := if twoBits then
    [.tuple 3,.ordinary [.bit] (.bit output),.quantum ⟨returned,[.bit]⟩,.quantum ⟨unit,[.unit]⟩]
    else [.tuple 2,.ordinary [.bit] (.bit output),.quantum ⟨unit,[.unit]⟩]
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",signature.parameters.map (·.tree),inputStorage,[[]],signature.result.tree,
      storage,.observe,arguments⟩
  let checked ← RuntimeBodyGraph.prepareRuntime artifact #[0] "main" "route" arguments context runtime
  let measurements := checked.derivation.result.ordinary.measurements
  let expectedOrigin : Semantics.SourceOrdinary.Site := ⟨"main","read",measurement.call.calleeOffset⟩
  let expectedCall : Semantics.SourceOrdinary.Site := ⟨"main","route",call.call.calleeOffset⟩
  let expectedOwner := if twoBits then 2 else 1
  return ⟨checked.derivation.result.history.issued.map (·.ordinal),
    checked.derivation.result.retired.map (·.ordinal),checked.derivation.result.history.nextOrdinal,
    checked.derivation.result.bindings.map (·.owner.ordinal),checked.derivation.result.bindings.map (·.port.token),
    checked.derivation.result.actions.length,checked.derivation.result.steps.length,
    measurements.map (·.owner.ordinal),measurements.map (·.calls.length),
    measurements.all (fun measured => decide (measured.origin = expectedOrigin ∧ measured.calls = [expectedCall] ∧
      measured.owner.ordinal = expectedOwner)),
    historyCounts ((OrdinaryDomain.assignments checked.initial.domain).length+1) checked.ordinary.rows⟩

private def expected : Observation := ⟨[0,1],[1],2,[0],[0],0,1,[1],[1],true,[2]⟩

-- Both distinct original arm-call offsets feed the same common runtime step.
-- No pure action stands for the observing call; both lazy outcomes remain.
#guard (actual 0 .none false false).run 10000000 |>.1.toOption == some expected
#guard (actual 1 .none false false).run 10000000 |>.1.toOption == some expected

-- The unchanged actual instrument/output gate checks every outcome. Negating
-- the returned measured bit cannot pass by agreeing on a sampled history.
#guard (match (actual 1 .inverted false false).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (actual 1 .spectator false false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (actual 1 .missingMeasurement false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 .parentOffset false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 .childOffset false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 .otherArm false false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (actual 1 .unitaryHeader false false).run 10000000 with | (.error .request,_) => true | _ => false)

-- Both proposed Raw programs consume one Bit and return the other, with the
-- same widths. Only the original consumed-owner identity is admissible.
#guard (actual 1 .none true false).run 10000000 |>.1.toOption ==
  some ⟨[0,1,2],[2],3,[1,0],[1,0],0,1,[2],[1],true,[2]⟩
#guard (match (actual 1 .none true true).run 10000000 with | (.error .request,_) => true | _ => false)

private def pureContinuation (sequence : Bool) : WorkM Unit := do
  let signature ← SourceRuntimeContext.readSignature #[("main",source)] "main" "route" {naturals := [("n",1)]}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.staticConditional event _] := body.checked.events | throw .request
  if sequence then
    let _ ← RuntimeStaticPrimitive.readSequence event
    pure ()
  else
    let _ ← RuntimeStaticPrimitive.readSource event
    pure ()

-- The separate old pure APIs still refuse source consumption.
#guard (match (pureContinuation false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (pureContinuation true).run 10000000 with | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.RuntimeStaticObservingNamed
