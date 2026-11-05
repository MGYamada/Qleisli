import QleisliKernel.Qirf.RuntimeBodyGraph
import QleisliKernel.Tests.SourceTraceOriginals

/-! Ordinary branches use actual original named calls and fresh native phis.
The source and literal data are retained from calls-agent-first/
ordinary-branch-calls-native-first/Observe-fresh-phi.lean (SHA-256
4816bb239697b8651fb47537a5d50967c1c24695ba85a246669b22b88479230e).
The first reserved-name harness failure and original bad Raw wire payload are
preserved separately. Root genuinely checked all three corrected Raw payloads
before this connection; their native branch path then refused with request.
The bundled original's distinct invalid outcome is preserved as a benchmark,
not relabelled a success of this no-prelude executable translation. Every
native guard runs real prepareRuntime from plain data at a fresh 10M; source
metadata/Raw checks have separate counters and confer no checker authority.
No observation inside an arm, wire dispatch, whole-code equation or handle is
admitted by these component controls.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOrdinaryBranchCalls
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def original := "pub unitary fn route(c: Bit, a: Q<Bit>, b: Q<Bit>) -> (Q<Bit>,Q<Bit>) {\n    if c { (a,h(b)) } else { (b,h(a)) }\n}\n"

private def named := "#![no_implicit_prelude]\nunitary fn turn(q:Q<Bit>)->Q<Bit>{h(q)}\npub unitary fn route(c:Bit,a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){\n    if c{(a,turn(b))}else{(b,turn(a))}\n}\n"

private def external := "#![no_implicit_prelude]\nuse lib::turn;\npub unitary fn route(c:Bit,a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){\n    if c{(a,turn(b))}else{(b,turn(a))}\n}\n"

private def library := "#![no_implicit_prelude]\npub observe fn turn(q:Q<Bit>)->Q<Bit>{h(q)}\n"

private inductive Form where
  | original | named | localObserve | externalObserve
  deriving BEq

private inductive Fault where
  | none | wrongGate | wrongElsePhi | invertedCondition | otherArm | childScope | missingBranch
  deriving BEq

private def text : Form → String
  | .original => original
  | .named => named
  | .localObserve => named.replace "unitary fn turn" "pub observe fn turn"
  | .externalObserve => external

private def sources (form : Form) : Sources :=
  #[("main",text form)] ++
    (if form == .original then SourceTraceOriginals.bundled
     else if form == .externalObserve then #[("lib",library)] else #[])

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

private def sourceShape (form : Form) : WorkM
    (List Nat × List Nat × Nat × List (Nat × Nat × Nat) × List Nat × List Nat ×
      List Semantics.Raw.Effect × List (Option Semantics.Raw.Effect)) := do
  let signature ← SourceRuntimeContext.readSignature (sources form) "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.conditional event left right] := body.checked.events | throw .request
  let headers := (left ++ right).map fun event => match event with
    | .named call => call.target.signature.original.parsedHeader.effect
    | _ => none
  return (SourceRuntimeValues.valueOwners body.checked.summary.value |>.map (·.ordinal),
    body.checked.summary.consumed.map (·.ordinal),body.checked.summary.nextOrdinal,
    event.phis.map (fun phi => (phi.output.ordinal,phi.thenOwner.ordinal,phi.elseOwner.ordinal)),
    left.map (·.offset),right.map (·.offset),(left ++ right).map (·.effect),headers)

private structure Payload where
  artifact : Qirf.Artifact
  context : RuntimeContextRequest.Context
  runtime : RuntimeFamily.Request

private def literal (form : Form) (fault : Fault) : Except String Payload := do
  let current := text form
  let first : Semantics.Raw.Port := ⟨1,[0],1⟩
  let second : Semantics.Raw.Port := ⟨2,[1],1⟩
  let outputFirst : Semantics.Raw.Port := ⟨5,[2],1⟩
  let outputSecond : Semantics.Raw.Port := ⟨6,[3],1⟩
  let preamble : List Semantics.Observation.Op := if fault == .invertedCondition then [.not 0 7] else []
  let condition := if fault == .invertedCondition then 7 else 0
  let thenOps : List Semantics.Observation.Op := [.pure (.gate (if fault == .wrongGate then .x else .h) 2 3)]
  let elseOps : List Semantics.Observation.Op := [.pure (.gate .h 1 4)]
  let quantum : List Semantics.Observation.QuantumPhi :=
    [⟨1,if fault == .wrongElsePhi then 4 else 2,5,[2]⟩,
     ⟨3,if fault == .wrongElsePhi then 2 else 4,6,[3]⟩]
  let operations := preamble ++ [.branch condition thenOps elseOps quantum []]
  let program : Semantics.Observation.Program := ⟨[first,second],[0],operations,[5,6],[],.unitary⟩
  let tokens ← lexLocated current
  let some keyword := tokens.find? (·.text == "if") | throw "missing original branch"
  let (thenOffset,elseOffset,childOffset) ← if form == .original then do
      let [left,right] := tokens.filter (·.text == "h") | throw "original h occurrence count"
      pure (left.span.startByte,right.span.startByte,0)
    else if form == .externalObserve then do
      let [_import,left,right] := tokens.filter (·.text == "turn") | throw "import and call occurrence count"
      let leaf ← lexLocated library
      let some h := leaf.find? (·.text == "h") | throw "missing external original h"
      pure (left.span.startByte,right.span.startByte,h.span.startByte)
    else do
      let [_declaration,left,right] := tokens.filter (·.text == "turn") | throw "original turn occurrence count"
      let some h := tokens.find? (·.text == "h") | throw "missing original helper h"
      pure (left.span.startByte,right.span.startByte,h.span.startByte)
  let parent : SourceSequence.Position := ⟨keyword.span.startByte,preamble.length,1⟩
  let left : SourceSequence.Position := ⟨if fault == .otherArm then elseOffset else thenOffset,0,1⟩
  let right : SourceSequence.Position := ⟨if fault == .otherArm then thenOffset else elseOffset,0,1⟩
  let child : RuntimeContextRequest.Context := .mk
    [⟨if fault == .childScope then thenOffset else childOffset,0,1⟩] [] [] [] []
  let leftContext : RuntimeContextRequest.Context := .mk [left] []
    (if form == .original then [] else [(left,child)]) [] []
  let rightContext : RuntimeContextRequest.Context := .mk [right] []
    (if form == .original then [] else [(right,child)]) [] []
  let context : RuntimeContextRequest.Context := .mk [parent] [] []
    (if fault == .missingBranch then [] else [(parent,leftContext,rightContext)]) []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",[Semantics.RuntimeType.ordinary [.bit],Semantics.RuntimeType.owner [.bit],
        Semantics.RuntimeType.owner [.bit]],
      [[.ordinary [.bit] (.bit 0)],[.quantum ⟨first,[.bit]⟩],[.quantum ⟨second,[.bit]⟩]],
      [[false],[true]],Semantics.RuntimeType.tuple 2 [Semantics.RuntimeType.owner [.bit],Semantics.RuntimeType.owner [.bit]],
      [.tuple 2,.quantum ⟨outputFirst,[.bit]⟩,.quantum ⟨outputSecond,[.bit]⟩],.unitary,{}⟩
  return ⟨⟨#[program],#[],sources form,0,none⟩,context,runtime⟩

private abbrev Summary := List Nat × List Nat × Nat × List Nat × List Nat × List Nat × Nat × Nat × Nat

private def native (payload : Payload) : WorkM Summary := do
  let checked ← RuntimeBodyGraph.prepareRuntime payload.artifact #[0] "main" "route" {} payload.context payload.runtime
  return (checked.derivation.result.history.issued.map (·.ordinal),checked.derivation.result.retired.map (·.ordinal),
    checked.derivation.result.history.nextOrdinal,checked.derivation.result.bindings.map (·.owner.ordinal),
    checked.derivation.result.bindings.map (·.port.token),
    historyCounts ((OrdinaryDomain.assignments checked.initial.domain).length+1) checked.ordinary.rows,
    checked.derivation.result.ordinary.measurements.length,checked.derivation.result.actions.length,
    checked.derivation.result.steps.length)

private def observe (form : Form) (fault : Fault) : Except String (Except Finite.Error Summary × Nat) := do
  let payload ← literal form fault
  pure ((native payload).run 10000000)

private def raw (fault : Fault) : Except String (Except Finite.Error Unit × Nat) := do
  let payload ← literal .named fault
  let some program := payload.artifact.programs[0]? | throw "missing literal program"
  let checked : WorkM Unit := do
    let _ ← Raw.Observation.verify [] program
    pure ()
  pure (checked.run 10000000)


private def rawAccepted (fault : Fault) : Bool :=
  match raw fault with | .ok (.ok (),_) => true | _ => false

private def correct (form : Form) : Bool :=
  match observe form .none with
  | .ok (.ok result,_) => result == ([0,1,2,3],[1,0],4,[2,3],[5,6],[1,1],0,0,1)
  | _ => false

private def equation (fault : Fault) : Bool :=
  match observe .named fault with | .ok (.error .equation,_) => true | _ => false

private def refused (form : Form) (fault : Fault) : Bool :=
  match observe form fault with | .ok (.error .request,_) => true | _ => false

-- Wrong phis and the inverted actual condition are independently valid Raw;
-- neither ownership rejection nor malformed payload masks their source error.
#guard rawAccepted .none
#guard rawAccepted .wrongElsePhi
#guard rawAccepted .invertedCondition
#guard correct .named
#guard correct .localObserve
#guard equation .wrongGate
#guard equation .invertedCondition
#guard refused .named .wrongElsePhi
#guard refused .named .otherArm
#guard refused .named .childScope
#guard refused .named .missingBranch
#guard refused .externalObserve .none

-- Same-original-module precise inference leaves the exported Observe label
-- intact. Cross-original-module callers retain its public contract instead.
#guard (sourceShape .localObserve).run 10000000 |>.1.toOption ==
  some ([2,3],[1,0],4,[(2,0,1),(3,1,0)],[144],[161],
    [.unitary,.unitary],[some .observe,some .observe])
#guard (match (sourceShape .externalObserve).run 10000000 with
  | (.error .request,_) => true | _ => false)

private def observingArms : Except String Payload := do
  let current := "#![no_implicit_prelude]\nobserve fn read(q:Q<Bit>)->Bit{measure_z(q)}\npub observe fn route(c:Bit,q:Q<Bit>)->Bit{if c{read(q)}else{read(q)}}"
  let input : Semantics.Raw.Port := ⟨0,[0],1⟩
  let program : Semantics.Observation.Program :=
    ⟨[input],[0],[.branch 0 [.measure 0 1] [.measure 0 2] [] [⟨1,2,3⟩]],[],[3],.observe⟩
  -- Offsets come only from the untouched original lexed data; this total
  -- proposal constructor supplies no source result or native read receipt.
  let tokens ← lexLocated current
  let some keyword := tokens.find? (·.text == "if") | throw "missing original if"
  let [_definition,left,right] := tokens.filter (·.text == "read") | throw "original read occurrences"
  let some measure := tokens.find? (·.text == "measure_z") | throw "original measure occurrence"
  let position : SourceSequence.Position := ⟨keyword.span.startByte,0,1⟩
  let thenCall : SourceSequence.Position := ⟨left.span.startByte,0,1⟩
  let elseCall : SourceSequence.Position := ⟨right.span.startByte,0,1⟩
  let child : RuntimeContextRequest.Context := .mk [⟨measure.span.startByte,0,1⟩] [] [] [] []
  let context : RuntimeContextRequest.Context := .mk [position] [] []
    [(position,.mk [thenCall] [] [(thenCall,child)] [] [],
      .mk [elseCall] [] [(elseCall,child)] [] [])] []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",[Semantics.RuntimeType.ordinary [.bit],Semantics.RuntimeType.owner [.bit]],
      [[.ordinary [.bit] (.bit 0)],[.quantum ⟨input,[.bit]⟩]],[[false],[true]],
      Semantics.RuntimeType.ordinary [.bit],[.ordinary [.bit] (.bit 3)],.observe,{}⟩
  return ⟨⟨#[program],#[],#[("main",current)],0,none⟩,context,runtime⟩

private def observingArmsRaw : Bool :=
  match observingArms with
  | .error _ => false
  | .ok payload =>
    match payload.artifact.programs[0]? with
    | none => false
    | some program => match (Raw.Observation.verify [] program).run 10000000 with
      | (.ok _,_) => true | _ => false

private def observingArmsRefused : Bool :=
  match observingArms with
  | .error _ => false
  | .ok payload => match (native payload).run 10000000 with
    | (.error .request,_) => true | _ => false

-- Observing descendants remain outside this bounded arm connection. Both
-- source arms and actual Raw histories still exist; there is no pure fallback.
#guard observingArmsRaw
#guard observingArmsRefused

end QleisliKernel.Tests.RuntimeOrdinaryBranchCalls
