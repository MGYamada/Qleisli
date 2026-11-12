import Lean
import Protocol.ExecutionView.CheckedQmatch
import Protocol.ExecutionView.QmatchV5
import QleisliKernel.Qirf.RuntimeNamedSelectionSurroundings
import QleisliKernel.Qirf.RuntimeNamedCalls
import QleisliKernel.Qirf.RuntimeNamedCallsComposition
import QleisliKernel.Qirf.RuntimeLinkedSubject
import QleisliKernel.Qirf.RuntimePreparedArm
import QleisliKernel.Qirf.RuntimeBodyOperations
import QleisliKernel.Qirf.RuntimeNamedFrameAxes
import QleisliKernel.Qirf.RuntimeNamedPrimitiveOccurrence
import QleisliKernel.Qirf.RuntimeNamedThreeOccurrence
import QleisliKernel.Qirf.RuntimeSelectionWitness
import Protocol.NativeContext.Bindings
import QleisliKernel.Qirf.ContextSector

/-! Independent shared data expectations for the actual named-arm protocol.
The QLV3 comparison and context-dispatch definitions run directly; fresh native
compilation and Rust accepted-handle tests remain separate obligations. The
scalar controls retain Unit owners; nominal three/four-label controls use two
selector bits and a zero-width target. Each controlled arm uses one Bit.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
open Lean QleisliKernel QleisliKernel.Protocol.ExecutionView

private def value (fuel : Nat) : Json → Except String Value :=
  Nat.rec (fun _ => throw "qmatch vector depth") (fun _ recurse input => do
    match input with
    | .null => return .null
    | .bool b => return .boolean b
    | .num _ => return .natural (← input.getNat?)
    | .str s => return .text s
    | .arr xs => return .array (← xs.toList.mapM recurse)
    | .obj _ => throw "qmatch view contains an object") fuel

private def u32 (value : Nat) : ByteArray :=
  ⟨((List.range 4).map (fun index => (value / 256^index % 256).toUInt8)).toArray⟩

private def packet (body required : ByteArray) : ByteArray :=
  "QLV1".toUTF8 ++ u32 body.size ++ u32 required.size ++ body ++ required

private def envelope (original graph : ByteArray) (scope : Nat := 1) : ByteArray :=
  "QLV3".toUTF8 ++ u32 2026 ++ u32 scope ++ u32 original.size ++ u32 graph.size ++
    u32 0 ++ u32 0 ++ original ++ graph

private def cases (path : System.FilePath) : IO (Array Json) := do
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept ((parsed.getObjVal? "cases") >>= Json.getArr?)

private def qmatchWork := Protocol.NativeContext.Mode.qmatchSource.workLimit

-- Exercise the production counter on both modes, including a failed debit
-- after earlier work. No large matrix is needed to reach the numeric boundary.
#guard [Protocol.NativeContext.Mode.ordinary,.qmatchSource].all fun mode =>
  mode.workLimit == 20000000 &&
    (match (Exact.charge 20000000).run mode.workLimit with | (.ok (),0) => true | _ => false) &&
    (match (do Exact.charge 19999999; Exact.charge 2).run mode.workLimit with
      | (.error .workLimit,1) => true | _ => false)

-- These retained inputs predate explicit prelude lookup. Add its actual empty
-- module to the input and the expected source table. All offsets stay original.
private def fixtureArtifact (artifact : Json) : Except String Json := do
  let sources ← (← artifact.getObjVal? "sources").getArr?
  let prelude := Json.mkObj [("path",.str "std::prelude"),("text",.str "")]
  return artifact.setObjVal! "sources" (.arr (sources.push prelude))

private def fixtureView (json : Json) : Except String Value := do
  let original ← value 129 json
  let .array (tag :: .array (a :: b :: c :: .array sources :: fields) :: rest) := original
    | return original
  let prelude := Value.array [.text "source",.text "std::prelude",.text ""]
  return .array (tag :: .array (a :: b :: c :: .array (sources ++ [prelude]) :: fields) :: rest)

private def shapes (path : System.FilePath) : IO Unit := do
  let rows ← cases path
  unless rows.size == 48 do throw (IO.userError "qmatch shape inventory changed")
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let text ← IO.ofExcept ((row.getObjVal? "text") >>= Json.getStr?)
    let expected ← IO.ofExcept ((row.getObjVal? "accepted") >>= Json.getBool?)
    let actual := ((Protocol.Qmatch.readRequest text.toUTF8).run qmatchWork).1.isOk
    unless actual == expected do throw (IO.userError ("qmatch data mismatch: " ++ name))
  IO.println "passed 48 shared Rust/Lean request shape expectations; parsing confers no acceptance"

private def execution (path : System.FilePath) (precise : Bool := false)
    (positive : Nat := 2) (negative : Nat := 24) : IO Unit := do
  let rows ← cases path
  unless rows.size == positive+negative do throw (IO.userError "qmatch execution inventory changed")
  let mut accepts := 0
  let mut refusals := 0
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let artifact ← IO.ofExcept ((row.getObjVal? "artifact") >>= fixtureArtifact)
    let required ← IO.ofExcept (row.getObjVal? "request")
    let original := packet artifact.compress.toUTF8 required.compress.toUTF8
    let supplied ← IO.ofExcept ((row.getObjVal? "view") >>= fixtureView >>= encode)
    let expected ← IO.ofExcept ((row.getObjVal? "accepted") >>= Json.getBool?)
    let framed := envelope original supplied
    let actual := (CheckedQmatch.run framed).run qmatchWork
    let dispatched := (Protocol.NativeContext.run .qmatchSource Protocol.productVersion framed).run qmatchWork
    unless dispatched.1.isOk == actual.1.isOk && dispatched.2 == actual.2 do
      throw (IO.userError ("qmatch context changed the original decision/work: " ++ name))
    match (Protocol.NativeContext.run .qmatchSource "wrong-product" framed).run qmatchWork with
    | (.error .version,left) => unless left == qmatchWork do throw (IO.userError "wrong product consumed work")
    | _ => throw (IO.userError "qmatch context accepted a different product")
    match actual.1 with
    | .ok checked =>
      unless expected && checked.body == artifact.compress.toUTF8 &&
          checked.requestBytes == required.compress.toUTF8 do
        throw (IO.userError ("qmatch original bytes/acceptance mismatch: " ++ name))
      accepts := accepts+1
      let .ok decision := dispatched.1 | throw (IO.userError "qmatch context lost successful input")
      let lines := Protocol.NativeContext.successLines .qmatchSource decision (qmatchWork-dispatched.2)
      unless lines.take 6 == ["qleisli.native-result 3","accepted","2026",Protocol.productVersion,
          "--qmatch-source-check","execution"] && lines.drop 7 == ["1"] do
        throw (IO.userError "qmatch response lost its actual context/request binding")
      match (Protocol.NativeContext.run .qmatchSource Protocol.productVersion
          (envelope original ByteArray.empty 0)).run qmatchWork with
      | (.error .packet,_) => pure ()
      | _ => throw (IO.userError "qmatch context accepted inspection scope")
      let caller ← IO.ofExcept (encode (.array []))
      let callerEnvelope := "QLV3".toUTF8 ++ u32 2026 ++ u32 2 ++ u32 original.size ++
        u32 supplied.size ++ u32 caller.size ++ u32 0 ++ original ++ supplied ++ caller
      match (Protocol.NativeContext.run .qmatchSource Protocol.productVersion callerEnvelope).run qmatchWork with
      | (.error .packet,_) => pure ()
      | _ => throw (IO.userError "qmatch context accepted caller scope")
      -- Valid original bytes and view grant no inspection/caller execution.
      for scope in [0,2] do
        match ((CheckedQmatch.input ⟨.e2026,if scope == 0 then .inspection else .caller,
            original,supplied,ByteArray.empty,[]⟩).run qmatchWork).1 with
        | .error .packet => pure ()
        | _ => throw (IO.userError "qmatch non-execution scope did not refuse at the scope gate")
      if ((CheckedQmatch.run (envelope original supplied)).run 0).1.isOk then
        throw (IO.userError "qmatch exhausted work accepted")
    | .error error =>
      if expected then throw (IO.userError ("qmatch valid original rejected: " ++ name ++ ": " ++ reprStr error))
      let kind ← IO.ofExcept ((row.getObjVal? "error") >>= Json.getStr?)
      let correct := match kind,error with
        | "decodedView",.decodedView => true
        | "native",.native _ => true
        | _,_ => false
      unless correct do throw (IO.userError ("qmatch wrong refusal stage: " ++ name ++ ": " ++ reprStr error))
      if precise then
        let code ← IO.ofExcept ((row.getObjVal? "native_code") >>= Json.getStr?)
        let correct := match code,error with
          | "equation",.native .equation => true
          | "request",.native .request => true
          | "decodedView",.decodedView => true
          | _,_ => false
        unless correct do throw (IO.userError ("qmatch wrong exact refusal: " ++ name ++ ": " ++ reprStr error))
      refusals := refusals+1
  unless accepts == positive && refusals == negative do throw (IO.userError "qmatch coverage changed")
  IO.println s!"passed {positive} exact controls and {negative} QLV3 source/body/evidence/view refusals, including actual context dispatch; fresh native compilation/handle tests remain separate"

-- tests/fixtures/qmatch_v030/frame-execution-cases.json keeps these data.
private def frames (path : System.FilePath) : IO Unit := do
  let rows ← cases path
  unless rows.size == 18 do throw (IO.userError "qmatch source-frame inventory changed")
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let artifact ← IO.ofExcept ((row.getObjVal? "artifact") >>= fixtureArtifact)
    let request ← IO.ofExcept (row.getObjVal? "request")
    let expected ← IO.ofExcept ((row.getObjVal? "expected") >>= Json.getBool?)
    let actual := (do
      let (artifact,order) ← Protocol.Qirf.readAll artifact.compress.toUTF8
      let request ← Protocol.Qmatch.decode request
      let _ ← Qirf.ContextSector.check artifact order
        request.source.moduleName request.source.functionName request.positions request.sites
      pure ()).run qmatchWork
    unless actual.1.isOk == expected do
      throw (IO.userError ("qmatch source-frame mismatch: " ++ name ++ ": " ++ reprStr actual.1))
    if !expected then
      let code ← IO.ofExcept ((row.getObjVal? "native_code") >>= Json.getStr?)
      let correct := match code,actual.1 with
        | "request",.error .request => true
        | "invalid",.error .invalid => true
        | "equation",.error .equation => true
        | _,_ => false
      unless correct do throw (IO.userError ("qmatch source-frame wrong refusal: " ++ name))
  IO.println "passed 18 original structural source/frame/arm/code checks; paired native/QDV and compiler integration remain separate"

/-! Transport regression for the original named choose[then_op(sign,sign)] around its joined Raw
selection. Literal plain data is retained from the real Rust artifact/request;
no source proof, accepted result or external study file is a runtime input.
Each run freshly decodes and reads all original source, the distinct header
prefix, both arms and Meaning, one graph and the complete named caller return.

The first full named run, including its execution view, used 12,920,614
work units under the former 13M profile. The separate 16M component study
checks the held-owner example and its late rejection paths.
Remaining catalogue/global duties and broader source preservation stay open.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeNamedSelectionBoundary
open QleisliKernel Finite SourceTypes Qirf

private inductive Fault where
  | none | staleCaller | staleChild | missingChild | wrongArguments | wrongReturn | wrongSignature
  | heldUnit | droppedHeldUnit | wrongHeldValue | externalObserve
  | falseMeaning | changedControlled | wrongReferenceSlot | extraProviderReferences
  deriving BEq, Repr

abbrev Context := RuntimeContextRequest.Context
abbrev Position := SourceSequence.Position
abbrev Request := Protocol.QmatchV5.Request
abbrev Summary := List Nat × List Nat × List Nat × Nat × Nat × Nat

private def replaceChildPosition (child : Context) (position : Position) : Context :=
  .withReferences [position] (child.sites.map fun site => {site with position := position})
    child.calls child.branches child.bodies child.references child.staticIntervals

private def replaceParent (request : Request) (position : Position) (child : Context) : Request :=
  {request with context := .mk [position] [] [(position,child)] [] []}

private def originalRoute := "pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){\n    "
private def heldRoute := "pub unitary fn route(u:Q<Unit>,s:Q<Bit>,q:Q<Bit>)->(Q<Unit>,(Q<Bit>,Q<Bit>)){\n    (u,"
private def heldPort : Semantics.Raw.Port := ⟨6,[],0⟩

private def withHeldUnit (artifact : Artifact) (request : Request) (position : Position)
    (child : Context) (fault : Fault) : Except String (Artifact × Request) := do
  let some text := artifact.sources[0]? | throw "missing main source"
  let text := (text.2.replace originalRoute heldRoute).replace "](s,q)\n}" "](s,q))\n}"
  let some program := artifact.programs[0]? | throw "missing caller program"
  let program := {program with inputs := heldPort :: program.inputs, outputs := if fault == .droppedHeldUnit then program.outputs else heldPort.token :: program.outputs}
  let artifact := {artifact with programs := artifact.programs.set! 0 program, sources := #[("main",text)]}
  let runtime := request.runtime
  let unitTree := Semantics.RuntimeType.owner [.unit]
  let returned := if fault == .wrongHeldValue then {heldPort with token := 7} else heldPort
  let runtime := {runtime with parameters := unitTree :: runtime.parameters, inputStorage := [.quantum ⟨heldPort,[.unit]⟩] :: runtime.inputStorage, result := Semantics.RuntimeType.tuple 2 [unitTree,runtime.result], storage := [.tuple 2,.quantum ⟨returned,[.unit]⟩] ++ runtime.storage}
  let position := {position with offset := position.offset+heldRoute.utf8ByteSize-originalRoute.utf8ByteSize}
  return (artifact,replaceParent {request with runtime := runtime} position child)

private def externalSource (artifact : Artifact) (request : Request) (position : Position)
    (child : Context) : Except String (Artifact × Request) := do
  let some row := artifact.sources[0]? | throw "missing original source"
  let before :: _ := row.2.splitOn "pub unitary fn route" | throw "missing original route"
  let helper := (before.replace "unitary fn sign" "pub unitary fn sign").replace
    "unitary fn choose" "pub observe fn choose"
  let routePrefix := "#![no_implicit_prelude]\nuse helper::choose;\nuse helper::sign;\npub observe fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){\n    "
  let main := routePrefix ++ "choose[then_op(sign,sign)](s,q)\n}\n"
  let some program := artifact.programs[0]? | throw "missing caller program"
  let programs := artifact.programs.set! 0 {program with effect := .observe}
  let entries := artifact.entries.map fun entry => {entry with implementationName := "helper::sign", specificationName := "helper::sign", sources := [1]}
  let artifact := {artifact with programs := programs, entries := entries, sources := #[("main",main),("helper",helper)]}
  let phaseBodies := child.bodies.map fun (subject,body) =>
    let shift (pos : Position) := {pos with offset := pos.offset+4}
    let intervals := body.staticIntervals.map fun (parent,children) => (shift parent,children.map shift)
    (subject,RuntimeContextRequest.Context.withReferences (body.positions.map shift)
      body.sites body.calls body.branches body.bodies body.references intervals)
  let childPosition := {position with offset := 310}
  let child := RuntimeContextRequest.Context.withReferences [childPosition]
    (child.sites.map fun site => {site with position := childPosition}) child.calls child.branches
    phaseBodies child.references child.staticIntervals
  let position := {position with offset := routePrefix.utf8ByteSize}
  let runtime := {request.runtime with publicEffect := .observe}
  return (artifact,replaceParent {request with runtime := runtime} position child)

private def mutate (artifact : Artifact) (request : Request) (fault : Fault) : Except String (Artifact × Request) := do
  let [(position,child)] := request.context.calls | throw "expected one original caller"
  match fault with
  | .none => return (artifact,request)
  | .staleCaller =>
    return (artifact,replaceParent request {position with offset := 302} child)
  | .staleChild =>
    return (artifact,replaceParent request position (replaceChildPosition child {position with offset := 413}))
  | .missingChild =>
    let child : Context := .withReferences [] child.sites child.calls child.branches
      child.bodies child.references child.staticIntervals
    return (artifact,replaceParent request position child)
  | .wrongArguments =>
    let sources := artifact.sources.map fun (owner,text) => (owner,text.replace "](s,q)" "](q,s)")
    return ({artifact with sources := sources},request)
  | .wrongReturn =>
    let runtime := {request.runtime with storage := [.tuple 2,
      .quantum ⟨⟨5,[1],1⟩,[.bit]⟩,.quantum ⟨⟨4,[0],1⟩,[.bit]⟩]}
    return (artifact,{request with runtime := runtime})
  | .wrongSignature =>
    -- Coherent equal-width input metadata cannot change original Bit to Bits<1>.
    let runtime := {request.runtime with parameters := [Semantics.RuntimeType.owner [.bits 1],Semantics.RuntimeType.owner [.bit]], inputStorage := [[.quantum ⟨⟨0,[0],1⟩,[.bits 1]⟩],[.quantum ⟨⟨1,[1],1⟩,[.bit]⟩]]}
    return (artifact,{request with runtime := runtime})
  | .heldUnit | .droppedHeldUnit | .wrongHeldValue => withHeldUnit artifact request position child fault
  | .externalObserve => externalSource artifact request position child
  | .falseMeaning =>
    -- Change keep to sign everywhere that describes the reference. Its own
    -- body checks, so the remaining discrepancy is I versus Z.
    let [[],[],[[(.pure refProgram,_)]]] := child.references | throw "expected one arm reference"
    let (.function ev,phaseBody) :: _ := child.bodies | throw "expected the supplied sign"
    let some entry := artifact.entries[ev]? | throw "missing sign evidence"
    let some sign := artifact.programs[entry.implementation]? | throw "missing sign program"
    let sources := artifact.sources.map fun (owner,text) =>
      (owner,text.replace "Identity:Bit=reference(keep)" "Identity:Bit=reference(sign)")
    let artifact := {artifact with sources, programs := artifact.programs.set! refProgram sign}
    let child : Context := .withReferences child.positions child.sites child.calls child.branches
      child.bodies [[],[],[[(.pure refProgram,phaseBody)]]] child.staticIntervals
    return (artifact,replaceParent request position child)
  | .changedControlled =>
    let [site] := child.sites | throw "expected one selection"
    let [_,arm] := site.arms | throw "expected two original arms"
    let some program := artifact.programs[arm.controlled]? | throw "missing controlled program"
    let [join,.pure (.applyUnitary input output [first,second]),split] := program.operations
      | throw "expected both controlled sign steps"
    if first != second then throw "expected two identical steps"
    let program := {program with operations := [join,.pure (.applyUnitary input output [first]),split]}
    return ({artifact with programs := artifact.programs.set! arm.controlled program},request)
  | .wrongReferenceSlot =>
    let [supplied,keep,checked] := child.references | throw "expected three original operations"
    let child : Context := .withReferences child.positions child.sites child.calls child.branches
      child.bodies [checked,keep,supplied] child.staticIntervals
    return (artifact,replaceParent request position child)
  | .extraProviderReferences =>
    let (subject,body) :: rest := child.bodies | throw "missing first provider"
    let body : Context := .withReferences body.positions body.sites body.calls body.branches
      body.bodies [[]] body.staticIntervals
    return (artifact,replaceParent request position (child.withBodies ((subject,body) :: rest)))

private def inspect (artifactBytes requestBytes : ByteArray) (fault : Fault) : WorkM Summary := do
  let (decoded,order) ← Protocol.Qirf.readAll artifactBytes
  let request ← Protocol.QmatchV5.readRequest requestBytes
  let (artifact,request) ← lift ((mutate decoded request fault).mapError fun _ => .invalid)
  let joined ← Protocol.QmatchV5.readNamed artifact order request
  let named := joined.named
  let checkedAt := joined.result.checked
  return (checkedAt.boundary.boundary.after.issued.map (·.ordinal),
    checkedAt.boundary.boundary.after.bindings.map (·.owner.ordinal),
    checkedAt.boundary.returned.finalBindings.map (·.port.token),
    (named.supplies.collection.entries.map (·.implementations.length)).sum,
    (named.selection.arms.toList.map (·.implementations.length)).sum,
    checkedAt.child.reverseArms.length)

-- Exact original JSON bytes, including the source newlines and final newline.
-- artifact-first SHA256 2e09ad2be20f693149594419a7936f5acd98e67b74f400995071f8f750575b79
-- request-first SHA256 663b5469b725152775fd74f139ffb5255d5e18741d2cabedcb6f7503947f52e0
private def artifactBytes : ByteArray := ("{\"evidence\":[{\"identity\":{\"implementation\":\"main::sign\",\"sources\":[0],\"specification\":\"main::sign\"},\"implementation\":1,\"signature\":{\"tag\":\"bit\"},\"specification\":2,\"tag\":\"circuit\"}],\"format\":\"qleisli.finite-ir\",\"profile\":\"finite-meaning-v1\",\"programs\":[{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[{\"left\":0,\"output\":2,\"right\":1,\"tag\":\"join\"},{\"input\":2,\"output\":3,\"steps\":[{\"action\":{\"adjoint\":false,\"evidence\":0,\"indices\":[1],\"tag\":\"contract\"},\"controls\":[{\"index\":0,\"when_one\":true}]},{\"action\":{\"adjoint\":false,\"evidence\":0,\"indices\":[1],\"tag\":\"contract\"},\"controls\":[{\"index\":0,\"when_one\":true}]}],\"tag\":\"apply_unitary\"},{\"input\":3,\"left\":4,\"left_bits\":1,\"right\":5,\"tag\":\"split\"}],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]},{\"shape\":{\"bits\":1},\"token\":1,\"wires\":[1]}],\"quantum_outputs\":[4,5]},{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[{\"input\":0,\"output\":1,\"steps\":[{\"action\":{\"indices\":[0],\"permutation\":[0,1],\"phases\":[0,4],\"tag\":\"monomial\"},\"controls\":[]}],\"tag\":\"apply_unitary\"}],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]}],\"quantum_outputs\":[1]},{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[{\"input\":0,\"output\":1,\"steps\":[{\"action\":{\"indices\":[0],\"permutation\":[0,1],\"phases\":[0,4],\"tag\":\"monomial\"},\"controls\":[]}],\"tag\":\"apply_unitary\"}],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]}],\"quantum_outputs\":[1]},{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[{\"input\":0,\"output\":1,\"steps\":[],\"tag\":\"apply_unitary\"}],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]}],\"quantum_outputs\":[1]},{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[{\"left\":0,\"output\":2,\"right\":1,\"tag\":\"join\"},{\"input\":2,\"output\":3,\"steps\":[],\"tag\":\"apply_unitary\"},{\"input\":3,\"left\":4,\"left_bits\":1,\"right\":5,\"tag\":\"split\"}],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]},{\"shape\":{\"bits\":1},\"token\":1,\"wires\":[1]}],\"quantum_outputs\":[4,5]},{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]}],\"quantum_outputs\":[0]},{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[{\"input\":0,\"output\":1,\"steps\":[{\"action\":{\"adjoint\":false,\"evidence\":0,\"indices\":[0],\"tag\":\"contract\"},\"controls\":[]},{\"action\":{\"adjoint\":false,\"evidence\":0,\"indices\":[0],\"tag\":\"contract\"},\"controls\":[]}],\"tag\":\"apply_unitary\"}],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]}],\"quantum_outputs\":[1]},{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[{\"left\":0,\"output\":2,\"right\":1,\"tag\":\"join\"},{\"input\":2,\"output\":3,\"steps\":[{\"action\":{\"adjoint\":false,\"evidence\":0,\"indices\":[1],\"tag\":\"contract\"},\"controls\":[{\"index\":0,\"when_one\":true}]},{\"action\":{\"adjoint\":false,\"evidence\":0,\"indices\":[1],\"tag\":\"contract\"},\"controls\":[{\"index\":0,\"when_one\":true}]}],\"tag\":\"apply_unitary\"},{\"input\":3,\"left\":4,\"left_bits\":1,\"right\":5,\"tag\":\"split\"}],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]},{\"shape\":{\"bits\":1},\"token\":1,\"wires\":[1]}],\"quantum_outputs\":[4,5]},{\"classical_inputs\":[],\"classical_outputs\":[],\"declared_effect\":\"unitary\",\"operations\":[],\"quantum_inputs\":[{\"shape\":{\"bits\":1},\"token\":0,\"wires\":[0]}],\"quantum_outputs\":[0]}],\"root\":0,\"root_interface\":null,\"sources\":[{\"path\":\"main\",\"text\":\"#![no_implicit_prelude]\\u000aunitary fn keep(q:Q<Bit>)->Q<Bit>{q}\\u000aunitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\\u000ameaning Identity:Bit=reference(keep);\\u000ameaning Sign:Bit=reference(sign);\\u000aunitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)\\u000a    requires Applicable(U),Controllable(U) {\\u000a    qmatch(s,q){0=>keep,1=>checked_op(U,Identity)}\\u000a}\\u000apub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){\\u000a    choose[then_op(sign,sign)](s,q)\\u000a}\\u000a\"}],\"version\":2}\n").toUTF8
private def requestBytes : ByteArray := ("{\"bodies\":[],\"branches\":[],\"calls\":[{\"body\":{\"bodies\":[{\"body\":{\"bodies\":[],\"branches\":[],\"calls\":[],\"positions\":[{\"count\":1,\"offset\":95,\"start\":0}],\"references\":[],\"sites\":[]},\"subject\":{\"evidence\":0,\"kind\":\"function\"}},{\"body\":{\"bodies\":[],\"branches\":[],\"calls\":[],\"positions\":[{\"count\":1,\"offset\":95,\"start\":0}],\"references\":[],\"sites\":[]},\"subject\":{\"evidence\":0,\"kind\":\"function\"}},{\"body\":{\"bodies\":[],\"branches\":[],\"calls\":[],\"positions\":[],\"references\":[],\"sites\":[]},\"subject\":{\"kind\":\"pure\",\"program\":5}},{\"body\":{\"bodies\":[],\"branches\":[],\"calls\":[],\"positions\":[{\"count\":1,\"offset\":95,\"start\":0}],\"references\":[],\"sites\":[]},\"subject\":{\"evidence\":0,\"kind\":\"function\"}},{\"body\":{\"bodies\":[],\"branches\":[],\"calls\":[],\"positions\":[{\"count\":1,\"offset\":95,\"start\":0}],\"references\":[],\"sites\":[]},\"subject\":{\"evidence\":0,\"kind\":\"function\"}}],\"branches\":[],\"calls\":[],\"positions\":[{\"count\":3,\"offset\":302,\"start\":0}],\"references\":[[],[],[[{\"body\":{\"bodies\":[],\"branches\":[],\"calls\":[],\"positions\":[],\"references\":[],\"sites\":[]},\"subject\":{\"kind\":\"pure\",\"program\":8}}]]],\"sites\":[{\"arms\":[{\"controlled\":4,\"implementation\":3},{\"controlled\":7,\"implementation\":6}],\"attached\":{\"inputs\":[{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":0,\"wires\":[0]}},{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":1,\"wires\":[1]}}],\"outputs\":[{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":4,\"wires\":[0]}},{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":5,\"wires\":[1]}}],\"public_effect\":\"unitary\"},\"position\":{\"count\":3,\"offset\":302,\"start\":0},\"required\":{\"inputs\":[{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":0,\"wires\":[0]}},{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":1,\"wires\":[1]}}],\"outputs\":[{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":4,\"wires\":[0]}},{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":5,\"wires\":[1]}}],\"public_effect\":\"unitary\"}}]},\"position\":{\"count\":3,\"offset\":413,\"start\":0}}],\"format\":\"qleisli.qmatch-request\",\"positions\":[{\"count\":3,\"offset\":413,\"start\":0}],\"profile\":\"finite-source-qmatch-context-v5\",\"references\":[],\"runtime\":{\"declaration\":\"route\",\"format\":\"qleisli.runtime-root-request\",\"input_rows\":[[]],\"input_storage\":[[{\"owner\":{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":0,\"wires\":[0]}},\"tag\":\"quantum\"}],[{\"owner\":{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":1,\"wires\":[1]}},\"tag\":\"quantum\"}]],\"module\":\"main\",\"parameters\":[[{\"tag\":\"quantum\"},{\"atom\":{\"tag\":\"bit\"},\"tag\":\"finite\"}],[{\"tag\":\"quantum\"},{\"atom\":{\"tag\":\"bit\"},\"tag\":\"finite\"}]],\"profile\":\"finite-runtime-root-v2\",\"public_effect\":\"unitary\",\"result\":[{\"atom\":{\"tag\":\"pair\"},\"tag\":\"finite\"},{\"tag\":\"quantum\"},{\"atom\":{\"tag\":\"bit\"},\"tag\":\"finite\"},{\"tag\":\"quantum\"},{\"atom\":{\"tag\":\"bit\"},\"tag\":\"finite\"}],\"selection\":\"exported\",\"static_bases\":[],\"static_naturals\":[],\"storage\":[{\"arity\":2,\"tag\":\"tuple\"},{\"owner\":{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":4,\"wires\":[0]}},\"tag\":\"quantum\"},{\"owner\":{\"basis\":[{\"tag\":\"bit\"}],\"port\":{\"bits\":1,\"token\":5,\"wires\":[1]}},\"tag\":\"quantum\"}],\"version\":2},\"sites\":[],\"source\":{\"function\":\"route\",\"module\":\"main\",\"static_bases\":[],\"static_naturals\":[],\"static_operations\":[]},\"version\":5}\n").toUTF8

private def study (fault : Fault) := (inspect artifactBytes requestBytes fault).run 16000000

-- Actual original transport: caller 413/0/3, qmatch 302/0/3, two header
-- provider occurrences followed by three arm providers and two original arms.
#guard (study .none).1.toOption == some ([0,1],[0,1],[4,5],2,3,2)
#guard (study .heldUnit).1.toOption == some ([0,1,2],[0,1,2],[6,4,5],2,3,2)

-- Neither source coordinates nor equal-width argument/result wires are names
-- that can be reassigned. Cross-module public Observe is not sharpened to Unit.
#guard [Fault.staleCaller,.staleChild,.missingChild,.wrongArguments,.wrongReturn,
    .wrongHeldValue,.externalObserve,.wrongReferenceSlot,.extraProviderReferences].all fun fault =>
  match (study fault).1 with | .error .request => true | _ => false

-- The advertised Bits<1> input and its storage agree with each other, but
-- cannot replace the genuinely read original Q<Bit> parameter.
#guard (study .wrongSignature).1 matches .error .request

-- Dropping the logical zero-width spectator is already a real Raw violation.
#guard (study .droppedHeldUnit).1 matches .error .invalid

-- Both altered graphs remain reachable and structurally valid. The written
-- Meaning and the literal controlled interval each enforce their own equation.
#guard [Fault.falseMeaning,.changedControlled].all fun fault =>
  match (study fault).1 with | .error .equation => true | _ => false

-- The saved former-10M refusals remain authoring history. Shared original
-- Meaning scans now let both examples fit that allowance; exhaustion itself
-- must still refuse without a counter reset or an alternate checker.
#guard [Fault.none,.heldUnit].all fun fault =>
  match (inspect artifactBytes requestBytes fault).run 1 with
  | (.error (.arithmetic .workLimit),_) => true
  | _ => false

private def viewSize (fault : Fault) : WorkM Nat := do
  let (decoded,order) ← Protocol.Qirf.readAll artifactBytes
  let original ← Protocol.QmatchV5.readRequest requestBytes
  let (artifact,request) ← lift ((mutate decoded original fault).mapError fun _ => .invalid)
  let joined ← Protocol.QmatchV5.readNamed artifact order request
  let view ← Protocol.ExecutionView.QmatchV5.description artifact joined.result.root request
  let bytes ← lift ((Protocol.ExecutionView.encode view).mapError fun _ => .request)
  return bytes.size

-- The original result, both false equations and the larger held-owner
-- program run from the same public allowance, without a counter refill.
#guard ((viewSize .none).run WorkProfile.qmatch.limit).1.toOption == some 8288
#guard [Fault.falseMeaning,.changedControlled].all fun fault =>
  match ((viewSize fault).run WorkProfile.qmatch.limit).1 with | .error .equation => true | _ => false
#guard ((viewSize .heldUnit).run WorkProfile.qmatch.limit).1.isOk

end QleisliKernel.Tests.RuntimeNamedSelectionBoundary

namespace QleisliKernel.Tests.RuntimeNamedSelectionBoundary
open QleisliKernel Finite SourceTypes Qirf

private inductive SurroundingFault where
  | none | wrongOrder | omittedUnit | wrongCallStart | wrongReturn | incompatible | nestedReferences
  deriving BEq

private def surroundingRoute := "pub unitary fn route(u:Q<Unit>,s:Q<Bit>,q:Q<Bit>)->(Q<Unit>,(Q<Bit>,Q<Bit>)){\n    let q=phase[1,1](q);\n    let (s,q)=choose[then_op(sign,sign)](s,q);\n    let q=h(q);\n    (u,(s,q))\n}\n"

/-- A plain proposal from the one retained packet. Every result is freshly
source/IR checked below; this transformation contributes no authority. -/
private def surroundingProposal (artifact : Artifact) (request : Request) (fault : SurroundingFault) :
    Except String (Artifact × Request) := do
  let some row := artifact.sources[0]? | throw "missing original main"
  let before :: _ := row.2.splitOn "pub unitary fn route" | throw "missing original route"
  let text := before ++ surroundingRoute
  let some caller := artifact.programs[0]? | throw "missing caller"
  let [.pure (.join _ _ _),.pure (.applyUnitary _ _ steps),.pure (.split _ _ _ leftBits)] := caller.operations
    | throw "unexpected original joined caller"
  let some sign := artifact.programs[1]? | throw "missing original sign"
  let [.pure (.applyUnitary _ _ phaseSteps)] := sign.operations | throw "unexpected original sign"
  let unitPort : Semantics.Raw.Port := ⟨8,[],0⟩
  let first : Semantics.Observation.Op := if fault == .wrongOrder then .pure (.gate .h 1 2)
    else .pure (.applyUnitary 1 2 phaseSteps)
  let last : Semantics.Observation.Op := if fault == .wrongOrder then .pure (.applyUnitary 6 7 phaseSteps)
    else .pure (.gate .h 6 7)
  let caller := {caller with inputs := unitPort :: caller.inputs, operations := [first,.pure (.join 0 2 3),.pure (.applyUnitary 3 4 steps),.pure (.split 4 5 6 leftBits),last], outputs := if fault == .omittedUnit then [5,7] else [8,5,7]}
  let artifact := {artifact with sources := #[(row.1,text)], programs := artifact.programs.set! 0 caller}
  let [(_,child)] := request.context.calls | throw "missing original call"
  let [site] := child.sites | throw "missing original selection"
  let interface : Semantics.CarrierInterface.Interface := ⟨[⟨⟨0,[0],1⟩,[.bit]⟩,⟨⟨2,[1],1⟩,[.bit]⟩],[⟨⟨5,[0],1⟩,[.bit]⟩,⟨⟨6,[1],1⟩,[.bit]⟩],.unitary⟩
  let site := {site with attached := interface, required := interface}
  let bodies ← if fault == .nestedReferences then do
    let (subject,body) :: rest := child.bodies | throw "missing original provider body"
    let body : Context := .withReferences body.positions body.sites body.calls body.branches
      body.bodies [[]] body.staticIntervals
    pure ((subject,body) :: rest)
  else pure child.bodies
  let child : Context := .withReferences child.positions [site] child.calls child.branches
    bodies child.references child.staticIntervals
  let callPosition : Position := ⟨468,if fault == .wrongCallStart then 0 else 1,3⟩
  let context : Context := .withReferences [⟨439,0,1⟩,callPosition,⟨511,4,1⟩] []
    [(callPosition,child)] [] [] request.context.references request.context.staticIntervals
  let unitTree := Semantics.RuntimeType.owner [.unit]
  let returned : Semantics.Raw.Port := ⟨if fault == .wrongReturn then 6 else 7,[1],1⟩
  let runtime := {request.runtime with parameters := unitTree :: request.runtime.parameters, inputStorage := [.quantum ⟨unitPort,[.unit]⟩] :: request.runtime.inputStorage, result := Semantics.RuntimeType.tuple 2 [unitTree,request.runtime.result], storage := [.tuple 2,.quantum ⟨unitPort,[.unit]⟩,.tuple 2,.quantum ⟨⟨5,[0],1⟩,[.bit]⟩,.quantum ⟨returned,[.bit]⟩]}
  let runtime := if fault == .incompatible then {runtime with declarationName := "choose"} else runtime
  return (artifact,{request with context := context, runtime := runtime})

private def surroundingInspect (fault : SurroundingFault) : WorkM (List Nat × List Nat × Nat) := do
  let (artifact,order) ← Protocol.Qirf.readAll artifactBytes
  let original ← Protocol.QmatchV5.readRequest requestBytes
  let (artifact,request) ← lift ((surroundingProposal artifact original fault).mapError fun _ => .invalid)
  let checked ← Protocol.QmatchV5.readNamedOccurrence artifact order request
  return (checked.result.checked.after.history.issued.map (·.ordinal),
    checked.result.checked.finalBindings.map (·.port.token),checked.result.checked.nodes.length)

private def surroundingStudy (fault : SurroundingFault) := (surroundingInspect fault).run 20000000 |>.1

-- Full original source and child intervals, plus all header/arm/Meaning reads.
#guard (surroundingStudy .none).toOption == some ([0,1,2],[8,5,7],3)
-- Both orders are structurally valid Raw. Exact original local equations
-- distinguish H Z from Z H, retaining phase rather than just channel equality.
#guard surroundingStudy .wrongOrder matches .error .equation
#guard surroundingStudy .omittedUnit matches .error .invalid
#guard [SurroundingFault.wrongCallStart,.wrongReturn,.incompatible,.nestedReferences].all fun fault =>
  match surroundingStudy fault with | .error .request => true | _ => false
-- The entire original source, typed child and caller share one public allowance.
#guard ((surroundingInspect .none).run WorkProfile.qmatch.limit).1.toOption == some ([0,1,2],[8,5,7],3)

-- The separate original singleton binding must keep refusing this source;
-- the new reader is never tried as an automatic fallback.
private def originalSingletonSurrounding : WorkM Unit := do
  let (artifact,order) ← Protocol.Qirf.readAll artifactBytes
  let original ← Protocol.QmatchV5.readRequest requestBytes
  let (artifact,request) ← lift ((surroundingProposal artifact original .none).mapError fun _ => .invalid)
  let _ ← Protocol.QmatchV5.readNamed artifact order request
  return ()

#guard (originalSingletonSurrounding.run 20000000).1 matches .error .request

end QleisliKernel.Tests.RuntimeNamedSelectionBoundary

namespace QleisliKernel.Tests.RuntimeNamedSelectionBoundary
open QleisliKernel Finite SourceTypes Qirf

private inductive OrderedCallFault where
  | none | wrongOrder | omittedUnit | missingCall | extraCall | reorderedCalls
  | wrongOffset | childOffset | wrongCursor | wrongReturn | sourceReturnOrder
  | ordinaryReferences | providerReferences | referenceReferences
  | ordinaryDescendant | descendantReferences
  | reversedNodes | missingLastNode
  deriving BEq

private def ordinaryCallDeclarations := "unitary fn pre(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\npub unitary fn post(q:Q<Bit>)->Q<Bit>{h(q)}\n"

/-- Derive the frozen three-call authoring program and literal IR from the
existing packet, preserving every choose header/arm/Meaning occurrence. This
proposal is plain untrusted data; no original Body or native result is reused.
Original main.qli SHA256 34b561f7aaea90710dd520bc59dc6895cd57a55b432a6dca2d7e5846a18540b7. -/
private def orderedCallProposal (artifact : Artifact) (request : Request) (fault : OrderedCallFault) :
    Except String (Artifact × Request) := do
  let rawFault := if fault == .wrongOrder then SurroundingFault.wrongOrder
    else if fault == .omittedUnit then .omittedUnit
    else if fault == .wrongReturn then .wrongReturn else .none
  let (artifact,request) ← surroundingProposal artifact request rawFault
  let some row := artifact.sources[0]? | throw "missing main source"
  let before :: _ := row.2.splitOn "pub unitary fn route" | throw "missing original route"
  let route := (surroundingRoute.replace "let q=phase[1,1](q);" "let q=pre(q);").replace
    "let q=h(q);" "let q=post(q);"
  let route := if fault == .sourceReturnOrder then route.replace "(u,(s,q))" "(u,(q,s))" else route
  let nested := fault == .ordinaryDescendant || fault == .descendantReferences
  let declarations := if nested then ordinaryCallDeclarations.replace "{phase[1,1](q)}" "{sign(q)}"
    else ordinaryCallDeclarations
  let text := before ++ declarations ++ route
  let [(_,selection)] := request.context.calls | throw "missing original selection call"
  let extra := fun (context : Context) => RuntimeContextRequest.Context.withReferences context.positions context.sites
    context.calls context.branches context.bodies [[]] context.staticIntervals
  let selection ← if fault == .providerReferences then do
      let (subject,body) :: rest := selection.bodies | throw "missing original provider"
      pure (selection.withBodies ((subject,extra body) :: rest))
    else if fault == .referenceReferences then do
      let [supplied,first,[[(subject,body)]]] := selection.references | throw "missing original reference"
      pure (RuntimeContextRequest.Context.withReferences selection.positions selection.sites selection.calls selection.branches
        selection.bodies [supplied,first,[[(subject,extra body)]]] selection.staticIntervals)
    else pure selection
  let shift := if nested then 6 else 0
  let prePosition : Position := ⟨531-shift,0,1⟩
  let selectionPosition : Position := ⟨if fault == .wrongOffset then 302 else 553-shift,
    if fault == .wrongCursor then 0 else 1,3⟩
  let postPosition : Position := ⟨596-shift,4,1⟩
  let pre : Context := .mk [⟨if fault == .childOffset then 531 else 384,0,1⟩] [] [] [] []
  let pre := if nested then
      let inner : Context := .withReferences [⟨95,0,1⟩] [] [] [] []
        (if fault == .descendantReferences then [[]] else []) []
      RuntimeContextRequest.Context.withReferences pre.positions pre.sites
        [(⟨384,0,1⟩,inner)] pre.branches pre.bodies pre.references pre.staticIntervals
    else if fault == .ordinaryReferences then extra pre else pre
  let post : Context := .mk [⟨437-shift,0,1⟩] [] [] [] []
  let calls := if fault == .missingCall then [(selectionPosition,selection),(postPosition,post)]
    else if fault == .extraCall then [(prePosition,pre),(selectionPosition,selection),(postPosition,post),(postPosition,post)]
    else if fault == .reorderedCalls then [(selectionPosition,selection),(prePosition,pre),(postPosition,post)]
    else [(prePosition,pre),(selectionPosition,selection),(postPosition,post)]
  let context : Context := .mk [prePosition,selectionPosition,postPosition] [] calls [] []
  return ({artifact with sources := #[(row.1,text)]},{request with context := context})

private def orderedCallInspect (fault : OrderedCallFault) :
    WorkM (List Nat × List Nat × List Nat × List Nat × Nat) := do
  let (decoded,order) ← Protocol.Qirf.readAll artifactBytes
  let original ← Protocol.QmatchV5.readRequest requestBytes
  let (artifact,request) ← lift ((orderedCallProposal decoded original fault).mapError fun _ => .invalid)
  guard request.compatible .request
  let source ← RuntimeBodyDiscovery.prepareSource artifact request.source.moduleName
    request.source.functionName request.source.arguments
  let prepared ← RuntimeNamedCallsSource.prepare source request.context
  let result ← RuntimeNamedCalls.read prepared order request.combinedRuntime
  let checked := result.checked
  if fault == .reversedNodes then
    let _ ← RuntimePureComposition.readOriginal result.root checked.result.nodes.reverse
    pure ()
  else if fault == .missingLastNode then
    let _ ← RuntimePureComposition.readOriginal result.root (checked.result.nodes.take 2)
    pure ()
  else
    let _ ← RuntimeNamedCallsComposition.read checked
    pure ()
  return (checked.result.history.issued.map (·.ordinal),checked.result.retired.map (·.ordinal),
    checked.finalBindings.map (·.port.token),
    checked.result.reverseReceipts.reverse.map (fun receipt => receipt.entry.pair.2.offset),checked.result.cursor)

private def orderedCallRaw (fault : OrderedCallFault) : WorkM (List Nat) := do
  let (decoded,order) ← Protocol.Qirf.readAll artifactBytes
  let original ← Protocol.QmatchV5.readRequest requestBytes
  let (artifact,_) ← lift ((orderedCallProposal decoded original fault).mapError fun _ => .invalid)
  let root ← Validity.checkRootFromRoots artifact order artifact.sources.toList
    (List.range artifact.programs.size) .qmatch
  return root.program.outputs

private def orderedCallStudy (fault : OrderedCallFault) :=
  (orderedCallInspect fault).run WorkProfile.qmatch.limit |>.1

-- The first source preparation alone genuinely spent 21,502,918 units;
-- its immutable external study remains a failed authoring benchmark. These
-- strict maintained controls require the actual public allowance throughout,
-- with no per-stage reset or developmental acceptance guard.
#guard (orderedCallStudy .none).toOption == some ([0,1,2],[],[8,5,7],[531,553,596],5)
#guard orderedCallStudy .wrongOrder matches .error .equation
#guard orderedCallStudy .omittedUnit matches .error .invalid
#guard [OrderedCallFault.missingCall,.extraCall,.reorderedCalls,.wrongOffset,.childOffset,
    .wrongCursor,.wrongReturn,.sourceReturnOrder,.ordinaryReferences,.providerReferences,
    .referenceReferences,.descendantReferences,.reversedNodes,.missingLastNode].all fun fault =>
  match orderedCallStudy fault with | .error .request => true | _ => false

-- The ordinary descendant is a real original pre -> sign call, not a dummy
-- context added under a primitive. Its own missing groups remain admissible;
-- adding an otherwise ignored empty group at sign must refuse above.
#guard (orderedCallStudy .ordinaryDescendant).toOption == some ([0,1,2],[],[8,5,7],[525,547,590],5)

-- Both literal orders satisfy Raw independently. The original child body
-- equations, not Raw validity alone, distinguish Z then H from H then Z.
#guard ((orderedCallRaw .none).run WorkProfile.qmatch.limit).1.toOption == some [8,5,7]
#guard ((orderedCallRaw .wrongOrder).run WorkProfile.qmatch.limit).1.toOption == some [8,5,7]
#guard ((orderedCallRaw .omittedUnit).run WorkProfile.qmatch.limit).1 matches .error .invalid

end QleisliKernel.Tests.RuntimeNamedSelectionBoundary


namespace QleisliKernel.Tests.RuntimeNamedSelectionBoundary
open Lean QleisliKernel Finite SourceTypes Qirf

-- These maintained cases follow the separately preserved first observations.
-- All source/body preparation and checking below share the public counter.
private structure ObservingPayload where
  artifact : Artifact
  rootArtifact : Artifact
  order : Array Nat
  rootOrder : Array Nat
  context : Context
  runtime : RuntimeFamily.Request

private def observingHistoryCounts {sources : Sources} {owner name : String}
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
private def observingPlainSource : String := "#![no_implicit_prelude]\nunitary fn keep(q:Q<Bit>)->Q<Bit>{q}\nunitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\nunitary fn choose(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){\n    qmatch(s,q){0=>keep,1=>sign}\n}\nobserve fn read(q:Q<Bit>)->Bit{measure_z(q)}\nobserve fn before(c:Bit,r:Q<Bit>)->Bit{\n    let a=read(r);\n    c xor a\n}\nobserve fn after(c:Bit,q:Q<Bit>)->Bit{\n    let b=read(q);\n    c xor b\n}\npub observe fn route(c:Bit,u:Q<Unit>,r:Q<Bit>,s:Q<Bit>,q:Q<Bit>)->(Q<Unit>,Q<Bit>,Bit){\n    let c=before(c,r);\n    let (s,q)=choose(s,q);\n    let b=after(c,q);\n    (u,s,b)\n}\n"
private def observingComposedSource : String := "#![no_implicit_prelude]\nunitary fn keep(q:Q<Bit>)->Q<Bit>{q}\nunitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\nmeaning Identity:Bit=reference(keep);\nmeaning Sign:Bit=reference(sign);\nunitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)\n    requires Applicable(U),Controllable(U) {\n    qmatch(s,q){0=>keep,1=>checked_op(U,Identity)}\n}\nobserve fn read(q:Q<Bit>)->Bit{measure_z(q)}\nobserve fn before(c:Bit,r:Q<Bit>)->Bit{\n    let a=read(r);\n    c xor a\n}\nobserve fn after(c:Bit,q:Q<Bit>)->Bit{\n    let b=read(q);\n    c xor b\n}\npub observe fn route(c:Bit,u:Q<Unit>,r:Q<Bit>,s:Q<Bit>,q:Q<Bit>)->(Q<Unit>,Q<Bit>,Bit){\n    let c=before(c,r);\n    let (s,q)=choose[then_op(sign,sign)](s,q);\n    let b=after(c,q);\n    (u,s,b)\n}\n"

private def observingOrder (artifact : Artifact) (roots : List Nat) : WorkM (Array Nat) := do
  let nodes := Qirf.nodes artifact
  let visit : Nat → Nat → (Array Nat × Array Nat) → Except Finite.Error (Array Nat × Array Nat) :=
    Nat.rec (fun _ _ => throw .limit) (fun _ recurse index (colors,order) => do
      let some color := colors[index]? | throw .invalid
      if color == 2 then return (colors,order)
      if color == 1 then throw .invalid
      let (colors,order) ← (Hierarchical.Graph.dependencies nodes index).foldlM
        (fun state child => recurse child state) (colors.set! index 1,order)
      return (colors.set! index 2,order.push index))
  let (_,order) ← lift (roots.foldlM (fun state root => visit 33 root state)
    (Array.replicate nodes.size 0,#[]))
  pure order

/-- Fresh untrusted proposals from the frozen observing-before/after sources.
The seed bytes are shared above; every native/source result is checked anew. -/
private def observingPayload (composed : Bool) (wrongOwner wrongXor : Bool := false) : WorkM ObservingPayload := do
  let (seed,_originalOrder) ← Protocol.Qirf.readAll artifactBytes
  let seedRequest ← Protocol.QmatchV5.readRequest requestBytes
  let [(_,selection)] := seedRequest.context.calls | throw .request
  let [site] := selection.sites | throw .request
  let text := if composed then observingComposedSource else observingPlainSource
  let tokens ← lift ((lexLocated text).mapError fun _ => .request)
  let [_,chooseCall] := tokens.filter (·.text == "choose") | throw .request
  let [_,beforeCall] := tokens.filter (·.text == "before") | throw .request
  let [_,afterCall] := tokens.filter (·.text == "after") | throw .request
  let [_,firstRead,lastRead] := tokens.filter (·.text == "read") | throw .request
  let [measure] := tokens.filter (·.text == "measure_z") | throw .request
  let [phase] := tokens.filter (·.text == "phase") | throw .request
  let [qmatch] := tokens.filter (·.text == "qmatch") | throw .request
  let some original := seed.programs[0]? | throw .request
  let [join,.pure (.applyUnitary input output [first,second]),split] := original.operations | throw .request
  let [selector,target] := original.inputs | throw .request
  let selectionOps := [join,.pure (.applyUnitary input output (if composed then [first,second] else [first])),split]
  let unit : Semantics.Raw.Port := ⟨6,[],0⟩
  let r : Semantics.Raw.Port := ⟨7,[2],1⟩
  let firstMeasured := if wrongOwner then 1 else 7
  let lastMeasured := if wrongOwner then 7 else 5
  let operations : List Semantics.Observation.Op :=
    [.measure firstMeasured 1,if wrongXor then .and 0 1 2 else .xor 0 1 2] ++ selectionOps ++
    [.measure lastMeasured 3,.xor 2 3 4]
  let program : Semantics.Observation.Program :=
    ⟨unit :: r :: original.inputs,[0],operations,[6,4],[4],.observe⟩
  -- The plain controlled sign is the same literal one-step controlled body;
  -- the composed reference/action uses both actual sign occurrences.
  let some controlled := seed.programs[7]? | throw .request
  let controlled := {controlled with operations := selectionOps}
  let programs := if composed then seed.programs.set! 0 program
    else ((seed.programs.toList.take 6).toArray.set! 0 program).push controlled
  let artifact := {seed with programs,sources := #[("main",text)]}
  -- Ordinary RuntimeFamily has only the main root, so its independent Raw
  -- control must carry no unrelated arm/reference subjects. It retains exactly
  -- the same root body, evidence and complete original source/request bytes.
  -- This control is never passed to the common source-body continuation.
  let rootArtifact := {artifact with programs := (seed.programs.toList.take 3).toArray.set! 0 program}
  let localSite : RuntimeContextRequest.Site := {site with
    position := ⟨qmatch.span.startByte,0,3⟩,
    arms := if composed then site.arms else [⟨3,4⟩,⟨1,6⟩]}
  let phaseBody : Context := .mk [⟨phase.span.startByte,0,1⟩] [] [] [] []
  let empty : Context := .mk [] [] [] [] []
  let child : Context := if composed then
      .withReferences [localSite.position] [localSite] [] []
        selection.bodies selection.references selection.staticIntervals
    else .withReferences [localSite.position] [localSite] [] []
      [(.pure 5,empty),(.function 0,phaseBody)] [[],[]] []
  let leaf : Context := .mk [⟨measure.span.startByte,0,1⟩] [] [] [] []
  let before : Context := .mk [⟨firstRead.span.startByte,0,1⟩] [] [(⟨firstRead.span.startByte,0,1⟩,leaf)] [] []
  let after : Context := .mk [⟨lastRead.span.startByte,0,1⟩] [] [(⟨lastRead.span.startByte,0,1⟩,leaf)] [] []
  let p : SourceSequence.Position := ⟨beforeCall.span.startByte,0,2⟩
  let q : SourceSequence.Position := ⟨chooseCall.span.startByte,2,3⟩
  let s : SourceSequence.Position := ⟨afterCall.span.startByte,5,2⟩
  let context : Context := .mk [p,q,s] [] [(p,before),(q,child),(s,after)] [] []
  let runtime : RuntimeFamily.Request := ⟨.exported,"main","route",
    [Semantics.RuntimeType.ordinary [.bit],Semantics.RuntimeType.owner [.unit],Semantics.RuntimeType.owner [.bit],
      Semantics.RuntimeType.owner [.bit],Semantics.RuntimeType.owner [.bit]],
    [[.ordinary [.bit] (.bit 0)],[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨r,[.bit]⟩],
      [.quantum ⟨selector,[.bit]⟩],[.quantum ⟨target,[.bit]⟩]],
    [[false],[true]],
    Semantics.RuntimeType.tuple 3 [Semantics.RuntimeType.owner [.unit],Semantics.RuntimeType.owner [.bit],
      Semantics.RuntimeType.ordinary [.bit]],
    [.tuple 3,.quantum ⟨unit,[.unit]⟩,.quantum ⟨⟨4,[0],1⟩,[.bit]⟩,.ordinary [.bit] (.bit 4)],.observe,{}⟩
  let roots := if composed then [artifact.root,5,3,4,6,7,8,9] else [artifact.root,5,3,4,1,7,6]
  let order ← observingOrder artifact roots
  let rootOrder ← observingOrder rootArtifact [rootArtifact.root]
  return ⟨artifact,rootArtifact,order,rootOrder,context,runtime⟩


private def observingTypedRoot (p : ObservingPayload) : WorkM Nat := do
  let checked ← RuntimeFamily.check p.rootArtifact p.rootOrder p.runtime
  return (OrdinaryDomain.assignments checked.domain).length

private def markerRows {artifact catalogue owner description graph implementations references originals prepared root requested checked}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references
      originals prepared root requested checked) : List (Nat × Nat × String) :=
  source.entries.map fun entry =>
    ((source.markers[entry.index].tokens.head?.map (·.span.startByte)).getD 0,
      entry.assertion.binding.index.val,entry.assertion.requirement.request.declarationName)

/-- Inspect the original arm association on the same common-loop receipt. -/
private def originalMarkerSummary {artifact catalogue context description graph implementations references}
    (origin : @RuntimeGraphOperation.Origin artifact.sources context description graph) :
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references) →
    {root requested : _} → (checked : RuntimeOperationTree.Checked prepared root requested) →
    RuntimeSourceOperationMarkers.OriginChecked origin prepared checked → Nat × List (Nat × Nat × String) := by
  cases origin with
  | unlocated | application | supplying => exact fun _ {_ _} _ _ => (0,[])
  | arm => exact fun _ {_ _} _ association => (1,markerRows association)

private def rootedInRoute {sources rootOwner rootName owner name} :
    RuntimeOrdinaryBody.CallPath sources rootOwner rootName owner name → Bool
  | .root body => rootOwner == "main" && body.checked.signature.original.declaration.name == "route"
  | .named .. => false

private def directChooseOffset {sources rootOwner rootName owner name} :
    RuntimeOrdinaryBody.CallPath sources rootOwner rootName owner name → Option Nat
  | .root _ => none
  | .named event body _ parent =>
    if rootedInRoute parent && event.target.callerName == "route" &&
        event.target.resolution.moduleName == "main" && body.checked.signature.original.declaration.name == "choose" then
      some event.call.calleeOffset
    else none

private def originalArmSite {sources owner name context description graph origin} :
    @RuntimeGraphOperation.Site sources owner name context description graph origin → Option (Nat × Nat × Nat)
  | .unlocated | .application .. | .supplying .. => none
  | .arm table index => some (index.val,(table.arms[index]).label.ordinal,table.site.parsed.keyword.span.startByte)

private abbrev SupplyHopSummary := String × String × Nat × String × Nat × Nat × Option Nat

private def supplyHopSummary (hop : RuntimeForwardedSupply.Hop) : SupplyHopSummary :=
  (hop.key.moduleName,hop.key.declarationName,hop.key.ordinal,hop.formalName,hop.position,hop.mixed,
    hop.tokens.head?.map (·.span.startByte))

private abbrev InteriorRow := List Nat × Nat × Nat × String × Nat × Option Nat × Option Nat

private structure TailNodeView where
  positions : List Nat
  key : Semantics.SymbolicBasis.Parameter
  formalName : String
  inputIndex : Nat
  nodeOffset : Nat
  rowOffset : Nat
  outputIndex : Nat
  nativeIndex : Nat
  childNativeIndex : Nat
  argumentOffset : Option Nat
  terminal : Bool
  children : Nat
  localNodes : Nat
  localSuppliers : Nat
  deriving BEq, Repr

private def tailBasic (row : TailNodeView) :=
  (row.positions,row.key.declarationName,row.formalName,row.inputIndex,row.nodeOffset,row.outputIndex,
    row.nativeIndex,row.childNativeIndex,row.argumentOffset,row.terminal,row.children,row.localNodes)

private def tailNodeView {artifact catalogue context description graph implementations references prepared root requested}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {native : OperationDescription.Description} {queue : GenericDutyQueue.Checked catalogue} {rootOwner rootName : String}
    {task : RuntimeTransitiveInterior.Task checked native queue rootOwner rootName}
    (step : RuntimeTransitiveInterior.Step task) : TailNodeView :=
  let focus := step.focus.focus
  ⟨task.site.positions,task.site.key,task.site.leaf.choice.header.name,
    focus.inputIndex,focus.nodeOffset,focus.rowOffset,focus.outputIndex,
    task.site.leaf.finish.occurrence.cursor.binding.index.val,task.site.leaf.child.cursor.binding.index.val,
    task.site.leaf.supply.source.actual.argument.tokens.head?.map (·.span.startByte),
    (match step.next with | .terminal .. => true | .named .. => false),step.children.length,
    focus.row.result.subject.description.nodes.length,focus.row.result.subject.suppliers.length⟩

-- Observe every stored child, without rerunning a source/native reader. An
-- exhausted observation returns none rather than a truncated successful list.
private def tailTreeObservation {artifact catalogue context description graph implementations references prepared root requested}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {native : OperationDescription.Description} {queue : GenericDutyQueue.Checked catalogue} {rootOwner rootName : String} :
    Nat → {task : RuntimeTransitiveInterior.Task checked native queue rootOwner rootName} →
    RuntimeTransitiveInterior.Tree task → Option (List TailNodeView) :=
  Nat.rec (fun {_} _ => none) (fun _ next {_} tree => do
    match tree with
    | .node step _ children =>
      let nested ← (List.finRange step.children.length).mapM
        fun (index : Fin step.children.length) => next (children index)
      pure (tailNodeView step :: nested.flatten))

private def completeTailTree {artifact catalogue context description graph implementations references prepared root requested}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {native : OperationDescription.Description} {queue : GenericDutyQueue.Checked catalogue} {rootOwner rootName : String}
    {task : RuntimeTransitiveInterior.Task checked native queue rootOwner rootName}
    (tree : RuntimeTransitiveInterior.Tree task) : Option (List TailNodeView) :=
  tailTreeObservation (task.invocation.depth+1) tree

private structure InteriorView where
  rows : List InteriorRow
  observed : List GenericFormalPaths.Occurrence
  expected : List GenericFormalPaths.Occurrence
  trees : Option (List (List TailNodeView))
  deriving BEq

private def callerInterior {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired queue rootOwner rootName owner name path record invocation result}
    (hop : @RuntimeForwardedSupply.Selected artifact catalogue context description graph implementations references prepared root requested checked
      native index cursor terminal caller original event app transfer paired)
    (prior : @RuntimeDutyInvocation.Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : GenericDutyQueue.Transport invocation.applications.reverse transfer.result.subject result) :
    RuntimeForwardedSupply.AtCaller hop prior remaining → InteriorView := by
  cases prior with
  | root => exact fun impossible => nomatch impossible
  | named => exact fun result =>
    let value := result.1.val
    ⟨value.entries.map (fun entry =>
      (entry.leaf.route.positions,entry.leaf.finish.index,entry.leaf.finish.occurrence.cursor.binding.index.val,
       entry.leaf.choice.header.name,entry.leaf.choice.position,
       entry.use.tokens.head?.map (·.span.startByte),entry.leaf.supply.source.actual.argument.tokens.head?.map (·.span.startByte))),
      value.entries.map RuntimeInteriorSupply.Entry.signature,value.expected,
      (List.finRange value.entries.length).mapM
        fun (index : Fin value.entries.length) => completeTailTree (result.2.val index)⟩

private def firstInterior {artifact catalogue context description graph implementations references prepared root requested checked
    queue rootOwner rootName owner name path record invocation original result native index cursor terminal}
    {binding : @RuntimeDutyInvocation.Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation}
    {transport : GenericDutyQueue.Transport invocation.applications.reverse original result}
    {paired : @RuntimeClosedSubject.Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal}
    (chain : RuntimeForwardedSupply.Chain binding transport paired) : Option InteriorView :=
  match chain with
  | .direct .. => none
  | .formal hop inside _ =>
    match inside.val with
    | .noInterior _ => none
    | .located _ value _ => some (callerInterior hop _ _ value)

-- Compare the original provider expectation to a native instance returned by
-- another actual walk. Equal phase/actions do not identify unused scalar actuals.
private structure AppliedOffer (sources : Sources) where
  native : StaticOperation.Provider sources
  action : Semantics.Exact.Matrix
  checkIdentity : StaticOperation.Provider sources → WorkM Unit

private abbrev LinkedArmSummary (sources : Sources) :=
  (List SupplyHopSummary × Option InteriorView × OperationDescription.Node) × Option (AppliedOffer sources)

private def linkedForStatus {artifact catalogue owner description graph implementations references originals prepared root requested checked
    queue rootOwner rootName name entry path}
    (source : @RuntimeSourceOperationMarkers.Checked artifact catalogue owner description graph implementations references
      originals prepared root requested checked)
    (index : Nat)
    (invoked : @RuntimeDutyInvocation.DemandBinding artifact.sources catalogue queue rootOwner rootName owner name entry path) :
    (status : SourcePendingMeaning.DemandStatus invoked.demand) →
    RuntimeLinkedSubject.ForStatus source index invoked status → Option (LinkedArmSummary artifact.sources)
  | .classified (.closed _),linked =>
    some ((linked.suppliers.hops.map supplyHopSummary,firstInterior linked.suppliers,linked.structureMatch.matched.terminal.node),
      linked.applied.map fun applied =>
        ⟨applied.slot.provider.header.original.supplied.provider,applied.slot.actual.action,fun native => do
          let _ ← SourceDutyProviderFresh.readIdentity applied.provider native
          pure ()⟩)
  | .classified (.conditional ..),_ | .inactive _,_ => none

private def linkedArmSummary {artifact catalogue queue context description graph origin implementations references root requested owner name rootOwner rootName}
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat)
    {entry : @SourcePendingMeaning.Entry artifact.sources catalogue queue}
    {path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name}
    (invoked : RuntimeDutyInvocation.DemandBinding entry path) :
    RuntimeLinkedSubject.Evidence site prepared checked source index invoked → Option (LinkedArmSummary artifact.sources) := by
  cases site with
  | unlocated => exact fun impossible => nomatch impossible
  | arm | application => exact linkedForStatus source index invoked (RuntimeLinkedSubject.assessment invoked)
  | supplying => exact fun evidence => linkedForStatus source index invoked (RuntimeLinkedSubject.assessment invoked) evidence.1

private def summarizeLink {artifact owner name arguments request prepared root runtime}
    (body : @RuntimeBodyOperations.AtRoot artifact owner name arguments request prepared root runtime)
    (link : RuntimeBodyOperations.WrittenLink body) : Option (LinkedArmSummary artifact.sources) :=
  let receipt := body.receipts[link.receiptIndex]
  @linkedArmSummary artifact prepared.source.catalogue prepared.source.pending.queue
    receipt.request.context receipt.request.description receipt.request.graph receipt.request.origin
    receipt.request.implementations receipt.request.references root receipt.request.requested
    receipt.location.owner receipt.location.name receipt.location.rootOwner receipt.location.rootName
    receipt.location.site receipt.prepared receipt.evidence.checked receipt.evidence.source
    link.markerIndex prepared.source.pending.entries[link.queueIndex] receipt.location.path
    link.binding.instanceBinding link.subject

private def oneHopLinkedSummary {sources} : LinkedArmSummary sources → Option (Nat × Nat × String × Nat × Nat)
  | (([(_,_,ordinal,name,position,_,_)],none,.thenOp left right),_) => some (ordinal,position,name,left,right)
  | _ => none

private abbrev ObservingSummary :=
  List Nat × List Nat × List Nat × List Nat × List (Nat × Nat × List Nat) × Nat × Nat × Nat

private abbrev SelectionObservation := List RuntimeSelectionSteps.Edge × Nat × Nat × Nat

private def literalSize {dependencies program block node} (w : @RuntimeSelectionWitness.Checked dependencies program block node) : Nat × Nat :=
  match w with | .selection literal _ => (literal.chunks.length,literal.traceResult.events.length)

private def observeStoredSelections {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) :
    WorkM (List SelectionObservation) := do
  (List.finRange body.selections.count).mapM fun i => do
    let hit ← RuntimeSelectionSteps.locate body.selections i
    let ordinal := hit.found.ordinal
    let size := literalSize hit.found.literal
    return (hit.path,ordinal,size.1,size.2)

private abbrev PrimitiveView := String × Nat × List Nat × Nat × Nat
private def primitiveView {dependencies program block start count input output role kind}
    {action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (binding : RuntimePrimitiveSource.Checked action) : Option PrimitiveView :=
  match binding.event with
  | .phase event => some ("phase",event.call.calleeOffset,[event.application.j.result.value,event.application.k.result.value,event.application.coefficient.exponent],input,output)
  | .primitive event => some (String.intercalate "::" (event.call.call.callee.map (·.text)),event.call.calleeOffset,[],input,output)
  | _ => none

private def literalName {input output operation} : RuntimeNamedPrimitiveOccurrence.Literal input output operation → String
  | .gate .h => "gate h"
  | .gate _ => "other gate"
  | .applyUnitary _ => "apply_unitary"

private def sourceAndLiteral {dependencies program block} (step : RuntimePureBody.Step dependencies program block) :
    Option (PrimitiveView × String) := do
  let .named written bound ← RuntimeNamedPrimitiveOccurrence.inspect? step
  let source ← primitiveView written
  let location ← written.location
  let .direct subject positions entry := location.origin | none
  let event ← subject.events[entry.ordinal]?
  let position ← positions[entry.ordinal]?
  if entry.ordinal == 0 && position == location.position && event.offset == written.event.offset &&
      position.offset == event.offset && position.start == 0 && position.count == 1 then
    return (source,literalName bound.form)
  else none

private abbrev CallView := String × Nat × List Nat × List Nat × List Nat × List Nat × List Nat × Option (PrimitiveView × String)

private def namedView {dependencies program block} : RuntimePureBody.Step dependencies program block → Option CallView
  | step@(.named event scope _ _ boundary _ _) =>
    let tokens := scope.selected.map (·.token)
    some (event.target.resolution.declaration.name,event.call.calleeOffset,
      boundary.input.ordered.map (·.port.token),tokens,RuntimeNamedFrameAxes.mixedAxes scope,
      (PureInterval.spectators scope.interval.before tokens).map (·.token),scope.returned.map (·.token),sourceAndLiteral step)
  | _ => none

private def checkStoredMiddle {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (offset : Nat) : WorkM Unit := do
  let observations ← observeStoredSelections body
  guard (observations == [([.nextOrdinal 1,.atOrdinal 1,.named 1 "main" "route" offset "main" "choose",
    .atOrdinal 0,.pureStep 0],0,1,1)]) .invalid

private def observingRuntime (p : ObservingPayload) (composed : Bool) : WorkM ObservingSummary := do
  let prepared ← RuntimeBodyOperations.prepare p.artifact "main" "route" {} p.context
  let checked ← RuntimeBodyOperations.read prepared p.order p.runtime
  checkStoredMiddle checked (if composed then 666 else 515)
  let summaries := checked.checked.receipts.map fun receipt => originalMarkerSummary receipt.request.origin
    receipt.prepared receipt.evidence.checked receipt.evidence.source
  exactWork (Exact.charge (16*(checked.checked.receipts.length+1)^2))
  guard ((summaries.map (·.1)).sum == 2 &&
    summaries.flatMap (·.2) == (if composed then [(325,4,"Identity")] else [])) .request
  -- Both table entries retain the written qmatch and the direct route→choose
  -- call from the frozen source. A declaration occurrence has a different offset.
  let sites := checked.checked.receipts.filterMap fun receipt => do
    let (index,label,keyword) ← originalArmSite receipt.location.site
    let offset ← directChooseOffset receipt.location.path
    return (index,label,keyword,offset)
  let keyword := if composed then 302 else 169
  let offset := if composed then 666 else 515
  guard (sites == [(0,0,keyword,offset),(1,1,keyword,offset)]) .request
  let bindings := checked.writtenLinks.map fun link =>
    (link.binding.located.record,link.binding.instanceBinding.demand.source.original.origin.offset)
  guard (bindings == (if composed then [(4,325)] else [])) .request
  let linked := checked.writtenLinks.map fun link =>
    (summarizeLink checked.checked link).bind oneHopLinkedSummary
  guard (linked == (if composed then [some (0,0,"U",0,1)] else [])) .request
  let result := checked.checked.result
  return (result.history.issued.map (·.ordinal),result.retired.map (·.ordinal),
    result.history.bindings.map (·.port.token),observingHistoryCounts 3 checked.checked.ordinary.rows,
    result.ordinary.measurements.map (fun measurement =>
      (measurement.owner.ordinal,measurement.origin.offset,measurement.calls.map (·.offset))),
    result.steps.length,checked.checked.receipts.length,(prepared.source.pending.entries.filter (·.unconsumed)).length)


/-- The inner call passes W. The outer call supplies then_op(sign,sign).
Both use the same literal Raw interval. -/
private def forwardedSignedSource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Identity:Bit=reference(keep);
meaning Sign:Bit=reference(sign);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {
    qmatch(s,q){0=>keep,1=>checked_op(U,Identity)}
}
unitary fn relay[const W:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(W),Controllable(W) {choose[W](s,q)}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    relay[then_op(sign,sign)](s,q)
}
"#

private def checkForwardedCommonBody (interior : Bool := false) (dormant : Bool := false) : WorkM Unit := do
  let (seed,order) ← Protocol.Qirf.readAll artifactBytes
  let request ← Protocol.QmatchV5.readRequest requestBytes
  let [(_,selection)] := request.context.calls | throw .invalid
  let inner : SourceSequence.Position := ⟨465,0,3⟩
  let outer : SourceSequence.Position := ⟨if interior then 554 else 543,0,3⟩
  let signedInputs := selection.bodies.take (if interior then 1 else 2)
  let relay : Context := .withReferences [inner] [] [(inner,selection)] [] signedInputs [[]] []
  let context : Context := .mk [outer] [] [(outer,relay)] [] []
  let source := if interior then
      (forwardedSignedSource.replace "choose[W](s,q)" "choose[then_op(W,W)](s,q)").replace
        "relay[then_op(sign,sign)](s,q)" "relay[sign](s,q)"
    else forwardedSignedSource
  let source := if dormant then source ++
    "unitary fn dormant(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qmatch(s,q){0=>keep,1=>checked_op(keep,Identity)}}\n"
    else source
  let artifact := {seed with sources := #[("main",source)]}
  let body ← RuntimeBodyOperations.prepare artifact "main" "route" {} context
  let checked ← RuntimeBodyOperations.read body order request.runtime
  let [some ((hops,inside,_),_)] := checked.writtenLinks.map (summarizeLink checked.checked) | throw .invalid
  guard (body.source.pending.entries.countP (·.unconsumed) == (if dormant then 2 else 1)) .invalid
  let [⟨index,witness⟩] := checked.coverage.consumed | throw .invalid
  guard (witness.link.binding.instanceBinding.demand.source.original.origin.offset == 325) .invalid
  if dormant then
    let [other] := checked.coverage.residual | throw .invalid
    let .demand _ remaining := body.source.pending.entries[other].subject | throw .invalid
    guard (other != index && remaining.source.original.origin.state.name == "dormant") .invalid
  else guard checked.coverage.residual.isEmpty .invalid
  if interior then
    let some located := inside | throw .invalid
    guard (hops == [("main","choose",0,"U",0,0,some 472)] &&
      located.rows == [([0],0,1,"W",0,some 480,some 560),([1],1,3,"W",0,some 482,some 560)]) .invalid
  else
    guard (inside.isNone && hops == [("main","choose",0,"U",0,0,some 472),
      ("main","relay",0,"W",0,0,some 549)]) .invalid

-- The same original signed source and three literal call intervals as
-- constructed-transfer-common-body-first. Reuse the existing nine programs,
-- evidence and arm/reference requests; do not embed another packet copy.
private def fourLevelSignedSource : String :=
  (((forwardedSignedSource.replace "choose[W](s,q)" "choose[then_op(W,W)](s,q)").replace
    "pub unitary fn route"
    ("unitary fn outer[const X:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)\n" ++
     "    requires Applicable(X),Controllable(X) {relay[X](s,q)}\n" ++
     "pub unitary fn route")).replace
    "relay[then_op(sign,sign)](s,q)" "outer[sign](s,q)")

private def checkFourLevelCommonBody : WorkM Unit := do
  let (seed,order) ← Protocol.Qirf.readAll artifactBytes
  let request ← Protocol.QmatchV5.readRequest requestBytes
  let [(_,selection)] := request.context.calls | throw .invalid
  let inner : SourceSequence.Position := ⟨465,0,3⟩
  let middle : SourceSequence.Position := ⟨606,0,3⟩
  let outer : SourceSequence.Position := ⟨683,0,3⟩
  let supplied := selection.bodies.take 1
  let relay : Context := .withReferences [inner] [] [(inner,selection)] [] supplied [[]] []
  let outside : Context := .withReferences [middle] [] [(middle,relay)] [] supplied [[]] []
  let context : Context := .mk [outer] [] [(outer,outside)] [] []
  let artifact := {seed with sources := #[("main",fourLevelSignedSource)]}
  let body ← RuntimeBodyOperations.prepare artifact "main" "route" {} context
  let checked ← RuntimeBodyOperations.read body order request.runtime
  guard (body.source.pending.entries.countP (·.unconsumed) == 1) .invalid
  let [⟨_,witness⟩] := checked.coverage.consumed | throw .invalid
  guard (checked.coverage.residual.isEmpty && witness.link.binding.located.record == 8 &&
    witness.link.binding.instanceBinding.invocation.depth == 3) .invalid
  let bindings := checked.writtenLinks.map fun link =>
    (link.binding.instanceBinding.invocation.depth,link.binding.located.record,
      link.binding.instanceBinding.demand.source.original.origin.offset)
  guard (bindings == [(3,8,325)]) .invalid
  let sites := checked.checked.receipts.filterMap fun receipt => originalArmSite receipt.location.site
  guard (sites == [(0,0,302),(1,1,302)]) .invalid
  let [some ((hops,some inside,_),_)] := checked.writtenLinks.map (summarizeLink checked.checked) | throw .invalid
  guard (hops == [("main","choose",0,"U",0,0,some 472)] &&
    inside.rows == [([0],0,2,"W",0,some 480,some 612),([1],1,5,"W",0,some 482,some 612)] &&
    inside.observed == inside.expected) .invalid
  let some [[leftW,leftX],[rightW,rightX]] := inside.trees | throw .invalid
  guard ([tailBasic leftW,tailBasic leftX,tailBasic rightW,tailBasic rightX] ==
    [([0],"relay","W",0,0,0,2,1,some 612,false,1,1),
     ([0],"outer","X",0,0,0,1,0,some 689,true,0,1),
     ([1],"relay","W",1,1,1,5,4,some 612,false,1,1),
     ([1],"outer","X",1,1,1,4,3,some 689,true,0,1)]) .invalid
  guard ([leftW.key,leftX.key,rightW.key,rightX.key] ==
    [⟨"main","relay",0⟩,⟨"main","outer",0⟩,⟨"main","relay",0⟩,⟨"main","outer",0⟩] &&
    leftW.rowOffset == 0 && leftX.rowOffset == 0 && leftW.localSuppliers > 0 && leftX.localSuppliers > 0 &&
    rightW.rowOffset == leftW.localSuppliers && rightX.rowOffset == leftX.localSuppliers) .invalid
  let result := checked.checked.result
  guard (result.history.issued.map (·.ordinal) == [0,1] && result.history.nextOrdinal == 2 && result.retired.isEmpty &&
    result.history.bindings.map (·.owner.ordinal) == [0,1] &&
    result.history.bindings.map (·.port.token) == [4,5]) .invalid

private inductive ObservingFault where
  | correct | wrongMeasurementOwner | wrongXor | contextOrder | omittedUnitOwner | wrongSelectedPhase
  | extraReference | missingReference
  deriving BEq, Repr

/-- Change untrusted data only. Original source, expected owners/results and
complete runtime input rows remain unchanged for every observingMutation. -/
private def observingMutation (p : ObservingPayload) (fault : ObservingFault) : WorkM ObservingPayload := do
  let some original := p.artifact.programs[0]? | throw .request
  let [first,xor,.pure (.join left right joined),action,split,last,result] := original.operations | throw .request
  let phaseFault := match action with
    | .pure (.applyUnitary input output steps) =>
      -- Erasing both signs would preserve the constructed identity. One
      -- independent literal controlled sign changes its exact relative phase.
      let wrong := if steps.length > 1 then
        [(⟨[⟨0,true⟩],.monomial [1] [0,1] [0,4]⟩ : Semantics.Finite.Step)] else []
      Semantics.Observation.Op.pure (.applyUnitary input output wrong)
    | other => other
  let operations := match fault with
    | .wrongMeasurementOwner => [.measure right 1,xor,.pure (.join left 7 joined),action,split,last,result]
    | .wrongXor => [first,.and 0 1 2,.pure (.join left right joined),action,split,last,result]
    | .wrongSelectedPhase => [first,xor,.pure (.join left right joined),phaseFault,split,last,result]
    | _ => original.operations
  let keptInputs := if fault == .omittedUnitOwner then original.inputs.filter (·.token != 6) else original.inputs
  let keptOutputs := if fault == .omittedUnitOwner then original.outputs.filter (· != 6) else original.outputs
  let program : Semantics.Observation.Program :=
    {original with operations := operations, inputs := keptInputs, outputs := keptOutputs}
  let calls ← if fault == .extraReference || fault == .missingReference then do
      let [(before,first),(choose,child),(after,last)] := p.context.calls | throw .request
      let references := if fault == .extraReference then child.references ++ [[]] else child.references.dropLast
      let child := RuntimeContextRequest.Context.withReferences child.positions child.sites child.calls child.branches
        child.bodies references child.staticIntervals
      pure [(before,first),(choose,child),(after,last)]
    else pure (if fault == .contextOrder then p.context.calls.reverse else p.context.calls)
  let context := RuntimeContextRequest.Context.withReferences p.context.positions p.context.sites calls
    p.context.branches p.context.bodies p.context.references p.context.staticIntervals
  let artifact := {p.artifact with programs := p.artifact.programs.set! 0 program}
  let rootArtifact := if fault == .wrongSelectedPhase then
      {p.rootArtifact with programs := #[program], entries := #[]}
    else {p.rootArtifact with programs := p.rootArtifact.programs.set! 0 program}
  let rootOrder := if fault == .wrongSelectedPhase then #[0] else p.rootOrder
  return {p with context := context, artifact := artifact, rootArtifact := rootArtifact, rootOrder := rootOrder}

private def observingRaw (p : ObservingPayload) : WorkM (List Nat × List Nat) := do
  let dependencies ← Qirf.checkGraphWithSources p.rootArtifact p.rootOrder p.rootArtifact.sources.toList
  let some program := p.rootArtifact.programs[0]? | throw .request
  let _ ← Raw.Observation.verify dependencies program
  let histories ← p.runtime.inputRows.mapM fun row => do
    let checked ← Raw.Instrument.reconstruct dependencies program row
    pure checked.histories.length
  pure (histories,program.outputs)


private def observingStudy (composed : Bool) (fault : ObservingFault) :=
  (do
    let proposal ← observingPayload composed
    let proposal ← observingMutation proposal fault
    observingRuntime proposal composed).run WorkProfile.qmatch.limit |>.1

private def observingRawStudy (composed : Bool) (fault : ObservingFault) :=
  (do
    let proposal ← observingPayload composed
    let proposal ← observingMutation proposal fault
    let raw ← observingRaw proposal
    let rows ← observingTypedRoot proposal
    pure (raw,rows)).run WorkProfile.qmatch.limit |>.1

private def observingExpected (composed : Bool) : ObservingSummary :=
  if composed then
    ([0,1,2,3],[1,3],[6,4],[4,4],[(1,382,[639,446]),(3,382,[709,518])],3,3,1)
  else
    ([0,1,2,3],[1,3],[6,4],[4,4],[(1,231,[488,295]),(3,231,[538,367])],3,2,0)

#guard (observingStudy false .correct).toOption == some (observingExpected false)
#guard (observingStudy true .correct).toOption == some (observingExpected true)
#guard observingStudy false .wrongMeasurementOwner matches .error .invalid
#guard observingStudy false .wrongXor matches .error .equation
#guard observingStudy false .wrongSelectedPhase matches .error .equation
#guard [ObservingFault.contextOrder,.omittedUnitOwner,.extraReference,.missingReference].all fun fault =>
  match observingStudy false fault with | .error .request => true | _ => false
#guard observingStudy true .wrongMeasurementOwner matches .error .invalid
#guard observingStudy true .wrongXor matches .error .equation
#guard observingStudy true .wrongSelectedPhase matches .error .equation
#guard [ObservingFault.contextOrder,.omittedUnitOwner,.extraReference,.missingReference].all fun fault =>
  match observingStudy true fault with | .error .request => true | _ => false

-- Raw/type/history validity alone cannot bind the original source. The phase
-- mutation's compact Raw control keeps its exact root and removes newly
-- unreachable auxiliary nodes; the full source graph keeps every original arm.
#guard [ObservingFault.correct,.wrongMeasurementOwner,.wrongXor,.contextOrder,
    .extraReference,.missingReference,.wrongSelectedPhase].all fun fault =>
  (observingRawStudy false fault).toOption == some (([4,4],[6,4]),2)
#guard [ObservingFault.correct,.wrongMeasurementOwner,.wrongXor,.contextOrder,
    .extraReference,.missingReference,.wrongSelectedPhase].all fun fault =>
  (observingRawStudy true fault).toOption == some (([4,4],[6,4]),2)
#guard observingRawStudy false .omittedUnitOwner matches .error .request
#guard observingRawStudy true .omittedUnitOwner matches .error .request

-- The two written calls have the same provider and the same static actual.
-- Queue entries 11 and 19 belong to different source invocations of duty 3.
private def repeatedChooseSource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Identity:Bit=reference(keep);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {
    qmatch(s,q){0=>keep,1=>checked_op(U,Identity)}
}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    let (s,q)=choose[keep](s,q);
    choose[keep](s,q)
}
"#

private def readRepeatedChoose (secondCall secondDuty : Bool) : WorkM (Nat × Nat × Nat) := do
  let artifact : Artifact := ⟨#[],#[],#[("main",repeatedChooseSource)],0,none⟩
  let source ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let [.named first,.named last] := source.body.checked.events | throw .invalid
  let event := if secondCall then last else first
  let [firstDuty,lastDuty] := source.pending.entries.filter (·.unconsumed) | throw .invalid
  let entry := if secondDuty then lastDuty else firstDuty
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody event)
  if caller : event.target.callerName = "route" then
    let parent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route" "main" event.target.callerName := by
      simpa only [caller] using (RuntimeOrdinaryBody.CallPath.root source.body)
    let path := RuntimeOrdinaryBody.CallPath.named event body.val (by with_reducible exact body.property) parent
    let bound ← RuntimeDutyInvocation.readDemand entry path
    return (event.call.calleeOffset,entry.index.val,bound.demand.source.index.val)
  else throw .invalid

private def checkRepeatedChoose : IO Unit := do
  for secondCall in [false,true] do
    for secondDuty in [false,true] do
      let outcome := ((readRepeatedChoose secondCall secondDuty).run WorkProfile.qmatch.limit).1
      if secondCall == secondDuty then
        let expected := if secondCall then (412,19,3) else (389,11,3)
        unless outcome.toOption == some expected do
          throw (IO.userError "original call failed to select its own written duty")
      else
        match outcome with
        | .error .request => pure ()
        | _ => throw (IO.userError "sibling call's written duty must refuse at the request boundary")

-- Compare original slots even when all supplied operators act as identity.
-- The source and token positions are fixed independently of all native reads.
private def mixedSupplySource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn idle(q:Q<Bit>)->Q<Bit>{q}
meaning Identity:Bit=reference(keep);
unitary fn choose[const U:Op<Bit>,const N:Nat,const V:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U),Applicable(V),Controllable(V) {
    qmatch(s,q){0=>keep,1=>checked_op(V,Identity)}
}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    let (s,q)=choose[then_op(keep,idle),1,then_op(keep,idle)](s,q);
    choose[then_op(keep,idle),1,then_op(keep,idle)](s,q)
}
"#

private def expectSupplyRefusal {α : Type} (action : WorkM α) : WorkM Unit := do
  let refused ← try
    let _ ← action
    pure false
  catch error => match error with
    | .request => pure true
    | other => throw other
  guard refused .invalid

-- Both reversed tokens identify live ports with the same dimensions. The
-- original named event still fixes their order, including when the values agree.
private def checkWrongInputOrder {dependencies program block start count inputs sources caller before child retired value}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    {event : SourceRuntimeContext.NamedEvent sources caller}
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired value) : WorkM Unit := do
  let wrong := inputs.reverse
  let some selected := PureInterval.ports interval.before wrong | throw .invalid
  guard (wrong != inputs && selected == (boundary.input.ordered.map (·.port)).reverse) .invalid
  expectSupplyRefusal (RuntimeNamedBoundary.read interval wrong event before child retired value)

open QleisliKernel.Qirf.RuntimeNamedThreeOccurrence (Middle RetainedData)

private abbrev OriginalOperands := Nat × Nat × List Nat × List (List Nat)

private def originalOperands {dependencies program block} : RuntimePureBody.Step dependencies program block → Option OriginalOperands
  | .named (start := first) (count := size) event _ _ _ _ _ _ =>
    some (first,size,event.inputOwners.map (·.ordinal),
      event.arguments.map (fun argument => (QleisliKernel.SourceTypes.SourceRuntimeValues.valueOwners argument).map (·.ordinal)))
  | _ => none

private abbrev SpectatorData := List (Nat × List Nat × Nat)
private def spectatorsData {dependencies program block} : RuntimePureBody.Step dependencies program block → Option SpectatorData
  | .named _ scope _ _ _ _ _ =>
    some ((PureInterval.spectators scope.interval.before (scope.selected.map (·.token))).map
      (fun port => (port.token,port.wires,port.bits)))
  | _ => none

private abbrev MiddleData := String × Nat × Nat × List RuntimeSelectionSteps.Edge × Nat × Nat

private def middleCoversCall {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (middle : @Middle dependencies program block step) (held : RetainedData witness middle) : Bool :=
  match middle,held with
  | .named (start := start) (count := count) (scope := scope) _ _,held =>
    match held.literal with
    | .selection (start := first) (count := size) _ _ =>
      first == 0 && size == ((block.operations.drop start).take count).length &&
        scope.interval.before.quantum.frame.length == 2

/-- `held.literal` and `held.obtained` are literally the stored leaf returned
by actual_body_middle; their indices are this exact original middle Step. -/
private def retainedMiddleData {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (middle : @Middle dependencies program block step) (held : RetainedData witness middle) : MiddleData :=
  match middle,held with
  | .named (event := event) node _,held =>
    have _sameRead : RuntimeInterval.Computed (RuntimeSelectionWitness.read node) held.literal := held.obtained
    have _sameOccurrence : RuntimeSelectionSteps.At witness held.rank held.path
      ⟨_,_,0,node,held.literal,held.obtained⟩ := held.original
    let size := literalSize held.literal
    (event.target.resolution.declaration.name,event.call.calleeOffset,held.rank,held.path,size.1,size.2)


private def checkOrderedOriginalCalls : WorkM Unit := do
  let (decoded,order) ← Protocol.Qirf.readAll artifactBytes
  let original ← Protocol.QmatchV5.readRequest requestBytes
  let (artifact,request) ← lift ((orderedCallProposal decoded original .none).mapError fun _ => .invalid)
  let prepared ← RuntimeBodyOperations.prepare artifact request.source.moduleName request.source.functionName request.source.arguments request.context
  let body ← RuntimeBodyOperations.read prepared order request.combinedRuntime
  let some view := QleisliKernel.Qirf.RuntimeNamedThreeOccurrence.inspect? body.checked.result.steps
    | throw .invalid
  have _first : body.checked.result.steps[0]? = some view.pre := view.preAt
  have _middle : body.checked.result.steps[1]? = some view.center := view.centerAt
  have _last : body.checked.result.steps[2]? = some view.post := view.postAt
  let held := RuntimeNamedThreeOccurrence.actual_body_middle body view
  guard (middleCoversCall view.centerSelection held) .invalid
  let middle := retainedMiddleData view.centerSelection held
  let some calls := [view.pre,view.center,view.post].mapM namedView | throw .invalid
  guard (calls == [
    ("pre",531,[1],[1],[1],[8,0],[2],some (("phase",384,[1,1,4],1,2),"apply_unitary")),
    ("choose",553,[0,2],[0,2],[0,1],[8],[5,6],none),
    ("post",596,[6],[6],[1],[8,5],[7],some (("h",437,[],6,7),"gate h"))]) .invalid
  guard ([view.pre,view.center,view.post].map originalOperands == [
    some (0,1,[2],[[2]]),some (1,3,[1,2],[[1],[2]]),some (4,1,[2],[[2]])]) .invalid
  guard ([view.pre,view.center,view.post].map spectatorsData == [
    some [(8,[],0),(0,[0],1)],some [(8,[],0)],some [(8,[],0),(5,[0],1)]]) .invalid
  guard (middle == ("choose",553,0,
    [.nextOrdinal 1,.atOrdinal 1,.named 1 "main" "route" 553 "main" "choose",.atOrdinal 0,.pureStep 0],1,1)) .invalid
  guard (body.selections.count == 1) .invalid
  -- This is the complete list, not a filtered list of named calls. These
  -- malformed shapes are inspected without changing the original body.
  guard ((QleisliKernel.Qirf.RuntimeNamedThreeOccurrence.inspect? (body.checked.result.steps.take 2)).isNone &&
    (QleisliKernel.Qirf.RuntimeNamedThreeOccurrence.inspect? (body.checked.result.steps ++ [view.post])).isNone &&
    (QleisliKernel.Qirf.RuntimeNamedThreeOccurrence.inspect? [view.pre,view.post,view.center]).isNone) .invalid
  let [_,step,_] := body.checked.result.steps | throw .invalid
  match step with
  | .named _ _ _ _ boundary _ _ => checkWrongInputOrder boundary
  | _ => throw .invalid

private def keepSignSource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
unitary fn choose(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    qmatch(s,q){0=>keep,1=>sign}
}
unitary fn pre(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
pub unitary fn post(q:Q<Bit>)->Q<Bit>{h(q)}
pub unitary fn route(u:Q<Unit>,s:Q<Bit>,q:Q<Bit>)->(Q<Unit>,(Q<Bit>,Q<Bit>)){
    let q=pre(q);
    let (s,q)=choose(s,q);
    let q=post(q);
    (u,(s,q))
}
"#

private inductive SmallFault where
  | none | wrongOrder | relativeSign
  deriving BEq, Repr

private def bitPort (token wire : Nat) : Semantics.Raw.Port := ⟨token,[wire],1⟩
private def unitPort : Semantics.Raw.Port := ⟨8,[],0⟩
private def zSteps : List Semantics.Finite.Step := [⟨[],.monomial [0] [0,1] [0,4]⟩]
private def singleProgram (signed : Bool) : Semantics.Observation.Program :=
  ⟨[bitPort 0 0],[],if signed then [.pure (.applyUnitary 0 1 zSteps)] else [],
    [if signed then 1 else 0],[],.unitary⟩
private def controlledProgram (signed : Bool) : Semantics.Observation.Program :=
  ⟨[bitPort 0 0,bitPort 1 1],[],[.pure (.quantumIf 0 1 2 3 [] (if signed then [.gate .z 0] else []))],
    [2,3],[],.unitary⟩

/-- Untrusted proposal for keepSignSource. The original named
pre/choose/post body, source effect and Unit spectator are freshly re-read. -/
private def keepSignPayload (fault : SmallFault) : Artifact × Array Nat × Request := Id.run do
  let first : Semantics.Observation.Op := if fault == .wrongOrder then .pure (.gate .h 1 2)
    else .pure (.applyUnitary 1 2 zSteps)
  let last : Semantics.Observation.Op := if fault == .wrongOrder then .pure (.applyUnitary 6 7 zSteps)
    else .pure (.gate .h 6 7)
  let one : List Semantics.Raw.UnitaryStep := if fault == .relativeSign then [.phase .minusOne,.gate .z 0]
    else [.gate .z 0]
  let rootProgram : Semantics.Observation.Program :=
    ⟨[unitPort,bitPort 0 0,bitPort 1 1],[],[first,.pure (.quantumIf 0 2 5 6 [] one),last],[8,5,7],[],.unitary⟩
  let artifact : Artifact := ⟨#[rootProgram,singleProgram false,controlledProgram false,
    singleProgram true,controlledProgram true],#[],#[("main",keepSignSource)],0,none⟩
  let empty : Context := .mk [] [] [] [] []
  let signBody : Context := .mk [⟨95,0,1⟩] [] [] [] []
  let preBody : Context := .mk [⟨233,0,1⟩] [] [] [] []
  let postBody : Context := .mk [⟨286,0,1⟩] [] [] [] []
  let portsIn : List Semantics.CarrierInterface.Owner := [⟨bitPort 0 0,[.bit]⟩,⟨bitPort 2 1,[.bit]⟩]
  let portsOut : List Semantics.CarrierInterface.Owner := [⟨bitPort 5 0,[.bit]⟩,⟨bitPort 6 1,[.bit]⟩]
  let interface : Semantics.CarrierInterface.Interface := ⟨portsIn,portsOut,.unitary⟩
  let inner : Position := ⟨169,0,1⟩
  let site : RuntimeContextRequest.Site := ⟨interface,interface,inner,[⟨1,2⟩,⟨3,4⟩]⟩
  let chooseBody : Context := .withReferences [inner] [site] [] []
    [(.pure 1,empty),(.pure 3,signBody)] [[],[]] []
  let positions : List Position := [⟨380,0,1⟩,⟨402,1,1⟩,⟨425,2,1⟩]
  let context : Context := .mk positions []
    [(⟨380,0,1⟩,preBody),(⟨402,1,1⟩,chooseBody),(⟨425,2,1⟩,postBody)] [] []
  let unitTree := Semantics.RuntimeType.owner [.unit]
  let bitTree := Semantics.RuntimeType.owner [.bit]
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",[unitTree,bitTree,bitTree],
      [[.quantum ⟨unitPort,[.unit]⟩],[.quantum ⟨bitPort 0 0,[.bit]⟩],[.quantum ⟨bitPort 1 1,[.bit]⟩]],
      [[]],Semantics.RuntimeType.tuple 2 [unitTree,Semantics.RuntimeType.tuple 2 [bitTree,bitTree]],
      [.tuple 2,.quantum ⟨unitPort,[.unit]⟩,.tuple 2,.quantum ⟨bitPort 5 0,[.bit]⟩,.quantum ⟨bitPort 7 1,[.bit]⟩],
      .unitary,{}⟩
  return (artifact,#[0,1,2,3,4],⟨⟨"main","route",{}⟩,runtime,context⟩)

/-- Read the coefficient function already stored in the unique pure history. -/
private def storedHistory {sources owner name signature dependencies program body prepared runtime inputs initial ssa bindings assignments}
    (rows : @RuntimeOrdinaryHistories.Rows sources owner name signature dependencies program body prepared runtime inputs
      initial ssa bindings assignments) : Option Raw.StreamedInstrument.History :=
  match rows with
  | .cons row .nil =>
    match row.histories with
    | [history] => if history.hidden.isEmpty && history.values.isEmpty then some history else none
    | _ => none
  | _ => none

/-- ±sqrt(2)/2 in the exact independent R8 coefficient domain. -/
private def halfRootSigned (negative : Bool) : Semantics.Exact.Scalar :=
  ⟨.integer 0,⟨if negative then -1 else 1,1⟩,.integer 0,.integer 0⟩

/-- Source basis labels are low-first (s,q); Unit has one label and zero axes.
pre is Z on q. choose is I (sign;sign) or CZ (keep/sign). post is H on q.
Thus U[r,c] = delta(s_r,s_c) /sqrt(2) *
(-1)^(q_c*(1+q_r+s_c)) for CZ, omitting s_c for the Identity choice.
Wrong-order and relative-selector-phase oracles deliberately change that
independently stated expression. No native action/summary supplies a sign. -/
private def sourceOracleEntry (signedCZ wrongOrder relativeFlip : Bool) (row col : Nat) : Semantics.Exact.Scalar :=
  if row % 2 != col % 2 then .zero else
  let selector := if signedCZ then col % 2 else 0
  let inputTarget := col / 2
  let outputTarget := row / 2
  let exponent := if wrongOrder then outputTarget*(1+selector+inputTarget)
    else inputTarget*(1+selector+outputTarget)
  let exponent := exponent + (if relativeFlip then col % 2 else 0)
  halfRootSigned (exponent % 2 == 1)

private def sourceOracle (signedCZ wrongOrder relativeFlip : Bool) : List Semantics.Exact.Scalar :=
  (List.range 4).flatMap fun row => (List.range 4).map fun col => sourceOracleEntry signedCZ wrongOrder relativeFlip row col

private def originalPayload (wrongOrder : Bool) : WorkM (Artifact × Array Nat × Request) := do
  let (decoded,order) ← Protocol.Qirf.readAll artifactBytes
  let original ← Protocol.QmatchV5.readRequest requestBytes
  let (artifact,request) ← lift ((orderedCallProposal decoded original (if wrongOrder then .wrongOrder else .none)).mapError fun _ => .invalid)
  return (artifact,order,request)

/-- All 16 actual root entries are evaluated from its SAME retained history,
including the final original output ordering. No new native acceptance path. -/
private def rootOracle (signedCZ : Bool) (fault : SmallFault) : WorkM Unit := do
  let (artifact,order,request) ← if signedCZ then pure (keepSignPayload fault) else originalPayload (fault == .wrongOrder)
  guard request.compatible .request
  let prepared ← RuntimeBodyOperations.prepare artifact request.source.moduleName request.source.functionName
    request.source.arguments request.context
  let body ← RuntimeBodyOperations.read prepared order request.combinedRuntime
  guard (body.checked.native.whole.prepared.inputBits == 2 && body.checked.native.whole.state.quantum.frame.length == 2 &&
    body.root.program.classicalInputs.isEmpty && body.root.program.classicalOutputs.isEmpty) .invalid
  guard (body.root.program.inputs.map (fun port => (port.token,port.wires,port.bits)) ==
    [(8,[],0),(0,[0],1),(1,[1],1)] && body.root.program.outputs == [8,5,7]) .invalid
  let calls := body.checked.result.steps.map fun step => match step with
    | .named event .. => some (event.target.resolution.declaration.name,event.call.calleeOffset,event.inputOwners.map (·.ordinal))
    | _ => none
  guard (calls == (if signedCZ then [some ("pre",380,[2]),some ("choose",402,[1,2]),some ("post",425,[2])]
    else [some ("pre",531,[2]),some ("choose",553,[1,2]),some ("post",596,[2])])) .invalid
  let some history := storedHistory body.checked.ordinary.rows | throw .invalid
  let matrixRows ← (List.range 4).mapM fun row => (List.range 4).mapM fun col => history.operator row col
  let entries := matrixRows.flatten
  guard (entries == sourceOracle signedCZ false false) .equation
  guard (entries != sourceOracle signedCZ true false && entries != sourceOracle signedCZ false true) .invalid
  guard (body.checked.result.history.issued.map (·.ordinal) == [0,1,2]) .invalid

private def checkRootCoefficients : IO Unit := do
  for (signedCZ,fault) in [(false,SmallFault.none),(true,.none),(false,.wrongOrder),
      (true,.wrongOrder),(true,.relativeSign)] do
    match fault, (rootOracle signedCZ fault).run WorkProfile.qmatch.limit |>.1 with
    | .none,.ok () | .wrongOrder,.error .equation | .relativeSign,.error .equation => pure ()
    | _,answer => throw (IO.userError s!"ordered root coefficients (CZ={signedCZ}, {repr fault}): {repr answer}")

private def checkSuppliedSlot {sources catalogue record}
    (first last : SourceRuntimeContext.NamedEvent sources "main") (choice : RuntimeFormalActual.Choice) :
    (invocation : @GenericDutyQueue.Invocation sources catalogue record) →
    GenericDutyQueue.Demand invocation → WorkM Unit
  | .root _,_ => throw .invalid
  | .call _ app _,demand => do
    let transfer := RuntimeFormalActual.substitution demand
    let key : Semantics.SymbolicBasis.Parameter := ⟨"main","choose",2⟩
    let [u,v] := first.target.operationActuals.sourceActuals | throw .invalid
    let [laterU,laterV] := last.target.operationActuals.sourceActuals | throw .invalid
    guard (u.checked.description == v.checked.description && v.checked.description == laterV.checked.description &&
      u.index.val == 0 && v.index.val == 2 && u.name == "U" && v.name == "V") .invalid
    let offsets := [u.actual.argument.tokens,laterU.actual.argument.tokens,
      v.actual.argument.tokens,laterV.actual.argument.tokens].map fun tokens => tokens.head?.map (·.span.startByte)
    guard (offsets == [some 442,some 500,some 463,some 521]) .invalid
    let supply ← RuntimeFormalActual.readSupply first app.original transfer key choice
    guard (choice.position == 1 && choice.header.ordinal == 2 && choice.header.name == "V" &&
      supply.source.actual.argument.tokens.head?.map (·.span.startByte) == some 463) .invalid
    expectSupplyRefusal (RuntimeFormalActual.readSupply first app.original transfer key {choice with position := 0})
    expectSupplyRefusal (RuntimeFormalActual.readSupply first app.original transfer key {choice with header := u.actual.formal})
    -- Both calls resolve to the same declaration, headers and actual graphs.
    -- The later call's supplying argument has a different original token span.
    expectSupplyRefusal (RuntimeFormalActual.readSupply last app.original transfer key choice)

private def mixedSupplyStudy : WorkM Unit := do
  let identity : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩
  let selected : Semantics.Observation.Program :=
    ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.quantumIf 0 1 2 3 [] [])],[2,3],[],.unitary⟩
  let artifact : Artifact := ⟨#[selected,identity],#[],#[("main",mixedSupplySource)],0,none⟩
  let source ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let [.named first,.named last] := source.body.checked.events | throw .invalid
  let [duty,_] := source.pending.entries.filter (·.unconsumed) | throw .invalid
  let callee ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody first)
  if caller : first.target.callerName = "route" then
    let parent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route" "main" first.target.callerName := by
      simpa only [caller] using (RuntimeOrdinaryBody.CallPath.root source.body)
    let path := RuntimeOrdinaryBody.CallPath.named first callee.val (by with_reducible exact callee.property) parent
    let invoked ← RuntimeDutyInvocation.readDemand duty path
    let body := callee.val.checked
    let [.selection _ parsed _ selector target scope naturals ..] := body.events | throw .invalid
    let table ← QuantumArms.readArmsWithInstantiation body.signature.original body.signature.instantiation
      body.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
    let [left,right] := List.finRange table.arms.length | throw .invalid
    let empty : Context := .mk [] [] [] [] []
    let provider : RuntimeProviderHeader.Request := (.pure 1,empty)
    let plain ← RuntimePreparedArm.prepare artifact source.catalogue table left [provider] []
    let arm ← RuntimePreparedArm.prepare artifact source.catalogue table right (List.replicate 4 provider) [[provider]]
    let rows := source.signature.sourceRows ++ body.summary.staticRows ++ first.target.sourceRows ++ plain.rows ++ arm.rows
    let root ← Validity.checkRootFromRoots artifact #[0,1] rows (artifact.root :: plain.roots ++ arm.roots).eraseDups
    let .constructed _ _ _ markers _ ← RuntimePreparedArm.read arm root | throw .invalid
    let [entry] := markers.entries | throw .invalid
    let actual ← RuntimeNativeSubject.readSubject entry.assertion
    let cursor := actual.child.cursor
    let formal ← RuntimeNativeSubject.readFormal cursor
    let choice ← RuntimeFormalActual.readChoice formal
    checkSuppliedSlot first last choice invoked.invocation invoked.demand
    let description := invoked.demand.transported.subject.description
    let .closed correct ← GenericOperation.close description | throw .invalid
    let _ ← RuntimeClosedSubject.read correct cursor
    let some (.thenOp a b) := description.nodes[description.root]? | throw .invalid
    let swapped := {description with nodes := description.nodes.set description.root (.thenOp b a)}
    let .closed wrong ← GenericOperation.close swapped | throw .invalid
    -- Both independent leaves are identities, but the source requests keep then idle.
    expectSupplyRefusal (RuntimeClosedSubject.read wrong cursor)
  else throw .invalid

-- Exact original two-hop source from the independently executed first study.
-- Both inner arguments are the same byte375 occurrence, but their supplying
-- route arguments differ at462/484. Both operators and op-only slots coincide.
private def forwardedSupplySource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
meaning I:Bit=reference(keep);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {
    qmatch(s,q){0=>keep,1=>checked_op(U,I)}
}
unitary fn relay[const W:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(W),Controllable(W) {choose[W](s,q)}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    let (s,q)=relay[keep](s,q);
    relay[keep](s,q)
}
"#

private def rejectCrossedOuterSupply {sources caller original event app transfer key native}
    (other : SourceRuntimeContext.NamedEvent sources "main")
    (_supply : @RuntimeFormalActual.Supply sources caller original event app transfer key native) : WorkM Unit :=
  expectSupplyRefusal (RuntimeFormalActual.readSupply other app transfer key native)

private def rejectOuterChain {artifact catalogue context description graph implementations references prepared root requested checked
    queue rootOwner rootName owner name path record invocation original result native index cursor terminal}
    {binding : @RuntimeDutyInvocation.Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation}
    {transport : GenericDutyQueue.Transport invocation.applications.reverse original result}
    {paired : @RuntimeClosedSubject.Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal}
    (other : SourceRuntimeContext.NamedEvent artifact.sources "main")
    (chain : RuntimeForwardedSupply.Chain binding transport paired) : WorkM Unit := do
  match chain with
  | .direct .. => throw .invalid
  | .formal hop _ _ => rejectCrossedOuterSupply other hop.supply

private def rejectForwardedChain {artifact catalogue context description graph implementations references prepared root requested checked
    queue rootOwner rootName owner name path record invocation original result native index cursor terminal}
    {binding : @RuntimeDutyInvocation.Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation}
    {transport : GenericDutyQueue.Transport invocation.applications.reverse original result}
    {paired : @RuntimeClosedSubject.Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal}
    (other : SourceRuntimeContext.NamedEvent artifact.sources "main")
    (chain : RuntimeForwardedSupply.Chain binding transport paired) : WorkM Unit := do
  match chain with
  | .direct .. => throw .invalid
  | .formal _ _ tail => rejectOuterChain other tail

private def forwardedSupplyStudy (second : Bool) : WorkM (List SupplyHopSummary) := do
  let identity : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩
  let selected : Semantics.Observation.Program :=
    ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.quantumIf 0 1 2 3 [] [])],[2,3],[],.unitary⟩
  let artifact : Artifact := ⟨#[selected,identity],#[],#[("main",forwardedSupplySource)],0,none⟩
  let source ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let [.named first,.named last] := source.body.checked.events | throw .invalid
  let [firstDuty,lastDuty] := source.pending.entries.filter (·.unconsumed) | throw .invalid
  let outer := if second then last else first
  let other := if second then first else last
  let duty := if second then lastDuty else firstDuty
  let otherDuty := if second then firstDuty else lastDuty
  let relay ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody outer)
  let [.named inner] := relay.val.checked.events | throw .invalid
  let choose ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody inner)
  if outerCaller : outer.target.callerName = "route" then
    let parent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route" "main" outer.target.callerName := by
      simpa only [outerCaller] using (RuntimeOrdinaryBody.CallPath.root source.body)
    let relayPath := RuntimeOrdinaryBody.CallPath.named outer relay.val (by with_reducible exact relay.property) parent
    if innerCaller : inner.target.callerName = outer.target.resolution.declaration.name then
      let innerParent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route"
          outer.target.resolution.moduleName inner.target.callerName := by
        simpa only [innerCaller] using relayPath
      let path := RuntimeOrdinaryBody.CallPath.named inner choose.val (by with_reducible exact choose.property) innerParent
      let invoked ← RuntimeDutyInvocation.readDemand duty path
      expectSupplyRefusal (RuntimeDutyInvocation.readDemand otherDuty path)
      let [actual] := outer.target.operationActuals.sourceActuals | throw .invalid
      let [neighbor] := other.target.operationActuals.sourceActuals | throw .invalid
      guard (actual.checked.description == neighbor.checked.description && actual.index.val == 0 && neighbor.index.val == 0) .invalid
      let body := choose.val.checked
      let [.selection _ parsed _ selector target scope naturals ..] := body.events | throw .invalid
      let table ← QuantumArms.readArmsWithInstantiation body.signature.original body.signature.instantiation
        body.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
      let [left,right] := List.finRange table.arms.length | throw .invalid
      let empty : Context := .mk [] [] [] [] []
      let provider : RuntimeProviderHeader.Request := (.pure 1,empty)
      let plain ← RuntimePreparedArm.prepare artifact source.catalogue table left [provider] []
      let arm ← RuntimePreparedArm.prepare artifact source.catalogue table right [provider] [[provider]]
      let rows := source.signature.sourceRows ++ relay.val.checked.summary.staticRows ++ body.summary.staticRows ++
        outer.target.sourceRows ++ inner.target.sourceRows ++ plain.rows ++ arm.rows
      let root ← Validity.checkRootFromRoots artifact #[0,1] rows (artifact.root :: plain.roots ++ arm.roots).eraseDups
      let .constructed _ _ _ markers _ ← RuntimePreparedArm.read arm root | throw .invalid
      let [entry] := markers.entries | throw .invalid
      let child ← RuntimeNativeSubject.readSubject entry.assertion
      let .closed closed ← GenericOperation.close invoked.demand.transported.subject.description | throw .invalid
      let paired ← RuntimeClosedSubject.read closed child.child.cursor
      let chain ← RuntimeForwardedSupply.read invoked.binding invoked.demand.transported.receipt paired.matched.paired
      let expected : List SupplyHopSummary := [("main","choose",0,"U",0,0,some 375),
        ("main","relay",0,"W",0,0,some (if second then 484 else 462))]
      guard (chain.hops.map supplyHopSummary == expected) .invalid
      rejectForwardedChain other chain
      return chain.hops.map supplyHopSummary
    else throw .invalid
  else throw .invalid

-- Frozen source with W written twice in one argument and an equal unused V.
private def interiorSupplySource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
meaning I:Bit=reference(keep);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {
    qmatch(s,q){0=>keep,1=>checked_op(U,I)}
}
unitary fn relay[const W:Op<Bit>,const V:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(W),Controllable(W),Applicable(V),Controllable(V) {
    choose[then_op(W,W)](s,q)
}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    relay[keep,keep](s,q)
}
"#

private def rejectEqualInteriorSlot {sources catalogue record}
    (outer : SourceRuntimeContext.NamedEvent sources "main") (choice : RuntimeFormalActual.Choice) :
    (invocation : @GenericDutyQueue.Invocation sources catalogue record) →
    GenericDutyQueue.Demand invocation → WorkM Unit
  | .root _,_ | .call (.root _) _ _,_ => throw .invalid
  | .call (.call parent outerApp outerTarget) innerApp innerTarget,demand => do
    let inner := RuntimeFormalActual.splitInvocation (.call parent outerApp outerTarget) innerApp innerTarget
      demand.transported.receipt
    let transfer := (RuntimeFormalActual.splitInvocation parent outerApp outerTarget inner.tail).transfer
    let [w,v] := outer.target.operationActuals.sourceActuals | throw .invalid
    guard (w.name == "W" && v.name == "V" && w.checked.description == v.checked.description &&
      w.checked.description == choice.description && choice.header.name == w.name && choice.position == 0 &&
      w.actual.argument.tokens.head?.map (·.span.startByte) == some 515 &&
      v.actual.argument.tokens.head?.map (·.span.startByte) == some 520) .invalid
    let wKey : Semantics.SymbolicBasis.Parameter := ⟨"main","relay",w.actual.formal.ordinal⟩
    let vKey : Semantics.SymbolicBasis.Parameter := ⟨"main","relay",v.actual.formal.ordinal⟩
    expectSupplyRefusal (RuntimeFormalActual.readSupplyAt outer outerApp.original transfer 0 wKey
      {choice with position := 1})
    expectSupplyRefusal (RuntimeFormalActual.readSupplyAt outer outerApp.original transfer 0 vKey
      {choice with position := 1,header := v.actual.formal})

private def interiorSupplyStudy : WorkM Unit := do
  let identity : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩
  let selected : Semantics.Observation.Program :=
    ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.quantumIf 0 1 2 3 [] [])],[2,3],[],.unitary⟩
  let artifact : Artifact := ⟨#[selected,identity],#[],#[("main",interiorSupplySource)],0,none⟩
  let source ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let [.named outer] := source.body.checked.events | throw .invalid
  let [duty] := source.pending.entries.filter (·.unconsumed) | throw .invalid
  let relay ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody outer)
  let [.named inner] := relay.val.checked.events | throw .invalid
  let choose ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody inner)
  if outerCaller : outer.target.callerName = "route" then
    let parent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route" "main" outer.target.callerName := by
      simpa only [outerCaller] using (RuntimeOrdinaryBody.CallPath.root source.body)
    let relayPath := RuntimeOrdinaryBody.CallPath.named outer relay.val (by with_reducible exact relay.property) parent
    if innerCaller : inner.target.callerName = outer.target.resolution.declaration.name then
      let innerParent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route"
          outer.target.resolution.moduleName inner.target.callerName := by simpa only [innerCaller] using relayPath
      let path := RuntimeOrdinaryBody.CallPath.named inner choose.val (by with_reducible exact choose.property) innerParent
      let invoked ← RuntimeDutyInvocation.readDemand duty path
      let body := choose.val.checked
      let [.selection _ parsed _ selector target scope naturals ..] := body.events | throw .invalid
      let table ← QuantumArms.readArmsWithInstantiation body.signature.original body.signature.instantiation
        body.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
      let [left,right] := List.finRange table.arms.length | throw .invalid
      let empty : Context := .mk [] [] [] [] []
      let provider : RuntimeProviderHeader.Request := (.pure 1,empty)
      let plain ← RuntimePreparedArm.prepare artifact source.catalogue table left [provider] []
      let arm ← RuntimePreparedArm.prepare artifact source.catalogue table right (List.replicate 4 provider) [[provider]]
      let rows := source.signature.sourceRows ++ relay.val.checked.summary.staticRows ++ body.summary.staticRows ++
        outer.target.sourceRows ++ inner.target.sourceRows ++ plain.rows ++ arm.rows
      let root ← Validity.checkRootFromRoots artifact #[0,1] rows (artifact.root :: plain.roots ++ arm.roots).eraseDups
      let .constructed _ _ _ markers _ ← RuntimePreparedArm.read arm root | throw .invalid
      let [entry] := markers.entries | throw .invalid
      let child ← RuntimeNativeSubject.readSubject entry.assertion
      let .closed closed ← GenericOperation.close invoked.demand.transported.subject.description | throw .invalid
      let paired ← RuntimeClosedSubject.read closed child.child.cursor
      let chain ← RuntimeForwardedSupply.read invoked.binding invoked.demand.transported.receipt paired.matched.paired
      let some view := firstInterior chain | throw .invalid
      let key : Semantics.SymbolicBasis.Parameter := ⟨"main","relay",0⟩
      guard (view.rows == [([0],0,2,"W",0,some 434,some 515),([1],1,5,"W",0,some 436,some 515)] &&
        view.expected == [([0],0,key),([1],1,key)] && view.observed == view.expected) .invalid
      let [a,b] := view.observed | throw .invalid
      expectSupplyRefusal (RuntimeInteriorSupply.checkCoverage [b,a] view.expected)
      expectSupplyRefusal (RuntimeInteriorSupply.checkCoverage [a] view.expected)
      expectSupplyRefusal (RuntimeInteriorSupply.checkCoverage [a,a] view.expected)
      let u ← RuntimeNativeSubject.readFormal child.child.cursor
      let side ← RuntimeNativeSubject.readChild u.child.cursor 0
      let w ← RuntimeNativeSubject.readFormal side.cursor
      rejectEqualInteriorSlot outer (← RuntimeFormalActual.readChoice w) invoked.invocation invoked.demand
      -- A shared zero-power subgraph still contributes both distinct edge paths.
      let frame : NaturalFrames.Frame := ⟨[]⟩
      let shared : GenericOperation.Description := ⟨frame,[.formal key,.thenOp 0 0,.power 1 ⟨⟨0,[]⟩,false⟩],
        2,List.replicate 3 frame⟩
      guard ((← GenericFormalPaths.read shared) == [([0,0],0,key),([0,1],0,key)]) .invalid
    else throw .invalid
  else throw .invalid

-- Exact first source from constructed-transfer-tail-first/main.qli. The
-- earlier full route stopped at workLimit before the arm table; the separate
-- outer-only observation reached W records 2/5 and X records 1/4. Neither first
-- diagnostic is rewritten by these continuous public-budget component checks.
private def fourLevelSupplySource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
meaning I:Bit=reference(keep);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {
    qmatch(s,q){0=>keep,1=>checked_op(U,I)}
}
unitary fn relay[const W:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(W),Controllable(W) {choose[then_op(W,W)](s,q)}
unitary fn outer[const X:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(X),Controllable(X) {relay[X](s,q)}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){outer[keep](s,q)}
"#

private inductive TailFault where
  | correct | crossedNativeLeaf | crossedAncestry | siblingRow | unshiftedRow
  | missingRow | wrongFormal | wrongHopChoice | reversedUses
  deriving BEq, Repr

private def tailTreeRows {artifact catalogue context description graph implementations references prepared root requested}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {native : OperationDescription.Description} {queue : GenericDutyQueue.Checked catalogue} {rootOwner rootName : String} :
    Nat → {task : RuntimeTransitiveInterior.Task checked native queue rootOwner rootName} →
    RuntimeTransitiveInterior.Tree task → WorkM (List TailNodeView) :=
  Nat.rec (fun {_} _ => throw .limit) (fun _ next {_} tree => do
    match tree with
    | .node step _ children =>
      let view := tailNodeView step
      exactWork (Exact.charge (16*(step.children.length+1)^2))
      let nested ← (List.finRange step.children.length).mapM fun index => next (children index)
      pure (view :: nested.flatten))

private def tailSiteSignature {artifact catalogue context description graph implementations references prepared root requested checked native}
    (site : @RuntimeTransitiveInterior.Site artifact catalogue context description graph implementations references prepared root requested checked native) :
    GenericFormalPaths.Occurrence :=
  (site.leaf.route.positions,site.leaf.finish.index,site.key)

/-- Both Trees and all replacement sites are real children of the one checked
native occurrence. Only the proposed ancestry/coverage or selected hop is wrong.
Identical Choice payloads alone do not identify a different native occurrence. -/
private def checkTailMutations {artifact catalogue context description graph implementations references prepared root requested}
    {checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested}
    {native : OperationDescription.Description} {queue : GenericDutyQueue.Checked catalogue} {rootOwner rootName : String}
    {leftTask rightTask : RuntimeTransitiveInterior.Task checked native queue rootOwner rootName}
    (fault : TailFault) (left : RuntimeTransitiveInterior.Tree leftTask) (right : RuntimeTransitiveInterior.Tree rightTask) :
    WorkM Unit := do
  match left,right with
  | .node leftStep _ _,.node rightStep _ _ =>
    let [li] := List.finRange leftStep.children.length | throw .invalid
    let [ri] := List.finRange rightStep.children.length | throw .invalid
    let leftX := leftStep.children[li]
    let rightX := rightStep.children[ri]
    let actualLeft := tailSiteSignature leftX.site
    let actualRight := tailSiteSignature rightX.site
    guard ([actualLeft] == leftStep.focus.expectedAt && [actualRight] == rightStep.focus.expectedAt &&
      leftX.site.ancestors == [0] && rightX.site.ancestors == [1] &&
      leftX.site.leaf.finish.occurrence.cursor.binding.index.val == 1 &&
      rightX.site.leaf.finish.occurrence.cursor.binding.index.val == 4 &&
      leftX.site.key == rightX.site.key && leftX.site.leaf.choice.position == 0 &&
      rightX.site.leaf.choice.position == 0 &&
      leftX.site.leaf.choice.description == rightX.site.leaf.choice.description) .invalid
    match fault with
    | .correct | .reversedUses => pure ()
    | .crossedNativeLeaf =>
      -- This replacement carries the other real X row AND its native cursor.
      expectSupplyRefusal (RuntimeTransitiveInterior.readFocus {rightX.site with ancestors := leftX.site.ancestors})
    | .crossedAncestry =>
      expectSupplyRefusal (RuntimeTransitiveInterior.readFocus {leftX.site with ancestors := rightX.site.ancestors})
    | .siblingRow =>
      expectSupplyRefusal (RuntimeInteriorSupply.checkCoverage [actualRight] leftStep.focus.expectedAt)
    | .unshiftedRow =>
      -- The right whole-result X is 1; its original local closure index was 0.
      expectSupplyRefusal (RuntimeInteriorSupply.checkCoverage [actualRight] rightStep.focus.expected)
    | .missingRow =>
      expectSupplyRefusal (RuntimeInteriorSupply.checkCoverage [] rightStep.focus.expectedAt)
    | .wrongFormal =>
      let (positions,index,key) := actualRight
      expectSupplyRefusal (RuntimeInteriorSupply.checkCoverage
        [(positions,index,{key with declarationName := "relay"})] rightStep.focus.expectedAt)
    | .wrongHopChoice =>
      let site := leftX.site
      expectSupplyRefusal (RuntimeFormalActual.readSupplyAt site.event site.app site.transfer
        site.leaf.finish.index site.key leftTask.site.leaf.choice)

private def checkFourLevelAtCaller {artifact catalogue context description graph implementations references prepared root requested checked
    native index cursor terminal caller original event app transfer paired queue rootOwner rootName owner name path record invocation result}
    (hop : @RuntimeForwardedSupply.Selected artifact catalogue context description graph implementations references prepared root requested checked
      native index cursor terminal caller original event app transfer paired)
    (prior : @RuntimeDutyInvocation.Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : GenericDutyQueue.Transport invocation.applications.reverse transfer.result.subject result)
    (fault : TailFault) : RuntimeForwardedSupply.AtCaller hop prior remaining → WorkM (List (List TailNodeView)) := by
  cases prior with
  | root => exact fun impossible => nomatch impossible
  | named => exact fun value => do
    let immediate := value.1.val
    guard (immediate.entries.map (fun entry =>
      (entry.leaf.route.positions,entry.leaf.finish.index,entry.leaf.finish.occurrence.cursor.binding.index.val,
        entry.use.tokens.head?.map (·.span.startByte),entry.leaf.supply.source.actual.argument.tokens.head?.map (·.span.startByte))) ==
      [([0],0,2,some 383,some 515),([1],1,5,some 385,some 515)]) .invalid
    let [li,ri] := List.finRange immediate.entries.length | throw .invalid
    let left := value.2.val li
    let right := value.2.val ri
    let leftRows ← tailTreeRows 4 left
    let rightRows ← tailTreeRows 4 right
    let [leftW,leftX] := leftRows | throw .invalid
    let [rightW,rightX] := rightRows | throw .invalid
    guard ([tailBasic leftW,tailBasic leftX,tailBasic rightW,tailBasic rightX] ==
      [([0],"relay","W",0,0,0,2,1,some 515,false,1,1),
       ([0],"outer","X",0,0,0,1,0,some 587,true,0,1),
       ([1],"relay","W",1,1,1,5,4,some 515,false,1,1),
       ([1],"outer","X",1,1,1,4,3,some 587,true,0,1)]) .invalid
    -- Binary assembly keeps each entire supplier block. A zero row offset
    -- on the right would lose the preceding sibling's original origins.
    guard (leftW.rowOffset == 0 && leftX.rowOffset == 0 &&
      leftW.localSuppliers > 0 && leftX.localSuppliers > 0 &&
      rightW.rowOffset == leftW.localSuppliers && rightX.rowOffset == leftX.localSuppliers) .invalid
    checkTailMutations fault left right
    if fault == .reversedUses then
      let [first,last] := immediate.entries.map RuntimeInteriorSupply.Entry.signature | throw .invalid
      expectSupplyRefusal (RuntimeInteriorSupply.checkCoverage [last,first] immediate.expected)
    return [leftRows,rightRows]

private def checkFourLevelChain {artifact catalogue context description graph implementations references prepared root requested checked
    queue rootOwner rootName owner name path record invocation original result native index cursor terminal}
    {binding : @RuntimeDutyInvocation.Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation}
    {transport : GenericDutyQueue.Transport invocation.applications.reverse original result}
    {paired : @RuntimeClosedSubject.Paired artifact catalogue context description graph implementations references prepared root requested
      checked native index cursor terminal}
    (fault : TailFault) (chain : RuntimeForwardedSupply.Chain binding transport paired) :
    WorkM (List (List TailNodeView)) := do
  match chain with
  | .direct .. => throw .invalid
  | .formal hop inside _ =>
    match inside.val with
    | .noInterior _ => throw .invalid
    | .located _ value _ => checkFourLevelAtCaller hop _ _ fault value

private def fourLevelSupplyStudy (fault : TailFault) : WorkM (List (List TailNodeView)) := do
  let identity : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩
  let selected : Semantics.Observation.Program :=
    ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.quantumIf 0 1 2 3 [] [])],[2,3],[],.unitary⟩
  let artifact : Artifact := ⟨#[selected,identity],#[],#[("main",fourLevelSupplySource)],0,none⟩
  let source ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let [.named outer] := source.body.checked.events | throw .invalid
  let [duty] := source.pending.entries.filter (·.unconsumed) | throw .invalid
  let outside ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody outer)
  let [.named middle] := outside.val.checked.events | throw .invalid
  let relay ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody middle)
  let [.named inner] := relay.val.checked.events | throw .invalid
  let choose ← NaturalAffine.witness (SourceRuntimeTrace.readNamedBody inner)
  if outerCaller : outer.target.callerName = "route" then
    let parent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route" "main" outer.target.callerName := by
      simpa only [outerCaller] using (RuntimeOrdinaryBody.CallPath.root source.body)
    let outerPath := RuntimeOrdinaryBody.CallPath.named outer outside.val (by with_reducible exact outside.property) parent
    if middleCaller : middle.target.callerName = outer.target.resolution.declaration.name then
      let middleParent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route"
          outer.target.resolution.moduleName middle.target.callerName := by simpa only [middleCaller] using outerPath
      let relayPath := RuntimeOrdinaryBody.CallPath.named middle relay.val (by with_reducible exact relay.property) middleParent
      if innerCaller : inner.target.callerName = middle.target.resolution.declaration.name then
        let innerParent : RuntimeOrdinaryBody.CallPath artifact.sources "main" "route"
            middle.target.resolution.moduleName inner.target.callerName := by simpa only [innerCaller] using relayPath
        let path := RuntimeOrdinaryBody.CallPath.named inner choose.val (by with_reducible exact choose.property) innerParent
        let invoked ← RuntimeDutyInvocation.readDemand duty path
        let body := choose.val.checked
        let [.selection _ parsed _ selector target scope naturals ..] := body.events | throw .invalid
        let table ← QuantumArms.readArmsWithInstantiation body.signature.original body.signature.instantiation
          body.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
        let [left,right] := List.finRange table.arms.length | throw .invalid
        let empty : Context := .mk [] [] [] [] []
        let provider : RuntimeProviderHeader.Request := (.pure 1,empty)
        let plain ← RuntimePreparedArm.prepare artifact source.catalogue table left [provider] []
        let arm ← RuntimePreparedArm.prepare artifact source.catalogue table right (List.replicate 2 provider) [[provider]]
        let rows := source.signature.sourceRows ++ outside.val.checked.summary.staticRows ++ relay.val.checked.summary.staticRows ++
          body.summary.staticRows ++ outer.target.sourceRows ++ middle.target.sourceRows ++ inner.target.sourceRows ++ plain.rows ++ arm.rows
        let root ← Validity.checkRootFromRoots artifact #[0,1] rows (artifact.root :: plain.roots ++ arm.roots).eraseDups
        let .constructed _ _ _ markers _ ← RuntimePreparedArm.read arm root | throw .invalid
        let [entry] := markers.entries | throw .invalid
        let child ← RuntimeNativeSubject.readSubject entry.assertion
        let .closed closed ← GenericOperation.close invoked.demand.transported.subject.description | throw .invalid
        let paired ← RuntimeClosedSubject.read closed child.child.cursor
        let chain ← RuntimeForwardedSupply.read invoked.binding invoked.demand.transported.receipt paired.matched.paired
        guard (chain.hops.map supplyHopSummary == [("main","choose",0,"U",0,0,some 375)]) .invalid
        checkFourLevelChain fault chain
      else throw .invalid
    else throw .invalid
  else throw .invalid

private inductive AppliedFault where
  | correct | staleProviderOffset | wrongInnerMeaning | wrongOuterMeaning | nested
  deriving BEq, Repr

-- Capture the native report for the two small sources preserved before
-- the applied-provider check. Keeping the same phase on both providers makes
-- original source locations and separate Meaning reference groups observable.
private def appliedSource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
unitary fn stamp[const n:Nat](q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Sign:Bit=reference(sign);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {qmatch(s,q){0=>keep,1=>checked_op(U,Sign)}}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){choose[stamp[7]](s,q)}
"#

private def nestedSource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Sign:Bit=reference(sign);
meaning Outer:Bit=reference(sign);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {qmatch(s,q){0=>keep,1=>checked_op(U,Outer)}}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){choose[checked_op(sign,Sign)](s,q)}
"#

private def slottedSource : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Sign:Bit=reference(sign);
meaning Outer:Bit=reference(sign);
unitary fn choose[const V:Op<Bit>,const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(V),Controllable(V),Applicable(U),Controllable(U) {qmatch(s,q){0=>keep,1=>checked_op(U,Outer)}}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){choose[keep,checked_op(sign,Sign)](s,q)}
"#

private inductive SlotFault where
  | correct | swappedActuals | missingProvider | changedUnusedProvider
  deriving BEq, Repr

private def writtenSource : AppliedFault → String
  | .correct | .staleProviderOffset => appliedSource
  | .nested => nestedSource
  | .wrongInnerMeaning => nestedSource.replace "meaning Sign:Bit=reference(sign);" "meaning Sign:Bit=reference(keep);"
  | .wrongOuterMeaning => nestedSource.replace "meaning Outer:Bit=reference(sign);" "meaning Outer:Bit=reference(keep);"

private def refused {α : Type} (expected : Finite.Error) (action : WorkM α) : WorkM Unit := fun work =>
  match action.run work with
  | (.error actual,left) => if actual == expected then (.ok (),left) else (.error actual,left)
  | (.ok _,left) => (.error .invalid,left)

private def crossedMeaning {artifact catalogue context description graph origin implementations references root requested owner name}
    (pending : @SourcePendingMeaning.Prepared artifact.sources catalogue) (inner : Fin pending.entries.length)
    (site : @RuntimeGraphOperation.Site artifact.sources owner name context description graph origin)
    (prepared : RuntimePreparedOperation.GraphPrepared artifact catalogue graph implementations references)
    (checked : RuntimeOperationTree.Checked prepared root requested)
    (source : RuntimeSourceOperationMarkers.OriginChecked origin prepared checked) (index : Nat) :
    WorkM Unit := by
  cases site with
  | unlocated | application | supplying => exact throw Finite.Error.invalid
  | arm => exact do
    let some entry := source.entries[index]? | throw Finite.Error.invalid
    let outerMarker := source.markers[entry.index]
    let .demand instanceAt innerDuty := pending.entries[inner].subject | throw Finite.Error.invalid
    refused .invalid (RuntimeWrittenDuty.selectEntry pending instanceAt.id outerMarker)
    refused .request (RuntimeWrittenDuty.readWritten innerDuty.source.original.origin.state.name outerMarker innerDuty.source.original)
    let operand ← RuntimeNativeSubject.readSubject entry.assertion
    let forwarded ← RuntimeNativeSubject.readFormal operand.child.cursor
    let innerCursor := forwarded.child.cursor
    refused .request (RuntimeSourceOperationMarkers.readBoundAssertion checked outerMarker innerCursor.tree innerCursor.binding)
    refused .request (RuntimeOriginalMeaning.read entry.assertion innerDuty.source.original)

-- Each position has its own source evidence. Withholding either candidate
-- or duplicating it leaves precisely that original queue position unproved.
private def nestedOriginTag {artifact owner name arguments request prepared order runtime}
    {body : @RuntimeBodyOperations.Traversed artifact owner name arguments request prepared order runtime}
    {link q} : RuntimeArmDutyCoverage.Origin body link q → Nat
  | .direct _ => 0
  | .enclosing _ => 1
  | .supplying _ _ => 2

private def checkNestedOriginals {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (expected : List Nat := [6,12]) : WorkM Unit := do
  let report := body.coverage
  let required := (List.finRange prepared.source.pending.entries.length).filter (fun i =>
    prepared.source.pending.entries[i].unconsumed)
  let [inner,outer] := required | throw Finite.Error.invalid
  guard ([inner.val,outer.val] == expected) .invalid
  let observed := report.consumed.map fun item => item.1.val
  guard (observed == expected && report.residual.isEmpty) .invalid
  let [supplying,enclosing] := report.candidates | throw .invalid
  guard (nestedOriginTag supplying.origin == 0 && supplying.queueIndex == inner &&
    nestedOriginTag enclosing.origin == 1 && enclosing.queueIndex == outer &&
    supplying.link.queueIndex == inner && enclosing.link.queueIndex == outer) .invalid
  let supply := body.checked.receipts[supplying.link.receiptIndex]
  guard supply.request.origin.isSupplying .invalid
  let receipt := body.checked.receipts[enclosing.link.receiptIndex]
  crossedMeaning prepared.source.pending inner receipt.location.site receipt.prepared receipt.evidence.checked
    receipt.evidence.source enclosing.link.markerIndex
  let status := fun (candidates : List (RuntimeArmDutyCoverage.Candidate body.toTraversed)) =>
    (RuntimeArmDutyCoverage.covered candidates inner,RuntimeArmDutyCoverage.covered candidates outer)
  guard ([status [],status [enclosing],status [supplying],status [enclosing,supplying],
      status [enclosing,supplying,supplying],status [enclosing,enclosing,supplying]] ==
    [(false,false),(false,true),(true,false),(true,true),(false,true),(true,false)]) .invalid

private abbrev AppliedCoverage := List Nat × List Nat × List (Nat × Nat)

private def readAppliedFixture (source name : String) (callOffset : Nat) (fault : AppliedFault)
    (slots : Bool := false) (slotFault : SlotFault := .correct) :
    WorkM (AppliedCoverage × Option (AppliedOffer #[("main",source)])) := do
  let applied := fault == .correct || fault == .staleProviderOffset
  let port := fun (token wire : Nat) => (⟨token,[wire],1⟩ : Semantics.Raw.Port)
  let owner := fun (token wire : Nat) => (⟨port token wire,[.bit]⟩ : Semantics.CarrierInterface.Owner)
  let one := fun (phase : Bool) => (⟨[port 0 0],[],if phase then [.pure (.gate .z 0 1)] else [],[if phase then 1 else 0],[],.unitary⟩ :
    Semantics.Observation.Program)
  let selection := fun (phase : Bool) => (⟨[port 0 0,port 1 1],[],[.pure (.quantumIf 0 1 2 3 [] (if phase then [.gate .z 0] else []))],
    [2,3],[],.unitary⟩ : Semantics.Observation.Program)
  let artifact : Artifact := ⟨#[selection true,one false,selection false,one true,selection true,one true],
    #[],#[("main",source)],0,none⟩
  let interface : Semantics.CarrierInterface.Interface := ⟨[owner 0 0,owner 1 1],[owner 2 0,owner 3 1],.unitary⟩
  let t := Semantics.RuntimeType.owner [.bit]
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main",name,[t,t],[[.quantum (owner 0 0)],[.quantum (owner 1 1)]],[[]],
      Semantics.RuntimeType.tuple 2 [t,t],[.tuple 2,.quantum (owner 2 0),.quantum (owner 3 1)],.unitary,{}⟩
  let empty : Context := .mk [] [] [] [] []
  let phaseCtx := fun offset => RuntimeContextRequest.Context.mk [⟨offset,0,1⟩] [] [] [] []
  let implementation : RuntimeProviderHeader.Request := (.pure 3,phaseCtx
    (if fault == .staleProviderOffset then 159 else if applied then 158 else 95))
  let reference : RuntimeProviderHeader.Request := (.pure 5,phaseCtx 95)
  let inner := if fault == .wrongInnerMeaning then (.pure 1,empty) else reference
  let outer := if fault == .wrongOuterMeaning then (.pure 1,empty) else reference
  let s : SourceSequence.Position := ⟨if applied then 322 else if slots then 340 else 294,0,1⟩
  let c : SourceSequence.Position := ⟨callOffset,0,1⟩
  let site : RuntimeContextRequest.Site := ⟨interface,interface,s,[⟨1,2⟩,⟨3,4⟩]⟩
  let keep : RuntimeProviderHeader.Request := (.pure 1,empty)
  let bodies := if slots then match slotFault with
    | .correct => [keep,implementation,keep,keep,implementation]
    | .swappedActuals => [implementation,keep,keep,keep,implementation]
    | .missingProvider => [keep,implementation,keep,implementation]
    | .changedUnusedProvider => [(.pure 3,empty),implementation,keep,keep,implementation]
    else [implementation,keep,implementation]
  let child : Context := .withReferences [s] [site] [] [] bodies
    (if slots then [[],[[inner]],[],[[inner],[outer]]]
     else if applied then [[],[],[[reference]]] else [[[inner]],[],[[inner],[outer]]]) []
  let context : Context := .mk [c] [] [(c,child)] [] []
  let prepared ← RuntimeBodyOperations.prepare artifact "main" name {} context
  let checked ← RuntimeBodyOperations.read prepared #[0,1,2,3,4,5] runtime
  if fault == .nested then checkNestedOriginals checked (if slots then [8,16] else [6,12])
  let offer := match checked.writtenLinks with
    | [link] => (summarizeLink checked.checked link).bind (·.2)
    | _ => none
  return ((checked.coverage.consumed.map (·.1.val),checked.coverage.residual.map Fin.val,
    checked.writtenLinks.map fun link => (link.queueIndex.val,link.binding.instanceBinding.demand.source.original.origin.offset)),offer)

private def compareAppliedRoots : WorkM (Bool × List (String × Nat) × List (String × Nat) × List Bool) := do
  let source := appliedSource ++
    "pub unitary fn other(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){choose[stamp[8]](s,q)}\n"
  let (_,some seven) ← readAppliedFixture source "route" 423 .correct | throw .invalid
  let (_,some eight) ← readAppliedFixture source "other" 503 .correct | throw .invalid
  let compare := fun (original actual : AppliedOffer #[("main",source)]) => do
    try
      original.checkIdentity actual.native
      pure true
    catch error =>
      if error == .request then pure false else throw error
  let decisions ← [(seven,seven),(seven,eight),(eight,seven),(eight,eight)].mapM
    fun (original,actual) => compare original actual
  return (seven.action == eight.action,seven.native.signature.staticArguments.naturals,
    eight.native.signature.staticArguments.naturals,decisions)

-- Start from the genuine retained root call, then corrupt only its untrusted
-- Op-slot metadata. Reversed, missing and duplicate keys cannot authenticate a
-- call even when every original source token remains unchanged.
private def slottedKeys : WorkM Unit := do
  let artifact : Artifact := ⟨#[],#[],#[("main",slottedSource)],0,none⟩
  let source ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let entry ← GenericCatalogue.lookup source.catalogue.toRuntimeChecked source.signature.original
  let applications := (GenericCatalogue.bodyActivities entry.body).filterMap fun activity =>
    match activity with | .application app => some app | _ => none
  -- The original keep/sign provider occurrences remain separate applications.
  -- Select this fixture's containing call by its actual frozen source span.
  let [app] := applications.filter (fun app => app.tokens.head?.map (·.span.startByte) == some 442) | throw .invalid
  guard (app.owner == "main" && app.name == "choose") .invalid
  let [first,second] := app.operationActuals | throw .invalid
  guard (app.operationActuals.map (·.original.ordinal) == [0,1]) .invalid
  let _ ← SourceDutyProviderBare.readApplications source.catalogue [app]
  for actuals in [[second,first],[second],[first,first]] do
    refused .request (SourceDutyProviderBare.readApplications source.catalogue [{app with operationActuals := actuals}])

private def slottedControls : IO Unit := do
  for fault in [AppliedFault.nested,.wrongInnerMeaning,.wrongOuterMeaning] do
    let source := match fault with
      | .wrongInnerMeaning => slottedSource.replace "meaning Sign:Bit=reference(sign);" "meaning Sign:Bit=reference(keep);"
      | .wrongOuterMeaning => slottedSource.replace "meaning Outer:Bit=reference(sign);" "meaning Outer:Bit=reference(keep);"
      | _ => slottedSource
    let (observed,left) := (readAppliedFixture source "route" 442 fault true).run WorkProfile.qmatch.limit
    let result := observed.map Prod.fst
    let expected : Except Finite.Error AppliedCoverage :=
      if fault == .nested then .ok ([8,16],[],[(8,454),(16,363)]) else .error .equation
    let matched := match result,expected with
      | .ok actual,.ok wanted => actual == wanted
      | .error actual,.error wanted => actual == wanted
      | _,_ => false
    unless matched do
      throw (IO.userError s!"original Op slots {repr fault}: expected {repr expected}, observed {repr result}")
    IO.println s!"original Op slots {repr fault}: {repr result}; work={WorkProfile.qmatch.limit-left}"
  for fault in [SlotFault.swappedActuals,.missingProvider,.changedUnusedProvider] do
    let observed := ((readAppliedFixture slottedSource "route" 442 .nested true fault).run WorkProfile.qmatch.limit).1
    match observed with
    | .error .request => pure ()
    | _ => throw (IO.userError s!"original Op slot corruption {repr fault}: observed {repr (observed.map Prod.fst)}")
  match slottedKeys.run WorkProfile.qmatch.limit |>.1 with
  | .ok () => pure ()
  | .error error => throw (IO.userError s!"original Op slot key identity: {repr error}")
  IO.println "passed unused provider occurrence, wrong Meaning, crossed/missing body and exact original Op key controls"

private def appliedControls : IO Unit := do
  slottedControls
  for fault in [AppliedFault.correct,.nested,.staleProviderOffset,.wrongInnerMeaning,.wrongOuterMeaning] do
    let offset := if fault == .correct || fault == .staleProviderOffset then 423 else 396
    let observed := ((readAppliedFixture (writtenSource fault) "route" offset fault).run WorkProfile.qmatch.limit).1.map Prod.fst
    let expected : Except Finite.Error (List Nat × List Nat × List (Nat × Nat)) := match fault with
      | .correct => .ok ([11],[],[(11,345)])
      | .nested => .ok ([6,12],[],[(6,403),(12,317)])
      | .staleProviderOffset => .error .request
      | .wrongInnerMeaning | .wrongOuterMeaning => .error .equation
    let matched := match observed,expected with
      | .ok actual,.ok wanted => actual == wanted
      | .error actual,.error wanted => actual == wanted
      | _,_ => false
    unless matched do
      throw (IO.userError s!"applied-provider {repr fault}: expected {repr expected}, observed {repr observed}")
  let (compared,left) := compareAppliedRoots.run WorkProfile.qmatch.limit
  match compared with
  | .ok (true,[("n",7)],[("n",8)],[true,false,false,true]) =>
    IO.println s!"passed both actual source/provider matches and both crossed unused Nat refusals; work={WorkProfile.qmatch.limit-left}"
  | _ => throw (IO.userError s!"crossed unused applied-provider Nat: {repr compared}")

/-- Run the common source-origin association under native execution as well
as the kernel guards. Both original arms are covered; the one original Meaning
duty remains pending. Wrong phase and source order retain exact refusals. -/
def nativeSourceMarkerControls : IO Unit := do
  appliedControls
  for fault in [TailFault.correct,.crossedNativeLeaf,.crossedAncestry,.siblingRow,.unshiftedRow,
      .missingRow,.wrongFormal,.wrongHopChoice,.reversedUses] do
    match (fourLevelSupplyStudy fault).run WorkProfile.qmatch.limit with
    | (.ok rows,left) =>
      if fault == .correct then
        IO.println s!"four-level original supplier trees={repr rows}; work={WorkProfile.qmatch.limit-left}"
    | (.error error,_) =>
      throw (IO.userError ("four-level original supplier control " ++ reprStr fault ++ ": " ++ reprStr error))
  match (interiorSupplyStudy.run WorkProfile.qmatch.limit).1 with
  | .ok () => pure ()
  | .error error => throw (IO.userError ("constructed argument occurrence controls: " ++ reprStr error))
  for second in [false,true] do
    match (forwardedSupplyStudy second).run WorkProfile.qmatch.limit with
    | (.ok _,_) => pure ()
    | (.error error,_) => throw (IO.userError ("forwarded supplier occurrence controls: " ++ reprStr error))
  match (mixedSupplyStudy.run WorkProfile.qmatch.limit).1 with
  | .ok () => pure ()
  | .error error => throw (IO.userError ("mixed formal supply controls: " ++ reprStr error))
  for interior in [false,true] do
    match ((checkForwardedCommonBody interior).run WorkProfile.qmatch.limit).1 with
    | .ok () => pure ()
    | .error error => throw (IO.userError ("common forwarded source arguments: " ++ reprStr error))
  match (checkForwardedCommonBody true true).run WorkProfile.qmatch.limit |>.1 with
  | .ok () => pure ()
  | .error error => throw (IO.userError ("unreached equal-valued Meaning duty: " ++ reprStr error))
  match (checkOrderedOriginalCalls.run WorkProfile.qmatch.limit).1 with
  | .ok () => pure ()
  | .error error => throw (IO.userError ("ordered original call frames: " ++ reprStr error))
  checkRootCoefficients
  checkRepeatedChoose
  for composed in [false,true] do
    unless (observingStudy composed .correct).toOption == some (observingExpected composed) do
      throw (IO.userError "native common arm/source association or complete history changed")
    match observingStudy composed .wrongSelectedPhase with
    | .error .equation => pure ()
    | _ => throw (IO.userError "native common selected phase refusal changed")
    match observingStudy composed .contextOrder with
    | .error .request => pure ()
    | _ => throw (IO.userError "native common source order refusal changed")
  match (checkFourLevelCommonBody.run WorkProfile.qmatch.limit).1 with
  | .ok () => pure ()
  | .error error => throw (IO.userError ("four-level signed common body: " ++ reprStr error))
  IO.println "passed ordered call ports and primitive origins, written Meaning coverage, missing equal-valued occurrence, repeated-callee pairing, and observing phase/order controls"

private def generalHistory {sources owner name signature dependencies program body prepared runtime inputs initial ssa bindings assignments}
    (rows : @RuntimeOrdinaryHistories.Rows sources owner name signature dependencies program body prepared runtime inputs
      initial ssa bindings assignments) : Option Raw.StreamedInstrument.History :=
  match rows with
  | .cons row .nil => match row.histories with
    | [history] => if history.hidden.isEmpty && history.values.isEmpty then some history else none
    | _ => none
  | _ => none

private def generalIdentity {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) : WorkM Unit := do
  guard (body.checked.native.whole.prepared.inputBits == 2 &&
    body.checked.native.whole.state.quantum.frame.length == 2 &&
    body.root.program.classicalInputs.isEmpty && body.root.program.classicalOutputs.isEmpty) .request
  let some history := generalHistory body.checked.ordinary.rows | throw .request
  for row in List.range 4 do
    for col in List.range 4 do
      let actual ← history.operator row col
      let expected : Semantics.Exact.Scalar := if row == col then .one else .zero
      guard (actual == expected) .equation

private def generalField (payload : Json) (name : String) : IO ByteArray := do
  let .ok row := payload.getObjVal? name | throw (IO.userError "missing original general Meaning payload")
  let .ok text := row.getObjValAs? String "text" | throw (IO.userError "missing original general Meaning bytes")
  return text.toUTF8

private def generalMeaningCase (name : String) (payload : Json) : IO Unit := do
  let ir ← generalField payload "artifact"
  let req ← generalField payload "request"
  -- Maintainer-authorized development exception for this one general example,
  -- tracked by #472. Production WorkProfile and the whole-body entry guard
  -- remain unchanged. These separately budgeted actions issue no handle and
  -- are never presented as one successful bounded production computation.
  let developmentAllowance : Nat := 18446744073709551615
  let (.ok (artifact,order),afterIR) := (Protocol.Qirf.readAll ir).run developmentAllowance
    | throw (IO.userError "general Meaning IR decode failed")
  let (.ok request,afterRequest) := (Protocol.QmatchV5.readRequest req).run afterIR
    | throw (IO.userError "general Meaning request decode failed")
  let (prepared,afterPreparation) := (RuntimeBodyOperations.prepare artifact request.source.moduleName
    request.source.functionName request.source.arguments request.context).run afterRequest
  match prepared with
  | .error error =>
    unless (name == "swapped-original-slots" || name == "changed-sibling-provider") && error == .request do
      throw (IO.userError s!"general Meaning unexpected preparation refusal {name}: {repr error}")
  | .ok prepared =>
    let (result,afterBody) := (RuntimeBodyOperations.read prepared order request.combinedRuntime).run WorkProfile.qmatch.limit
    match result with
    | .error error =>
      unless (name == "wrong-inner-meaning" || name == "wrong-outer-meaning") && error == .equation do
        throw (IO.userError s!"general Meaning unexpected body refusal {name}: {repr error}")
    | .ok body =>
      unless name == "positive" && body.coverage.consumed.map (·.1.val) == [15,27] && body.coverage.residual.isEmpty do
        throw (IO.userError s!"general Meaning wrong original credits {name}")
      let (.ok (),afterOracle) := (generalIdentity body).run developmentAllowance
        | throw (IO.userError "general Meaning independent exact I4 failed")
      IO.println s!"general Meaning original credits [15,27], no residual, exact I4; development-only aggregate work={developmentAllowance-afterPreparation+WorkProfile.qmatch.limit-afterBody+developmentAllowance-afterOracle}; production profile={WorkProfile.qmatch.limit}"

def generalMeaningControls : IO Unit := do
  let .ok record := Json.parse (← IO.FS.readFile
      "tests/fixtures/authoring_sessions/qmatch-source-coupling-v030/general-meaning-first.json")
    | throw (IO.userError "general Meaning fixture parse failed")
  let .ok controls := record.getObjVal? "controls" | throw (IO.userError "general Meaning controls missing")
  for name in ["positive","wrong-inner-meaning","wrong-outer-meaning","swapped-original-slots","changed-sibling-provider"] do
    let .ok payload := controls.getObjVal? name | throw (IO.userError "general Meaning case missing")
    generalMeaningCase name payload
  IO.println "passed general constructed Meaning credits, both exact equation refusals and both original-source substitutions"

end QleisliKernel.Tests.RuntimeNamedSelectionBoundary

def main (args : List String) : IO Unit := do
  let [shapePath,executionPath] := args | throw (IO.userError "expected qmatch shape and execution fixtures")
  shapes shapePath
  execution executionPath
  let parent := (System.FilePath.mk executionPath).parent.getD (System.FilePath.mk ".")
  execution (parent / "nominal-execution-cases.json") true
  execution (parent / "body-execution-cases.json") true 5 9
  frames (parent / "frame-execution-cases.json")
  QleisliKernel.Tests.RuntimeNamedSelectionBoundary.nativeSourceMarkerControls
  QleisliKernel.Tests.RuntimeNamedSelectionBoundary.generalMeaningControls

namespace QleisliKernel.Tests.RuntimeNamedSelectionBoundary
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

-- These exact first-payload bytes were observed through the real common reader
-- before this regression was authored. No join, split or quantumIf is present:
-- only the target is renamed by an actual empty applyUnitary. Both original
-- source arms, their two provider slots and both reference groups remain intact.
private def shapeFreeArtifactBytes : ByteArray := ("{\n  \"format\": \"qleisli.finite-ir\",\n  \"profile\": \"finite-meaning-v1\",\n  \"version\": 2,\n  \"programs\": [\n    {\n      \"quantum_inputs\": [\n        {\n          \"token\": 0,\n          \"wires\": [\n            0\n          ],\n          \"shape\": {\n            \"bits\": 1\n          }\n        },\n        {\n          \"token\": 1,\n          \"wires\": [\n            1\n          ],\n          \"shape\": {\n            \"bits\": 1\n          }\n        }\n      ],\n      \"classical_inputs\": [],\n      \"operations\": [\n        {\n          \"tag\": \"apply_unitary\",\n          \"input\": 1,\n          \"output\": 2,\n          \"steps\": []\n        }\n      ],\n      \"quantum_outputs\": [\n        0,\n        2\n      ],\n      \"classical_outputs\": [],\n      \"declared_effect\": \"unitary\"\n    },\n    {\n      \"quantum_inputs\": [\n        {\n          \"token\": 0,\n          \"wires\": [\n            0\n          ],\n          \"shape\": {\n            \"bits\": 1\n          }\n        }\n      ],\n      \"classical_inputs\": [],\n      \"operations\": [],\n      \"quantum_outputs\": [\n        0\n      ],\n      \"classical_outputs\": [],\n      \"declared_effect\": \"unitary\"\n    },\n    {\n      \"quantum_inputs\": [\n        {\n          \"token\": 0,\n          \"wires\": [\n            0\n          ],\n          \"shape\": {\n            \"bits\": 1\n          }\n        },\n        {\n          \"token\": 1,\n          \"wires\": [\n            1\n          ],\n          \"shape\": {\n            \"bits\": 1\n          }\n        }\n      ],\n      \"classical_inputs\": [],\n      \"operations\": [],\n      \"quantum_outputs\": [\n        0,\n        1\n      ],\n      \"classical_outputs\": [],\n      \"declared_effect\": \"unitary\"\n    }\n  ],\n  \"evidence\": [],\n  \"sources\": [\n    {\n      \"path\": \"main\",\n      \"text\": \"#![no_implicit_prelude]\\nunitary fn keep(q:Q<Bit>)->Q<Bit>{q}\\npub unitary fn main(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){\\n    qmatch(s,q){0=>keep,1=>keep}\\n}\\n\"\n    }\n  ],\n  \"root\": 0,\n  \"root_interface\": null\n}\n").toUTF8
private def shapeFreeRequestBytes : ByteArray := ("{\n  \"format\": \"qleisli.qmatch-request\",\n  \"profile\": \"finite-source-qmatch-context-v5\",\n  \"version\": 5,\n  \"source\": {\n    \"module\": \"main\",\n    \"function\": \"main\",\n    \"static_bases\": [],\n    \"static_naturals\": [],\n    \"static_operations\": []\n  },\n  \"runtime\": {\n    \"format\": \"qleisli.runtime-root-request\",\n    \"profile\": \"finite-runtime-root-v2\",\n    \"version\": 2,\n    \"selection\": \"exported\",\n    \"module\": \"main\",\n    \"declaration\": \"main\",\n    \"parameters\": [\n      [\n        {\n          \"tag\": \"quantum\"\n        },\n        {\n          \"tag\": \"finite\",\n          \"atom\": {\n            \"tag\": \"bit\"\n          }\n        }\n      ],\n      [\n        {\n          \"tag\": \"quantum\"\n        },\n        {\n          \"tag\": \"finite\",\n          \"atom\": {\n            \"tag\": \"bit\"\n          }\n        }\n      ]\n    ],\n    \"input_storage\": [\n      [\n        {\n          \"tag\": \"quantum\",\n          \"owner\": {\n            \"port\": {\n              \"token\": 0,\n              \"wires\": [\n                0\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          }\n        }\n      ],\n      [\n        {\n          \"tag\": \"quantum\",\n          \"owner\": {\n            \"port\": {\n              \"token\": 1,\n              \"wires\": [\n                1\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          }\n        }\n      ]\n    ],\n    \"input_rows\": [\n      []\n    ],\n    \"result\": [\n      {\n        \"tag\": \"finite\",\n        \"atom\": {\n          \"tag\": \"pair\"\n        }\n      },\n      {\n        \"tag\": \"quantum\"\n      },\n      {\n        \"tag\": \"finite\",\n        \"atom\": {\n          \"tag\": \"bit\"\n        }\n      },\n      {\n        \"tag\": \"quantum\"\n      },\n      {\n        \"tag\": \"finite\",\n        \"atom\": {\n          \"tag\": \"bit\"\n        }\n      }\n    ],\n    \"storage\": [\n      {\n        \"tag\": \"tuple\",\n        \"arity\": 2\n      },\n      {\n        \"tag\": \"quantum\",\n        \"owner\": {\n          \"port\": {\n            \"token\": 0,\n            \"wires\": [\n              0\n            ],\n            \"bits\": 1\n          },\n          \"basis\": [\n            {\n              \"tag\": \"bit\"\n            }\n          ]\n        }\n      },\n      {\n        \"tag\": \"quantum\",\n        \"owner\": {\n          \"port\": {\n            \"token\": 2,\n            \"wires\": [\n              1\n            ],\n            \"bits\": 1\n          },\n          \"basis\": [\n            {\n              \"tag\": \"bit\"\n            }\n          ]\n        }\n      }\n    ],\n    \"public_effect\": \"unitary\",\n    \"static_bases\": [],\n    \"static_naturals\": []\n  },\n  \"positions\": [\n    {\n      \"offset\": 122,\n      \"start\": 0,\n      \"count\": 1\n    }\n  ],\n  \"sites\": [\n    {\n      \"position\": {\n        \"offset\": 122,\n        \"start\": 0,\n        \"count\": 1\n      },\n      \"attached\": {\n        \"inputs\": [\n          {\n            \"port\": {\n              \"token\": 0,\n              \"wires\": [\n                0\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          },\n          {\n            \"port\": {\n              \"token\": 1,\n              \"wires\": [\n                1\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          }\n        ],\n        \"outputs\": [\n          {\n            \"port\": {\n              \"token\": 0,\n              \"wires\": [\n                0\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          },\n          {\n            \"port\": {\n              \"token\": 2,\n              \"wires\": [\n                1\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          }\n        ],\n        \"public_effect\": \"unitary\"\n      },\n      \"required\": {\n        \"inputs\": [\n          {\n            \"port\": {\n              \"token\": 0,\n              \"wires\": [\n                0\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          },\n          {\n            \"port\": {\n              \"token\": 1,\n              \"wires\": [\n                1\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          }\n        ],\n        \"outputs\": [\n          {\n            \"port\": {\n              \"token\": 0,\n              \"wires\": [\n                0\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          },\n          {\n            \"port\": {\n              \"token\": 2,\n              \"wires\": [\n                1\n              ],\n              \"bits\": 1\n            },\n            \"basis\": [\n              {\n                \"tag\": \"bit\"\n              }\n            ]\n          }\n        ],\n        \"public_effect\": \"unitary\"\n      },\n      \"arms\": [\n        {\n          \"implementation\": 1,\n          \"controlled\": 2\n        },\n        {\n          \"implementation\": 1,\n          \"controlled\": 2\n        }\n      ]\n    }\n  ],\n  \"calls\": [],\n  \"branches\": [],\n  \"bodies\": [\n    {\n      \"subject\": {\n        \"kind\": \"pure\",\n        \"program\": 1\n      },\n      \"body\": {\n        \"positions\": [],\n        \"sites\": [],\n        \"calls\": [],\n        \"branches\": [],\n        \"bodies\": [],\n        \"references\": []\n      }\n    },\n    {\n      \"subject\": {\n        \"kind\": \"pure\",\n        \"program\": 1\n      },\n      \"body\": {\n        \"positions\": [],\n        \"sites\": [],\n        \"calls\": [],\n        \"branches\": [],\n        \"bodies\": [],\n        \"references\": []\n      }\n    }\n  ],\n  \"references\": [\n    [],\n    []\n  ]\n}\n").toUTF8

private def shapeFreeSelectionAction : WorkM (List Nat × List Nat × Nat × Nat × Nat) := do
  let (artifact,order) ← Protocol.Qirf.readAll shapeFreeArtifactBytes
  let request ← Protocol.QmatchV5.readRequest shapeFreeRequestBytes
  let prepared ← RuntimeBodyOperations.prepare artifact request.source.moduleName request.source.functionName
    request.source.arguments request.context
  let checked ← RuntimeBodyOperations.read prepared order request.runtime
  let [node] := checked.checked.result.actions | throw .request
  match node with
  | .selection frame selectorBits targetBits retained restricted _inputCode _outputCode _labels
      _expected _logical _equations codes _layouts =>
    -- Assert the exact retained Raw interval, rather than construct a node or
    -- a SelectionForm premise for one of the existing lowering shapes.
    let [.applyUnitary 1 2 []] := frame.operations | throw .request
    let literal ← RuntimeLocalEvents.readSource frame selectorBits targetBits retained restricted codes.owners
    let _ ← RuntimeSelectionWitness.read node
    pure (frame.returned.map (·.token),checked.root.program.outputs,
      (prepared.source.pending.entries.filter (·.unconsumed)).length,literal.chunks.length,frame.operations.length)
  | _ => throw .request

private def shapeFreeSelectionStudy := (shapeFreeSelectionAction.run WorkProfile.qmatch.limit).1

-- Both actual literal readers must succeed on this SAME common-read node;
-- an error in either query aborts the one continuously budgeted computation.
#guard shapeFreeSelectionStudy.toOption == some ([0,2],[0,2],0,1,1)

end QleisliKernel.Tests.RuntimeNamedSelectionBoundary
