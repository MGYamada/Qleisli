import QleisliKernel.Qirf.RuntimeNamedSelection
import Protocol.Qirf
import Protocol.QmatchV5

/-! Original named choose[then_op(sign,sign)] around its genuine joined Raw
selection. Literal plain data is retained from the real Rust artifact/request;
no source proof, accepted result or external study file is a runtime input.
Each run freshly decodes and reads all original source, the distinct header
prefix, both arms and Meaning, one graph and the complete named caller return.

The study starts once with 40M work units. The original named source, graph
and caller component used 32,608,658 units before the execution view. The
public 10M counter is tested separately on the same inputs.
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
    child.calls child.branches child.bodies child.references

private def replaceParent (request : Request) (position : Position) (child : Context) : Request :=
  {request with context := .withReferences [position] [] [(position,child)] [] [] []}

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
    (subject,RuntimeContextRequest.Context.withReferences (body.positions.map fun pos => {pos with offset := pos.offset+4})
      body.sites body.calls body.branches body.bodies body.references)
  let childPosition := {position with offset := 310}
  let child := RuntimeContextRequest.Context.withReferences [childPosition]
    (child.sites.map fun site => {site with position := childPosition}) child.calls child.branches phaseBodies child.references
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
    return (artifact,replaceParent request position (.withReferences [] child.sites child.calls child.branches child.bodies child.references))
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
      child.bodies [[],[],[[(.pure refProgram,phaseBody)]]]
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
      child.bodies [checked,keep,supplied]
    return (artifact,replaceParent request position child)
  | .extraProviderReferences =>
    let (subject,body) :: rest := child.bodies | throw "missing first provider"
    let body : Context := .withReferences body.positions body.sites body.calls body.branches body.bodies [[]]
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

private def study (fault : Fault) := (inspect artifactBytes requestBytes fault).run 40000000

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

-- Preserve the actual ordinary native-budget refusal instead of relabeling
-- the over-budget source as available. Both runs start once at exactly 10M.
#guard [Fault.none,.heldUnit].all fun fault =>
  match (inspect artifactBytes requestBytes fault).run 10000000 with
  | (.error (.arithmetic .workLimit),_) => true
  | _ => false

end QleisliKernel.Tests.RuntimeNamedSelectionBoundary
