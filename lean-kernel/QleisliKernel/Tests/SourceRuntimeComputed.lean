import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Qirf.RuntimeCertifiedComputed
import QleisliKernel.Qirf.RuntimeWorkspace
import QleisliKernel.Target.CanonicalOpenQasmWorkspace
import QleisliKernel.Target.CanonicalOpenQasmPlacement
import QleisliKernel.Tests.SourceTraceOriginals

/-! Actual original computed scope typing, owner histories and source bodies.
A successful source traversal still has an explicit protected/certified native
equation obligation; typed auxiliary return is deliberately not clean evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeComputed
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues SourceRuntimeContext

private def sources (source : String) : Sources := #[("main",source)] ++ SourceTraceOriginals.bundled
private def read (source : String) :=
  ((SourceRuntimeTrace.read (sources source) "main" "route").run 2000000000).1.toOption

private def predicate := "classical fn predicate(b:Bit)->Bit{b}"

private def cleanScope :=
  "pub unitary fn route(q:Q<Bit>)->Q<Bit>{clean(q,h){|data,scratch|(h(data),scratch)}}"
private def dirtyScope :=
  "pub unitary fn route(q:Q<Bit>,d:Q<Bit>)->(Q<Bit>,Q<Bit>){dirty(q,d,h){|data,scratch|(h(data),scratch)}}"

private def workspaceOwners (source : String) :=
  (read source).bind fun checked =>
    match checked.events with
    | [.workspace event _] =>
      some (event.fresh,event.input.ordinal,event.scratch.ordinal,
        (valueOwners checked.summary.value).map (·.ordinal),
        checked.summary.allocated.map (·.ordinal),checked.summary.consumed.map (·.ordinal))
    | _ => none

#guard workspaceOwners cleanScope == some (true,0,1,[0],[1],[1])
#guard workspaceOwners dirtyScope == some (false,0,1,[0,1],[],[])
#guard (read (dirtyScope.replace "dirty(q,d,h)" "dirty(q,q,h)")).isNone
#guard (read (cleanScope.replace "(h(data),scratch)" "h(data)")).isNone

private def readWorkspaceAction (source : String) : Finite.WorkM Nat := do
  let checked ← SourceRuntimeTrace.read #[("main","#![no_implicit_prelude]\n" ++ source)] "main" "route"
  let [.workspace event children] := checked.events | throw .request
  let original ← QleisliKernel.Qirf.RuntimeWorkspace.readOriginal event children
  return original.body.matrix.rows

private def checkWorkspaceSteps (source : String) (steps : List Semantics.Finite.Step) :
    Finite.WorkM Unit := do
  let checked ← SourceRuntimeTrace.read #[("main","#![no_implicit_prelude]\n" ++ source)] "main" "route"
  let [.workspace event children] := checked.events | throw .request
  let original ← QleisliKernel.Qirf.RuntimeWorkspace.readOriginal event children
  let _ ← QleisliKernel.Qirf.RuntimeWorkspace.checkSteps original [] steps

private def hData : Semantics.Finite.Step := QleisliKernel.Raw.gateStep .h 0
private def zScratch : Semantics.Finite.Step := QleisliKernel.Raw.gateStep .z 1

#guard ((checkWorkspaceSteps cleanScope [hData]).run 20000000).1.isOk
#guard ((checkWorkspaceSteps dirtyScope [hData]).run 20000000).1.isOk
#guard (match ((checkWorkspaceSteps cleanScope [hData,zScratch]).run 20000000).1 with
  | .error .equation => true
  | _ => false)
#guard (match ((checkWorkspaceSteps dirtyScope [hData,zScratch]).run 20000000).1 with
  | .error .equation => true
  | _ => false)

private def cleanControlled :=
  "unitary fn gate(q:Q<Bit>)->Q<Bit>{h(q)} " ++
    "pub unitary fn route(q:Q<Bit>)->Q<Bit>{clean(q,h){|data,scratch|" ++
    "let (data,scratch)=controlled(gate)(data,scratch);" ++
    "let (data,scratch)=controlled(gate)(data,scratch);(h(data),scratch)}}"

#guard ((readWorkspaceAction cleanScope).run 20000000).1.toOption == some 4
#guard ((readWorkspaceAction dirtyScope).run 20000000).1.toOption == some 4
#guard ((readWorkspaceAction cleanControlled).run 20000000).1.toOption == some 4

private def workspaceInterval (sourceText : String) (operations : List Semantics.Observation.Op)
    (fresh : Bool) (targetTest : Option (String × List Nat × Nat × Nat) := none)
    (reuseTest : Option (String × List Nat × Nat × Nat × Nat) := none)
    (placementTest : Option (String × List Nat × Option Nat) := none) :
    Finite.WorkM (List Nat × List Nat × Raw.WorkspaceResources.Counts × Nat) := do
  let source ← SourceRuntimeTrace.read #[("main","#![no_implicit_prelude]\n" ++ sourceText)] "main" "route"
  let [.workspace event children] := source.events | throw .request
  let data : Semantics.Raw.Port := ⟨10,[6],1⟩
  let scratch : Semantics.Raw.Port := ⟨11,[2],1⟩
  let spectator : Semantics.Raw.Port := ⟨12,[],0⟩
  let spectatorOwner : Semantics.SourceOwners.Owner := ⟨4,[.unit]⟩
  let scratchPorts := if fresh then [] else [scratch]
  let outputs := if fresh then [13,12] else [13,14,12]
  let program : Semantics.Observation.Program :=
    ⟨data :: scratchPorts ++ [spectator],[],operations,outputs,[],.unitary⟩
  let block ← Qirf.RuntimeInterval.prepare [] program
  let interval ← Qirf.RuntimeInterval.check block.block 0 operations.length
  let scratchBindings := if fresh then [] else [⟨event.scratch,scratch⟩]
  let bindings : Qirf.RuntimeOwnerMap.Map := ⟨event.input,data⟩ :: scratchBindings ++ [⟨spectatorOwner,spectator⟩]
  let before : Qirf.RuntimeStructuralAction.SourceState := ⟨bindings,bindings.map (·.owner),event.nextOrdinal⟩
  let original ← Qirf.RuntimeWorkspace.readOriginal event children
  let checked ← Qirf.RuntimeWorkspace.readLiteral original interval before
  let map ← Qirf.RuntimeWorkspace.readCallerMap checked #[]
  if let some (text,layout,start,count) := targetTest then
    let target ← Target.CanonicalOpenQasmResources.check text.toUTF8 4
    let _ ← Target.CanonicalOpenQasmWorkspace.checkLifetime map target layout start count
  if let some (text,frame,scratch) := placementTest then
    let target ← Target.CanonicalOpenQasmResources.check text.toUTF8 4
    let _ ← Target.CanonicalOpenQasmWorkspace.checkPlacement map target frame 0 1 scratch
  if let some (text,layout,first,second,count) := reuseTest then
    let target ← Target.CanonicalOpenQasmResources.check text.toUTF8 4
    let before ← Target.CanonicalOpenQasmWorkspace.check map target layout first count
    let after ← Target.CanonicalOpenQasmWorkspace.check map target layout second count
    if offered : event.fresh = true then
      match scratch : layout.getLast? with
      | none => throw .request
      | some wire =>
        let _ ← Target.CanonicalOpenQasmWorkspace.checkReuse target wire
          [before.cleanUse offered scratch,after.cleanUse offered scratch]
    else throw .request
  return (checked.continuation.bindings.map (·.port.token),checked.continuation.issued.map (·.ordinal),
    map.resources.counts,map.resources.expandedBodySteps)

private def cleanOps (useSteps logicalSteps : List Semantics.Finite.Step) (table : List Nat := [0,0]) :
    List Semantics.Observation.Op :=
  [.pure (.certifiedCompute 10 13 [8] table useSteps logicalSteps)]

private def dirtyOps (steps : List Semantics.Finite.Step) (data : Nat := 10) (scratch : Nat := 11) :
    List Semantics.Observation.Op :=
  [.pure (.join data scratch 15),.pure (.applyUnitary 15 16 steps),.pure (.split 16 13 14 1)]

#guard ((workspaceInterval cleanScope (cleanOps [hData] [hData]) true).run 20000000).1.toOption ==
  some ([13,12],[0,4,1],⟨2,1,1,2,1,0⟩,1)
#guard ((workspaceInterval dirtyScope (dirtyOps [hData]) false).run 20000000).1.toOption ==
  some ([13,14,12],[0,1,4],⟨2,0,0,0,1,0⟩,1)
#guard ((workspaceInterval cleanScope (cleanOps [hData,zScratch] [hData]) true).run 20000000).1.toOption.isNone
#guard ((workspaceInterval cleanScope (cleanOps [hData] [hData] [1,1]) true).run 20000000).1.toOption.isNone
#guard ((workspaceInterval dirtyScope (dirtyOps [hData,zScratch]) false).run 20000000).1.toOption.isNone
#guard ((workspaceInterval dirtyScope (dirtyOps [hData] 11 10) false).run 20000000).1.toOption.isNone

private def targetWorkspace (width : Nat) (gates : String) : String :=
  s!"OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[{width}] q;\nreset q;\n{gates}"

private def targetWorkspaceAccepted (fresh : Bool) (text : String) (layout : List Nat) (start count : Nat) : Bool :=
  let (source,operations) := if fresh then (cleanScope,cleanOps [hData] [hData]) else (dirtyScope,dirtyOps [hData])
  ((workspaceInterval source operations fresh (some (text,layout,start,count))).run 20000000).1.isOk

#guard targetWorkspaceAccepted true (targetWorkspace 3 "h q[2];\n") [2,0] 0 1
#guard targetWorkspaceAccepted false (targetWorkspace 3 "x q[0];\nh q[2];\nz q[0];\n") [2,0] 1 1
#guard !targetWorkspaceAccepted false (targetWorkspace 3 "h q[2];\n") [0,2] 0 1
#guard !targetWorkspaceAccepted true (targetWorkspace 3 "h q[2];\nz q[0];\n") [2,0] 0 2
#guard !targetWorkspaceAccepted true (targetWorkspace 3 "x q[0];\nh q[2];\n") [2,0] 1 1
#guard !targetWorkspaceAccepted true (targetWorkspace 3 "h q[2];\nz q[0];\n") [2,0] 0 1
#guard !targetWorkspaceAccepted true (targetWorkspace 3 "h q[1];\n") [2,0] 0 1
#guard !targetWorkspaceAccepted true (targetWorkspace 1 "h q[0];\n") [0,0] 0 1

private def placedWorkspace (fresh : Bool) (frame : List Nat) (scratch : Option Nat) : Bool :=
  let (source,operations) := if fresh then (cleanScope,cleanOps [hData] [hData]) else (dirtyScope,dirtyOps [hData])
  ((workspaceInterval source operations fresh none none
    (some (targetWorkspace 3 "h q[2];\n",frame,scratch))).run 20000000).1.isOk

#guard placedWorkspace true [2] (some 0)
#guard placedWorkspace false [2,0] none
#guard !placedWorkspace true [2] (some 2)
#guard !placedWorkspace true [2,0] (some 1)
#guard !placedWorkspace false [0,2] none
#guard !placedWorkspace false [2,0] (some 1)

private def routedWorkspace (gates : String) (align : List Target.CanonicalOpenQasmPlacement.Match)
    (suffix : Option (List Target.CanonicalOpenQasmPlacement.Match) := none) :
    Finite.WorkM (List Nat × Nat) := do
  let source ← SourceRuntimeTrace.read #[("main","#![no_implicit_prelude]\n" ++ cleanScope)] "main" "route"
  let [.workspace event children] := source.events | throw .request
  let beforeOps : List Semantics.Observation.Op :=
    [.pure (.init0 10 6),.pure (.packUnit 12)]
  let body := cleanOps [hData] [hData]
  let program : Semantics.Observation.Program := if suffix.isSome then
    ⟨[],[],beforeOps++body++[.pure (.gate .z 13 14),.pure (.unpackUnit 12),.measure 14 3],[],[3],.observe⟩
    else ⟨[],[],beforeOps++body,[13,12],[],.isometry⟩
  let root ← Qirf.RuntimeInterval.prepare [] program
  let interval ← Qirf.RuntimeInterval.check root.block beforeOps.length body.length
  let bindings : Qirf.RuntimeOwnerMap.Map :=
    [⟨event.input,⟨10,[6],1⟩⟩,⟨⟨4,[.unit]⟩,⟨12,[],0⟩⟩]
  let before : Qirf.RuntimeStructuralAction.SourceState := ⟨bindings,bindings.map (·.owner),event.nextOrdinal⟩
  let original ← Qirf.RuntimeWorkspace.readOriginal event children
  let literal ← Qirf.RuntimeWorkspace.readLiteral original interval before
  let map ← Qirf.RuntimeWorkspace.readCallerMap literal #[]
  let text := if suffix.isSome then
    "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[4] q;\nbit[1] c;\nreset q;\n" ++ gates
    else targetWorkspace 3 gates
  let target ← Target.CanonicalOpenQasmResources.check text.toUTF8 4
  let prefixCheck ← Target.CanonicalOpenQasmPlacement.check target program
    (fun a b => a+1 == b || b+1 == a) align
  if let some suffix := suffix then
    let finished ← Target.CanonicalOpenQasmPlacement.finishWorkspace map prefixCheck 1 (some 3) suffix
    return (target.circuit.measurements,finished.final.gateIndex)
  let placed ← Target.CanonicalOpenQasmPlacement.workspace map prefixCheck 1 (some 0)
  pure (placed.placed.liveLayout,prefixCheck.state.gateIndex)

private def routedPrefix : List Target.CanonicalOpenQasmPlacement.Match := [.original,.original,.route,.route]
#guard ((routedWorkspace "swap q[0], q[1];\nswap q[1], q[2];\nh q[2];\n" routedPrefix).run
  20000000).1.toOption == some ([2],2)
#guard ((routedWorkspace "swap q[0], q[1];\nswap q[1], q[2];\nh q[1];\n" routedPrefix).run
  20000000).1.toOption.isNone
#guard ((routedWorkspace "swap q[0], q[2];\nswap q[1], q[2];\nh q[2];\n" routedPrefix).run
  20000000).1.toOption.isNone
#guard ((routedWorkspace "swap q[0], q[1];\nswap q[1], q[2];\nh q[2];\n" [.original,.route,.route]).run
  20000000).1.toOption.isNone

private def terminalWorkspaceGates : String := "swap q[0], q[1];\nswap q[1], q[2];\nh q[2];\nz q[2];\n"
private def terminalWorkspaceCase :=
  routedWorkspace (terminalWorkspaceGates ++ "c[0] = measure q[2];\n") routedPrefix (some [.original])
private def terminalWorkspace (tail : String) (suffix : List Target.CanonicalOpenQasmPlacement.Match) :=
  ((routedWorkspace (terminalWorkspaceGates ++ tail) routedPrefix (some suffix)).run 20000000).1.toOption

#guard (terminalWorkspaceCase.run exactWorkLimit).1.toOption == some ([2],4)
#guard
  let consumed := exactWorkLimit - (terminalWorkspaceCase.run exactWorkLimit).2
  match (terminalWorkspaceCase.run (consumed-1)).1 with
  | .error (.arithmetic .workLimit) => true
  | _ => false
#guard (terminalWorkspace "c[0] = measure q[1];\n" [.original]).isNone
#guard (terminalWorkspace "c[0] = measure q[3];\n" [.original]).isNone
#guard (terminalWorkspace "x q[2];\nc[0] = measure q[2];\n" [.original]).isNone
#guard (terminalWorkspace "c[0] = measure q[2];\n" []).isNone

private def terminalOutputOrder (measurements : String) : Finite.WorkM Unit := do
  let program : Semantics.Observation.Program := ⟨[],[],[.pure (.init0 10 6),.pure (.init0 11 7),
    .pure (.init0 12 8),.measure 11 20,.discard 12,.measure 10 21],[],[21,20],.observe⟩
  let _ ← Qirf.RuntimeInterval.prepare [] program
  let header := "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[3] q;\nbit[2] c;\nreset q;\n"
  let target ← Target.CanonicalOpenQasmResources.check (header ++ measurements).toUTF8 3
  let prefixCheck ← Target.CanonicalOpenQasmPlacement.check target program (fun _ _ => false)
    [.original,.original,.original]
  let _ ← Target.CanonicalOpenQasmPlacement.checkReadout target program prefixCheck.state

#guard ((terminalOutputOrder "c[0] = measure q[0];\nc[1] = measure q[1];\n").run 20000000).1.isOk
#guard !((terminalOutputOrder "c[0] = measure q[1];\nc[1] = measure q[0];\n").run 20000000).1.isOk
#guard !((terminalOutputOrder "c[0] = measure q[0];\nc[1] = measure q[2];\n").run 20000000).1.isOk

private def repeatedCleanSource : String :=
  "#![no_implicit_prelude]\npub unitary fn route(q:Q<Bit>)->Q<Bit>{" ++
  "clean(clean(q,h){|data,scratch|(h(data),scratch)},h){|data,scratch|(h(data),scratch)}}"

private def repeatedCleanBody (input output wire : Nat) : Semantics.Observation.Op :=
  .pure (.certifiedCompute input output [wire] [0,0] [hData] [hData])

private def repeatedCleanTrace (gates : String) (between : List Target.CanonicalOpenQasmPlacement.Match) :
    Finite.WorkM (List Nat × Nat) := do
  let sources := #[("main",repeatedCleanSource)]
  let source ← SourceRuntimeTrace.read sources "main" "route"
  let [.workspace first firstBody,.workspace second secondBody] := source.events | throw .request
  let program : Semantics.Observation.Program := ⟨[],[],[.pure (.init0 10 6),
    repeatedCleanBody 10 11 7,repeatedCleanBody 11 13 8,.measure 13 20],[],[20],.observe⟩
  let body ← Qirf.RuntimeInterval.prepare [] program
  let firstInterval ← Qirf.RuntimeInterval.check body.block 1 1
  let secondInterval ← Qirf.RuntimeInterval.check body.block 2 1
  let firstOriginal ← Qirf.RuntimeWorkspace.readOriginal first firstBody
  let secondOriginal ← Qirf.RuntimeWorkspace.readOriginal second secondBody
  let firstBefore : Qirf.RuntimeStructuralAction.SourceState :=
    ⟨[⟨first.input,⟨10,[6],1⟩⟩],[first.input],first.nextOrdinal⟩
  let secondBefore : Qirf.RuntimeStructuralAction.SourceState :=
    ⟨[⟨second.input,⟨11,[6],1⟩⟩],[first.input,first.scratch],second.nextOrdinal⟩
  let firstLiteral ← Qirf.RuntimeWorkspace.readLiteral firstOriginal firstInterval firstBefore
  let secondLiteral ← Qirf.RuntimeWorkspace.readLiteral secondOriginal secondInterval secondBefore
  let firstMap ← Qirf.RuntimeWorkspace.readCallerMap firstLiteral #[]
  let secondMap ← Qirf.RuntimeWorkspace.readCallerMap secondLiteral #[]
  let firstSegment : Target.CanonicalOpenQasmPlacement.Segment program :=
    ⟨sources,"main",[],body.block,1,1,first,firstBody,firstOriginal,firstInterval,firstBefore,firstLiteral,
      firstMap,[.original],3,some 1⟩
  let secondSegment : Target.CanonicalOpenQasmPlacement.Segment program :=
    ⟨sources,"main",[],body.block,2,1,second,secondBody,secondOriginal,secondInterval,secondBefore,secondLiteral,
      secondMap,between,3,some 1⟩
  let header := "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[3] q;\nbit[1] c;\nreset q;\n"
  let target ← Target.CanonicalOpenQasmResources.check (header ++ gates).toUTF8 3
  let checked ← Target.CanonicalOpenQasmPlacement.finishTrace target program (fun _ _ => true) [1]
    [firstSegment,secondSegment] []
  pure (target.circuit.measurements,checked.final.gateIndex)

private def repeatedCleanWord (data : Nat) : String := s!"x q[1];\nh q[{data}];\nx q[1];\n"
#guard ((repeatedCleanTrace (repeatedCleanWord 0 ++ "swap q[0], q[2];\n" ++ repeatedCleanWord 2 ++
  "c[0] = measure q[2];\n") [.route]).run exactWorkLimit).1.toOption == some ([2],7)
#guard ((repeatedCleanTrace (repeatedCleanWord 0 ++ "swap q[0], q[1];\n" ++ repeatedCleanWord 1 ++
  "c[0] = measure q[1];\n") [.route]).run exactWorkLimit).1.toOption.isNone
#guard ((repeatedCleanTrace (repeatedCleanWord 0 ++ repeatedCleanWord 0 ++ "c[0] = measure q[1];\n")
  []).run exactWorkLimit).1.toOption.isNone

private def reusableWorkspace (gates : String) (first second : Nat) (count : Nat := 1) : Bool :=
  ((workspaceInterval cleanScope (cleanOps [hData] [hData]) true none
    (some (targetWorkspace 3 gates,[2,0],first,second,count))).run 20000000).1.isOk

#guard reusableWorkspace "h q[2];\nt q[1];\nh q[2];\n" 0 2
#guard !reusableWorkspace "h q[2];\nt q[1];\nh q[2];\n" 2 0
#guard !reusableWorkspace "h q[2];\n" 0 0
#guard !reusableWorkspace "h q[2];\nx q[0];\nh q[2];\n" 0 2
#guard !reusableWorkspace "x q[0];\nh q[2];\nh q[2];\n" 1 2
#guard !reusableWorkspace "h q[2];\nh q[2];\nx q[0];\n" 0 1

private def touchAndRestore : String := "h q[0];\nh q[2];\nh q[0];\n"
#guard reusableWorkspace (touchAndRestore ++ "t q[1];\n" ++ touchAndRestore) 0 4 3
#guard !reusableWorkspace (touchAndRestore ++ "x q[0];\n" ++ touchAndRestore) 0 4 3
#guard !reusableWorkspace (touchAndRestore ++ "t q[1];\nh q[0];\nh q[2];\nz q[0];\n") 0 4 3

private def expandedWorkspaceBody : Finite.WorkM Nat := do
  let gate : Semantics.Raw.Op := .gate .h 0 1
  let body : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[.pure gate,.pure (.gate .h 1 2)],[2],[],.unitary⟩
  let input : Semantics.ObservingFunction.Input := ⟨[.bit],body,body,⟨"body","body",[]⟩⟩
  let receipt ← Raw.BranchFunction.checkEntry [] input input
  let call : Semantics.Finite.Step := ⟨[],.contract [0] 0 true⟩
  Raw.WorkspaceResources.bodyExpansion [receipt] [.computed 1 [0] 1 1 [0,0] [hData,call] []]

#guard (expandedWorkspaceBody.run 20000000).1.toOption == some 3

private def nestedPhysicalWorkspace : Finite.WorkM (Nat × Nat) := do
  let body : Semantics.Observation.Program :=
    ⟨[⟨0,[0],1⟩],[],[.pure (.certifiedCompute 0 1 [1] [0,0] [hData,hData] [])],[1],[],.unitary⟩
  let input : Semantics.ObservingFunction.Input := ⟨[.bit],body,body,⟨"cleanCall","cleanCall",[]⟩⟩
  let checked ← Raw.BranchFunction.checkEntry [] input input
  let call : Semantics.Finite.Step := ⟨[],.contract [0] 0 false⟩
  let inverse : Semantics.Finite.Step := ⟨[],.contract [0] 0 true⟩
  let expansion ← Raw.WorkspaceResources.bodyExpansion [checked] [.circuit 1 [call,inverse]]
  return (checked.expandedSteps,expansion)

-- Each call contains two physical H steps and two predicate passes.
#guard (nestedPhysicalWorkspace.run 20000000).1.toOption == some (1,8)
#guard ((Raw.WorkspaceResources.bodyExpansion [] [.circuit 1 [⟨[],.contract [0] 0 false⟩]]).run
  20000000).1.toOption.isNone

private def protectedSource := predicate ++
  "pub unitary fn route(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|aux|z(aux)}}"
#guard (read protectedSource).map (fun checked => ((valueOwners checked.summary.value).map (·.ordinal),
  checked.summary.allocated.map (·.ordinal),checked.summary.consumed.map (·.ordinal),
  checked.events.flatMap Event.computedOffsets |>.length)) = some ([0],[1],[1],1)

private def certifiedSource := predicate ++
  "unitary fn logical(q:Q<Bit>)->Q<Bit>{z(q)}" ++
  "pub unitary fn route(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate,logical){|data,aux|(z(data),aux)}}"
#guard (read certifiedSource).isSome
#guard (read (certifiedSource.replace "(z(data),aux)" "(data,z(aux))")).isSome

-- H is a well-typed use body. Only a later exact native cleanup equation can
-- reject this protected scope; source typing never certifies its cleanliness.
#guard (read (protectedSource.replace "z(aux)" "h(aux)")).isSome
#guard (read (protectedSource.replace "classical fn predicate" "fn predicate")).isNone
#guard (read (protectedSource.replace "predicate(b:Bit)" "predicate((b,u):(Bit,Unit))")).isNone
#guard (read ("use std::state::reset;" ++ protectedSource.replace "z(aux)" "reset(aux)")).isNone
#guard (read (protectedSource.replace "z(aux)" "q")).isNone
#guard (read (protectedSource.replace "z(aux)" "unit(())")).isNone

private def capture := predicate ++
  "pub unitary fn route(c:Bit,q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|aux|if c{z(aux)}else{aux}}}"
#guard (read capture).isSome
private def certifiedCapture := (certifiedSource.replace "route(q:" "route(c:Bit,q:").replace
  "(z(data),aux)" "(if c{z(data)}else{data},aux)"
#guard (read certifiedCapture).isNone

private def inactive := predicate ++
  "pub unitary fn route[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n==0{q}else{with_computed(q,predicate){|aux|z(aux)}}}"
#guard ((SourceRuntimeTrace.read (sources inactive) "main" "route" {naturals := [("n",0)]}).run 2000000000).1.toOption.map
  (fun checked => checked.events.flatMap Event.computedOffsets |>.length) = some 0
#guard ((SourceRuntimeTrace.read (sources inactive) "main" "route" {naturals := [("n",1)]}).run 2000000000).1.toOption.map
  (fun checked => checked.events.flatMap Event.computedOffsets |>.length) = some 1

private def recovered : Finite.WorkM (List Nat × Bool) := do
  let checked ← SourceRuntimeTrace.read (sources protectedSource) "main" "route"
  let [Event.computed event _] := checked.events | throw Finite.Error.request
  let body ← SourceRuntimeTrace.readComputedSource event
  let predicate ← SourceRuntimeTrace.readComputedPredicateBody event
  return ((valueOwners body.result.value).map (·.ordinal),predicate.checked.summary.generic.quantumUse)
#guard (recovered.run 2000000000).1.toOption = some ([1],false)

private def nominal := "#![no_implicit_prelude]\n" ++
  "pub enum Tri{A,B,C}\n" ++
  "classical fn is_b(tag:Tri)->Bit{match tag{Tri::A=>0,Tri::B=>1,Tri::C=>0}}\n" ++
  "pub unitary fn route(q:Q<Tri>)->Q<Tri>{with_computed(q,is_b){|flag|phase[1,1](flag)}}"

private def predicateTable (table : List Nat) : Finite.WorkM (List Nat) := do
  let checked ← SourceRuntimeTrace.read #[("main",nominal)] "main" "route"
  let [Event.computed event _] := checked.events | throw Finite.Error.request
  let original ← Qirf.RuntimeComputedPredicate.readSource event
  let _ ← Qirf.RuntimeComputedPredicate.checkTable original table
  return original.layout.labels

#guard ((predicateTable [0,1,0,0]).run 20000000).1.toOption = some [0,1,2]
#guard [[1,0,0,0],[0,1,0,1],[0,1,0]].all fun table =>
  match ((predicateTable table).run 20000000).1 with
  | .error .equation => true
  | _ => false


private def protectedInterval (sourceText : String) (table : List Nat) (uses : List Semantics.Raw.Use)
    (staleAuxiliary : Bool := false) :
    Finite.WorkM (List Nat × List Nat) := do
  let source ← SourceRuntimeTrace.read #[("main",sourceText)] "main" "route"
  let [Event.computed event _] := source.events | throw Finite.Error.request
  let input : Semantics.Raw.Port := ⟨10,[6,2],2⟩
  let spectator : Semantics.Raw.Port := ⟨11,[],0⟩
  let spectatorOwner : Semantics.SourceOwners.Owner := ⟨4,[.unit]⟩
  let program : Semantics.Observation.Program := ⟨[input,spectator],[],
    [.pure (.computeUseUncompute 10 12 [] [8] table uses)],
    [12,11],[],.unitary⟩
  let prepared ← Qirf.RuntimeInterval.prepare [] program
  let interval ← Qirf.RuntimeInterval.check prepared.block 0 1
  let issued := [event.input,spectatorOwner] ++ (if staleAuxiliary then [event.initial.auxiliary] else [])
  let before : Qirf.RuntimeStructuralAction.SourceState :=
    ⟨[⟨event.input,input⟩,⟨spectatorOwner,spectator⟩],issued,event.nextOrdinal⟩
  let original ← Qirf.RuntimeComputedUse.prepare event
  let checked ← Qirf.RuntimeComputedUse.read original interval before
  return (checked.literal.output.wires,checked.literal.after.bindings.map (·.port.token))

private def auxiliaryZ : Semantics.Raw.Use := .protectedGate ⟨.ancilla,0⟩ .z

#guard ((protectedInterval nominal [0,1,0,0] [auxiliaryZ]).run 20000000).1.toOption = some ([6,2],[12,11])
#guard (match ((protectedInterval nominal [0,0,1,0] [auxiliaryZ]).run 20000000).1 with
  | .error .equation => true
  | _ => false)
#guard ((protectedInterval nominal [0,1,0,0] [auxiliaryZ] true).run 20000000).1.toOption.isNone

-- A relative phase match alone would accept the negated matrix.
#guard (match ((protectedInterval nominal [0,1,0,0] [.phase [] .minusOne,auxiliaryZ]).run 20000000).1 with
  | .error .equation => true
  | _ => false)
#guard ((protectedInterval nominal [0,1,0,0] [.protectedGate ⟨.source,0⟩ .z]).run 20000000).1.toOption.isNone
#guard ((protectedInterval (nominal.replace "phase[1,1](flag)" "h(flag)") [0,1,0,0] []).run 20000000).1.toOption.isNone
#guard ((protectedInterval (nominal.replace "phase[1,1](flag)" "h(h(flag))") [0,1,0,0] []).run 20000000).1.toOption.isSome

private def nominalNamed := (nominal.replace "pub unitary fn route" "unitary fn mark(b:Q<Bit>)->Q<Bit>{phase[1,1](b)}\npub unitary fn route").replace
  "phase[1,1](flag)" "mark(flag)"
#guard ((protectedInterval nominalNamed [0,1,0,0] [auxiliaryZ]).run 20000000).1.toOption.isSome
#guard ((protectedInterval (nominalNamed.replace "phase[1,1](b)" "b") [0,1,0,0] [auxiliaryZ]).run 20000000).1.toOption.isNone


private def certifiedNominal := (nominal.replace "pub unitary fn route"
  "unitary fn logical(q:Q<Tri>)->Q<Tri>{global_phase_eighth(q)} pub unitary fn route").replace
  "with_computed(q,is_b){|flag|phase[1,1](flag)}"
  "with_computed(q,is_b,logical){|data,flag|(global_phase_eighth(data),flag)}"

private def certifiedInterval (sourceText : String) (table : List Nat) (useExponent logicalExponent : Nat) :
    Finite.WorkM (Nat × Nat) := do
  let source ← SourceRuntimeTrace.read #[("main",sourceText)] "main" "route"
  let [Event.computed event _] := source.events | throw Finite.Error.request
  let input : Semantics.Raw.Port := ⟨10,[6,2],2⟩
  let spectator : Semantics.Raw.Port := ⟨11,[],0⟩
  let spectatorOwner : Semantics.SourceOwners.Owner := ⟨4,[.unit]⟩
  let useSteps : List Semantics.Finite.Step := [⟨[],.monomial [] [0] [useExponent]⟩]
  let logicalSteps : List Semantics.Finite.Step := [⟨[],.monomial [] [0] [logicalExponent]⟩]
  let program : Semantics.Observation.Program := ⟨[input,spectator],[],
    [.pure (.certifiedCompute 10 12 [8] table useSteps logicalSteps)],[12,11],[],.unitary⟩
  let block ← Qirf.RuntimeInterval.prepare [] program
  let interval ← Qirf.RuntimeInterval.check block.block 0 1
  let before : Qirf.RuntimeStructuralAction.SourceState :=
    ⟨[⟨event.input,input⟩,⟨spectatorOwner,spectator⟩],[event.input,spectatorOwner],event.nextOrdinal⟩
  let prepared ← Qirf.RuntimeCertifiedComputed.prepare event
  let checked ← Qirf.RuntimeCertifiedComputed.read prepared interval before
  return (checked.used.action.logical.rows,checked.logical.action.logical.rows)

#guard ((certifiedInterval certifiedNominal [0,1,0,0] 1 1).run 20000000).1.toOption = some (6,3)
-- Raw cleanup still holds for both substituted phases. The original
-- contracts independently refuse the identical change to both Raw circuits.
#guard (match ((certifiedInterval certifiedNominal [0,1,0,0] 2 2).run 20000000).1 with
  | .error .equation => true
  | _ => false)
#guard ((certifiedInterval certifiedNominal [0,1,0,1] 1 1).run 20000000).1.toOption.isNone
#guard ((certifiedInterval (certifiedNominal.replace "{global_phase_eighth(q)}" "{q}")
  [0,1,0,0] 1 1).run 20000000).1.toOption.isNone

#print axioms QleisliKernel.SourceTypes.SourceComputedBindings.originalMember
#print axioms QleisliKernel.SourceTypes.SourceRuntimeTrace.readComputedSource
end QleisliKernel.Tests.SourceRuntimeComputed
