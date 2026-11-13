import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Qirf.RuntimeCertifiedComputed
import QleisliKernel.Qirf.RuntimeWorkspace
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
    (fresh : Bool) : Finite.WorkM (List Nat × List Nat × Raw.WorkspaceResources.Counts × Nat) := do
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
