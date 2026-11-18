import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimeLocalEvents
import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.Qirf.RuntimeBodyOperations
import QleisliKernel.Qirf.RuntimePureComposition
import QleisliKernel.Tests.ArmBody

/-! Fresh original named bodies against actual local Raw fragments.
Small role/phase faults stay structurally valid Raw; the source continuation
must independently reject them. No v5 handle or full-profile claim is issued.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimePureBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes QleisliKernel.Finite

private def text := "#![no_implicit_prelude]\nunitary fn change(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){(b,h(a))}\npub unitary fn main(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){change(a,b)}"
private def sources : Sources := #[("main",text)]
private def program (wrongRole wrongReturn : Bool) : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.gate .h (if wrongRole then 1 else 0) 2)],
    if wrongReturn then [2,if wrongRole then 0 else 1] else [if wrongRole then 0 else 1,2],[],.unitary⟩

private def checked (wrongRole wrongReturn : Bool) : WorkM Nat := do
  let artifact : Qirf.Artifact := ⟨#[program wrongRole wrongReturn],#[],sources,0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let childSignature ← SourceRuntimeContext.readSignature sources "main" "change" {}
  let child ← SourceRuntimeTrace.readBodyWithSignature childSignature
  let some call := body.checked.events.head? | throw .request
  let some action := child.checked.events.head? | throw .request
  let context : RuntimeContextRequest.Context := .mk
    [⟨call.offset,0,1⟩] [] [(⟨call.offset,0,1⟩,.mk [⟨action.offset,0,1⟩] [] [] [] [])] [] []
  let initial : RuntimeOwnerMap.Map := [⟨⟨0,[.bit]⟩,⟨0,[0],1⟩⟩,⟨⟨1,[.bit]⟩,⟨1,[1],1⟩⟩]
  let root ← Validity.checkRootFromRoots artifact #[0] [("main",text)] [0]
  let result ← Qirf.RuntimePureBody.check artifact root body root.program context initial
  let _ ← RuntimePureComposition.prepare artifact root body context initial result
  return result.result.actions.length

#guard (checked false false).run 10000000 |>.1.toOption == some 1
#guard (match (checked true false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (checked false true).run 10000000 with | (.error _,_) => true | _ => false)

-- An equal-length, reordered label list cannot have the receipt retained
-- by a successful Bit selection, even if the proposed matrices are equal.
example : ¬ Qirf.RuntimePureBody.SelectionLayouts [.bit] [.bit] 1 1 [1,0] := by
  intro proposed
  obtain ⟨work,left,ran⟩ := proposed.selectorRead
  have original := QleisliKernel.FiniteCarrier.read_reference _ _ _ _ ran
  change some (⟨1,[0,1]⟩ : Semantics.FiniteCarrier.Layout) = some ⟨1,[1,0]⟩ at original
  cases original

private def selected (exponent : Nat) (swapOutputs : Bool := false) : WorkM (Nat × List (Nat × Nat)) := do
  let artifact := ArmBody.artifact exponent
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let sign ← SourceRuntimeContext.readSignature artifact.sources "main" "sign" {}
  let sign ← SourceRuntimeTrace.readBodyWithSignature sign
  let some phase := sign.checked.events.head? | throw .request
  let some event := body.checked.events.head? | throw .request
  let position : SourceSequence.Position := ⟨event.offset,0,3⟩
  let interface := ArmBody.interface
  let proposed := if swapOutputs then
    let outputs := interface.outputs.zipWith (fun owner other => {owner with port := other.port}) interface.outputs.reverse
    {interface with outputs}
  else interface
  let site : RuntimeContextRequest.Site := ⟨proposed,proposed,position,[⟨3,4⟩,⟨1,2⟩]⟩
  let context : RuntimeContextRequest.Context := .mk [position] [site] [] []
    [(.function 1,.mk [⟨phase.offset,0,1⟩] [] [] [] []),(.function 0,.mk [] [] [] [] [])]
  let headers ← RuntimeBodyDiscovery.readHeaders artifact "main" "route" {} context
  let fresh ← RuntimeBodyDiscovery.prepare ArmBody.order headers
  let prepared ← RuntimeInterval.prepare fresh.root.dependencies fresh.root.program
  let actualBody := headers.source.body
  let inputs ← RuntimeSourceBoundary.readInputs actualBody prepared
    ((ArmBody.interface).inputs.map fun owner => [.quantum owner])
  let actual ← Qirf.RuntimePureBody.check artifact fresh.root actualBody fresh.root.program context inputs.owners.bindings
  let _ ← RuntimePureComposition.prepare artifact fresh.root actualBody context inputs.owners.bindings actual
  let [.selection frame selectorBits targetBits retained restricted _ _ _ _ _ _ codes _] := actual.result.actions
    | throw .request
  let owners := codes.owners
  let localAction ← RuntimeLocalEvents.readSource frame selectorBits targetBits retained restricted owners
  return (localAction.traceResult.events.length,
    owners.transport.after.bindings.map fun b => (b.owner.ordinal,b.port.token))

#guard (selected 4).run 10000000 |>.1.toOption == some (1,[(0,4),(1,5)])
-- Full port types and Raw are unchanged when the two claimed output tokens are swapped.
#guard (match (selected 4 true).run 10000000 with | (.error .request,_) => true | _ => false)
-- The whole main, arm, specification and control agree on the wrong phase.
-- Every original provider body is nevertheless traversed, so this refuses.
#guard (match (selected 0).run 10000000 with | (.error .equation,_) => true | _ => false)

private inductive InlineFault where
  | none | phase | order | controlled | parent | offset | ordinal
  deriving BEq

private inductive InlineShape where
  | qif | qmatch | product
  deriving BEq

private def inlineSelection (fault : InlineFault) (shape : InlineShape := .qmatch) : WorkM (List Nat) := do
  let basis := if shape == .product then "(Unit,Bit)" else "Bit"
  let text := s!"#![no_implicit_prelude] pub unitary fn route(s:Q<Bit>,q:Q<{basis}>)->(Q<Bit>,Q<{basis}>)" ++
    match shape with
    | .qif => "{qif(s,q){0=>{q},1=>{let r=h(q);phase[1,1](r)}}}"
    | .qmatch => "{qmatch(s,q){1=>{let r=h(q);phase[1,1](r)},0=>{q}}}"
    | .product => "{qmatch(s,q){1=>{let (u,b)=split(q);join(u,phase[1,1](h(b)))},0=>{q}}}"
  let port := fun token wire => (⟨token,[wire],1⟩ : Semantics.Raw.Port)
  let desired : List Semantics.Raw.Gate := [.h,.z]
  let actual := if fault == .phase then [.h,.t] else if fault == .order then desired.reverse else desired
  let control := fun (gates : List Semantics.Raw.Gate) =>
    (⟨[port 0 0,port 1 1],[],[.pure (.quantumIf 0 1 2 3 [] (gates.map (fun gate => .gate gate 0)))],
      [2,3],[],.unitary⟩ : Semantics.Observation.Program)
  let gates := actual.zipIdx.map fun (gate,index) =>
    let input := index + (if shape == .product then 2 else 0)
    Semantics.Raw.Op.gate gate input (input+1)
  let operations := if shape == .product then [.split 0 1 2 0] ++ gates ++ [.join 1 4 5] else gates
  let action : Semantics.Observation.Program :=
    ⟨[port 0 0],[],operations.map .pure,[if shape == .product then 5 else 2],[],.unitary⟩
  let keep : Semantics.Observation.Program := ⟨[port 0 0],[],[],[0],[],.unitary⟩
  let artifact : Artifact := ⟨#[control (if fault == .parent then [.h] else actual),
    action,control (if fault == .controlled then [.h] else actual),keep,control []],#[],#[("main",text)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let root ← Validity.checkRootFromRoots artifact #[1,2,3,4,0] [("main",text)] [0,1,2,3,4]
  let prepared ← RuntimeInterval.prepare root.dependencies root.program
  let interval ← RuntimeInterval.check prepared.block 0 1
  if first : 0 < body.checked.events.length then
    let index : Fin body.checked.events.length := ⟨0,first⟩
    let .selection event := body.checked.events[index] | throw .request
    let selector := event.selector
    let target := event.target
    let offset := event.parsed.keyword.span.startByte
    let table ← QuantumArms.readRuntimeArms event offset selector.basis target.basis
    let interface : Semantics.CarrierInterface.Interface :=
      ⟨[⟨port 0 0,selector.basis⟩,⟨port 1 1,target.basis⟩],
        [⟨port 2 0,selector.basis⟩,⟨port 3 1,target.basis⟩],.unitary⟩
    let subjects : List RuntimeContextRequest.Arm := [⟨1,2⟩,⟨3,4⟩]
    let site : RuntimeContextRequest.Site :=
      ⟨interface,interface,⟨offset,0,1⟩,if shape == .qif then subjects.reverse else subjects⟩
    let frame ← RuntimeOwnerMap.check [selector,target] interval.before [⟨selector,port 0 0⟩,⟨target,port 1 1⟩]
    let owners ← RuntimeOwnerTransition.read interval frame.bindings
    let execution : Qirf.RuntimePureBody.ExecutionMode artifact root := .fresh .strict
    let run := Qirf.RuntimePureBody.runBlockCore artifact root execution 8
    let history : RuntimeStructuralAction.SourceState :=
      ⟨frame.bindings,[selector,target],if fault == .ordinal then 3 else 2⟩
    let same ← if same : event.callerName = "route" then pure (⟨same⟩ : PLift _) else throw .request
    let (_,labels) ← Qirf.RuntimePureBody.selectionNode artifact interval frame owners selector target table site []
      fun index arm labels => do
        let .inline replay original _ _ _ := arm | throw .request
        let some subject := site.arms[index.val]? | throw .request
        let positions := replay.result.events.zipIdx.map fun (event,index) =>
          (⟨event.offset+(if fault == .offset then 1 else 0),index,1⟩ : SourceSequence.Position)
        let request := RuntimeContextRequest.Context.mk positions [] [] [] []
        let checked ← Qirf.RuntimePureBody.readInlineArm (execution := execution) same.down replay original
          subject.implementation request () (.root body) history run
        return (checked.action.code.logical,labels ++ [arm.ordinal])
    return labels
  else throw .request

#guard ((inlineSelection .none).run 10000000).1.toOption == some [1,0]
#guard ((inlineSelection .none .qif).run 10000000).1.toOption == some [0,1]
#guard ((inlineSelection .none .product).run 10000000).1.toOption == some [1,0]
#guard [InlineFault.phase,.order,.controlled,.parent].all fun fault =>
  ((inlineSelection fault).run 10000000).1 matches .error .equation
#guard ((inlineSelection .offset).run 10000000).1 matches .error .request
#guard ((inlineSelection .ordinal).run 10000000).1 matches .error .request

private inductive InlinePlanFault where
  | none | missing | extra | wrongArm | wrongBody | missingRoot | forward | control | parent
  deriving BEq

private def inlinePlan (fault : InlinePlanFault) (checkRaw : Bool := false) (viaHelper : Bool := false) :
    WorkM (List Nat × Nat) := do
  let helperSource := if viaHelper then "unitary fn helper(q:Q<Bit>)->Q<Bit>{adjoint(h)(q)} " else ""
  let block := if viaHelper then "helper(q)" else "h(q)"
  let text := "#![no_implicit_prelude] " ++ helperSource ++ "pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){" ++
    "qmatch(s,q){1=>{" ++ block ++ "},0=>h}}"
  let port := fun token wire => (⟨token,[wire],1⟩ : Semantics.Raw.Port)
  let standalone := fun gate => (⟨[port 0 0],[],[.pure (.gate gate 0 1)],[1],[],.unitary⟩ : Semantics.Observation.Program)
  let controlled (zero one : List Semantics.Raw.UnitaryStep) : Semantics.Observation.Program :=
    ⟨[port 0 0,port 1 1],[],[.pure (.quantumIf 0 1 2 3 zero one)],[2,3],[],.unitary⟩
  let h := [.gate .h 0]
  let written := if fault == .forward then .z else .h
  let physical := [.gate written 0]
  let parent := if fault == .parent then .phase .minusOne :: physical else physical
  let active := if fault == .control then .phase .minusOne :: physical else physical
  let artifact : Artifact :=
    ⟨#[controlled h parent,standalone written,controlled [] active,standalone .h,controlled [] h],#[],#[("main",text)],0,none⟩
  let body ← SourceRuntimeTrace.read artifact.sources "main" "route"
  let [.selection event] := body.events | throw .request
  let replay ← SourceRuntimeTrace.readInlineArmBody event 0
  let [action] := replay.result.events | throw .request
  let position : SourceSequence.Position := ⟨event.parsed.keyword.span.startByte,0,1⟩
  let interface : Semantics.CarrierInterface.Interface :=
    ⟨[⟨port 0 0,[.bit]⟩,⟨port 1 1,[.bit]⟩],[⟨port 2 0,[.bit]⟩,⟨port 3 1,[.bit]⟩],.unitary⟩
  let site : RuntimeContextRequest.Site := ⟨interface,interface,position,[⟨1,if fault == .missingRoot then 5 else 2⟩,⟨3,4⟩]⟩
  let activePosition : SourceSequence.Position := ⟨action.offset+(if fault == .wrongBody then 1 else 0),0,1⟩
  let calls : List (SourceSequence.Position × RuntimeContextRequest.Context) ← if viaHelper then do
    let .named call := action | throw .request
    let helper ← SourceRuntimeTrace.readNamedBody call
    let [.operation operation] := helper.checked.events | throw .request
    let position : SourceSequence.Position := ⟨operation.call.calleeOffset,0,1⟩
    let graph := RuntimeContextRequest.Context.withReferences [] [] [] [] [] [[]] [] []
    pure [(activePosition,RuntimeContextRequest.Context.mk [position] [] [(position,graph)] [] [])]
  else pure []
  let child := RuntimeContextRequest.Context.mk [activePosition] [] calls [] []
  let slots := match fault with
    | .missing => []
    | .extra => [(position,0,child),(position,1,child)]
    | .wrongArm => [(position,1,child)]
    | _ => [(position,0,child)]
  let request := RuntimeContextRequest.Context.withReferences [position] [site] [] [] [] [[]] [] slots
  let plan ← RuntimeBodyOperations.prepare artifact "main" "route" {} request
  if checkRaw then
    let tree := Semantics.RuntimeType.owner [.bit]
    let runtime : RuntimeFamily.Request := ⟨.exported,"main","route",[tree,tree],
      interface.inputs.map fun value => [.quantum value],[[]],Semantics.RuntimeType.tuple 2 [tree,tree],
      .tuple 2 :: interface.outputs.map (· |> .quantum),.unitary,{}⟩
    let checked ← RuntimeBodyOperations.read plan #[1,2,3,4,0] runtime
    if viaHelper then
      guard (checked.checked.receipts.length == 2 && checked.checked.receipts.any
        (fun receipt => receipt.request.requested.applicable && receipt.request.requested.controllable)) .request
    return (plan.roots,checked.selections.count)
  return (plan.roots,plan.receipts.length)

#guard ((inlinePlan .none).run 10000000).1.toOption == some ([0,1,2,3,4],1)
#guard [InlinePlanFault.missing,.extra,.wrongArm,.wrongBody,.missingRoot].all fun fault =>
  ((inlinePlan fault).run 10000000).1.toOption.isNone
#guard ((inlinePlan .none true).run 10000000).1.toOption == some ([0,1,2,3,4],1)
#guard ((inlinePlan .none true true).run 10000000).1.toOption == some ([0,1,2,3,4],1)
#guard [InlinePlanFault.forward,.control,.parent].all fun fault =>
  ((inlinePlan fault true).run 10000000).1 matches .error .equation

private def structural (text : String) (inputs : List Semantics.Raw.Port)
    (operations : List Semantics.Raw.Op) (outputs : List Nat) : WorkM (List Nat × List Nat × List Nat) := do
  let text := "#![no_implicit_prelude]\n" ++ text
  let sources : Sources := #[("main",text)]
  let program : Semantics.Observation.Program := ⟨inputs,[],operations.map .pure,outputs,[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],sources,0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let roles := body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let initial := (roles.zip inputs).map fun (owner,port) => (⟨owner,port⟩ : RuntimeOwnerMap.Binding)
  let context : RuntimeContextRequest.Context := .mk
    (body.checked.events.zipIdx.map fun (event,index) => ⟨event.offset,index,1⟩) [] [] [] []
  let root ← Validity.checkRootFromRoots artifact #[0] [("main",text)] [0]
  let checked ← Qirf.RuntimePureBody.check artifact root body root.program context initial
  let _ ← RuntimePureComposition.prepare artifact root body context initial checked
  return (checked.result.history.issued.map (·.ordinal),checked.result.retired.map (·.ordinal),
    checked.result.bindings.map (·.owner.ordinal))

private def splitJoin (wrongBoundary wrongOrder : Bool) := structural
  "pub unitary fn main(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{let (u,b)=split(q);join(u,h(b))}"
  [⟨0,[0],1⟩] [.split 0 1 2 (if wrongBoundary then 1 else 0),.gate .h 2 3,
    .join (if wrongOrder then 3 else 1) (if wrongOrder then 1 else 3) 4] [4]

-- The original owner 0 is replaced by 1,2,3. The same literal intervals retain
-- that complete history while H acts only on the original Bit component.
#guard (splitJoin false false).run 10000000 |>.1.toOption == some ([0,1,2,3],[0,1,2],[3])
#guard (match (splitJoin true false).run 10000000 with | (.error .invalid,_) => true | _ => false)
#guard (match (splitJoin false true).run 10000000 with | (.error .request,_) => true | _ => false)

-- Releasing a zero-width owner does not undo its scalar phase or issued ID.
private def releaseRecreate (exponent : Nat) := structural
  "pub unitary fn main(u:Q<Unit>)->Q<Unit>{let u=global_phase_eighth(u);finish(u);unit(())}"
  [⟨0,[],0⟩] [.applyUnitary 0 1 [⟨[],.monomial [] [0] [exponent]⟩],.unpackUnit 1,.packUnit 2] [2]

#guard (releaseRecreate 1).run 10000000 |>.1.toOption == some ([0,1],[0],[1])
#guard (match (releaseRecreate 0).run 10000000 with | (.error .equation,_) => true | _ => false)

private def namedStructural (omitH wrongJoin wrongReturn : Bool) : WorkM (List Nat × List Nat × List Nat) := do
  let text := "#![no_implicit_prelude]\nunitary fn rebuild(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{let (u,b)=split(q);join(u,h(b))}\npub unitary fn main(s:Q<Unit>,q:Q<(Unit,Bit)>)->(Q<(Unit,Bit)>,Q<Unit>){(rebuild(q),s)}"
  let operations : List Semantics.Raw.Op := [.split 1 2 3 0] ++ (if omitH then [] else [.gate .h 3 4]) ++
    [.join (if wrongJoin then (if omitH then 3 else 4) else 2)
      (if wrongJoin then 2 else (if omitH then 3 else 4)) 5]
  let program : Semantics.Observation.Program := ⟨[⟨0,[],0⟩,⟨1,[0],1⟩],[],operations.map .pure,
    (if wrongReturn then [0,5] else [5,0]),[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "main" {}
  let body ← SourceRuntimeTrace.readBodyWithSignature signature
  let callee ← SourceRuntimeTrace.readBodyWithSignature
    (← SourceRuntimeContext.readSignature artifact.sources "main" "rebuild" {})
  let some call := body.checked.events.head? | throw .request
  let [split,h,join] := callee.checked.events | throw .request
  let hCount := if omitH then 0 else 1
  let callPosition : SourceSequence.Position := ⟨call.offset,0,2+hCount⟩
  let context : RuntimeContextRequest.Context := .mk [callPosition] [] [(callPosition,
    .mk [⟨split.offset,0,1⟩,⟨h.offset,1,hCount⟩,⟨join.offset,1+hCount,1⟩] [] [] [] [])] [] []
  let roles := body.checked.summary.parameterValues.flatMap SourceRuntimeValues.valueOwners
  let initial := (roles.zip program.inputs).map fun (owner,port) => (⟨owner,port⟩ : RuntimeOwnerMap.Binding)
  let root ← Validity.checkRootFromRoots artifact #[0] [("main",text)] [0]
  let checked ← Qirf.RuntimePureBody.check artifact root body root.program context initial
  let _ ← RuntimePureComposition.prepare artifact root body context initial checked
  return (checked.result.history.issued.map (·.ordinal),checked.result.retired.map (·.ordinal),
    checked.result.bindings.map (·.owner.ordinal))

-- The callee's canonical owners are distinct from the caller's zero-width
-- spectator, and its source return order is not the native live-list order.
#guard (namedStructural false false false).run 10000000 |>.1.toOption == some ([0,1,2,3,4],[1,2,3],[4,0])
#guard (match (namedStructural true false false).run 10000000 with | (.error .equation,_) => true | _ => false)
#guard (match (namedStructural false true false).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (namedStructural false false true).run 10000000 with | (.error .request,_) => true | _ => false)

/-- A complete source frame includes the Unit spectator even for an empty
tape. The two active owners keep their identities when CNOT renames its ports. -/
private def ownerFlow (gate : Bool) : WorkM (List (Nat × Nat)) := do
  let roles : List RuntimeOwnerMap.Owner := [⟨0,[.bit]⟩,⟨1,[.bit]⟩,⟨2,[.unit]⟩]
  let ports : List Semantics.Raw.Port := [⟨0,[0],1⟩,⟨1,[1],1⟩,⟨2,[],0⟩]
  let ops := if gate then [Semantics.Observation.Op.pure (.cnot 0 1 4 5)] else []
  let program : Semantics.Observation.Program := ⟨ports,[],ops,if gate then [4,5,2] else [0,1,2],[],.unitary⟩
  let root ← RuntimeInterval.prepare [] program
  let interval ← RuntimeInterval.check root.block 0 ops.length
  let before ← RuntimeOwnerMap.check roles interval.before (roles.zipWith (fun owner port => ⟨owner,port⟩) ports)
  let transport ← RuntimeOwnerTransition.read interval before.bindings
  return transport.after.bindings.map fun b => (b.owner.ordinal,b.port.token)

#guard (ownerFlow false).run 10000000 |>.1.toOption == some [(0,0),(1,1),(2,2)]
#guard (ownerFlow true).run 10000000 |>.1.toOption == some [(0,4),(1,5),(2,2)]

end QleisliKernel.Tests.RuntimePureBody
