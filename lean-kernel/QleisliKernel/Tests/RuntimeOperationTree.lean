import QleisliKernel.Qirf.RuntimePreparedArm
import QleisliKernel.Qirf.RuntimeOperationOccurrenceTree

/-! The original caller supplies then_op(sign,sign). Its complete action is
identity and each leaf realizes Z. The indexed arm requires an actual
controlled implementation at each occurrence. The negative cases exercise
a false Meaning under a zero power and changes to either provider body.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOperationTree
open QleisliKernel Finite SourceTypes Qirf

private def source : String := r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Identity:Bit=reference(keep);
meaning Sign:Bit=reference(sign);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {
    qmatch(s,q){0=>keep,1=>checked_op(U,Identity)}
}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    choose[then_op(sign,sign)](s,q)
}
"#

private def falseSource := source.replace "checked_op(U,Identity)" "checked_op(U,Sign)"
private def dormantSource := source.replace "checked_op(U,Identity)" "power(checked_op(U,Sign),0)"
private def dormantCorrectSource := source.replace "checked_op(U,Identity)" "power(checked_op(U,Identity),0)"
private def pairSource (first second : String) := source.replace "checked_op(U,Identity)"
  ("then_op(checked_op(U," ++ first ++ "),checked_op(U," ++ second ++ "))")
private def formalSource (meaning : String) :=
  let withFormals := source.replace "const U:Op<Bit>" ("const V:Op<Bit>,const U:Op<Bit," ++ meaning ++ ">")
  withFormals.replace "choose[then_op(sign,sign)]" "choose[sign,then_op(sign,sign)]"
private def z : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[.pure (.gate .z 0 1)],[1],[],.unitary⟩
private def identity : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩
private def erased : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[.pure (.applyUnitary 0 1 [])],[1],[],.unitary⟩
private def selected : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.quantumIf 0 1 2 3 [] [])],[2,3],[],.unitary⟩

private inductive Fault where
  | none | falseMeaning | dormantFalse | dormantTrue | omittedFirst | omittedSecond | missing | extra
  | pair | pairWrongFirst | pairWrongSecond
  | formalArgument | wrongFormalArgument
  deriving BEq

private def controlPresent {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderPaths.Checked artifact context description graph index request header root demand) : Bool :=
  match checked.paths with
  | .forwardOnly .. => false
  | .transformed _ _ _ _ _ _ _ controlled _ => controlled.isSome

private abbrev Summary := List Nat × List (Nat × Bool × Bool) × List Nat × Bool

private def inspect (fault : Fault) : WorkM Summary := do
  let pair := fault == .pair || fault == .pairWrongFirst || fault == .pairWrongSecond
  let formal := fault == .formalArgument || fault == .wrongFormalArgument
  let text := if formal then formalSource (if fault == .wrongFormalArgument then "Sign" else "Identity")
    else if pair then
      pairSource (if fault == .pairWrongFirst then "Sign" else "Identity")
        (if fault == .pairWrongSecond then "Sign" else "Identity")
    else if fault == .falseMeaning then falseSource else if fault == .dormantFalse then dormantSource
    else if fault == .dormantTrue then dormantCorrectSource else source
  let omitted := fault == .omittedFirst || fault == .omittedSecond
  let programs := if omitted then #[selected,z,identity,erased] else #[selected,z,identity]
  let artifact : Artifact := ⟨programs,#[],#[("main",text)],0,none⟩
  let original ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let [.named call] := original.body.checked.events | throw .request
  let callee ← SourceRuntimeTrace.readNamedBody call
  let body := callee.checked
  let [.selection _ parsed _ selector target scope naturals ..] := body.events | throw .request
  let table ← QuantumArms.readArmsWithInstantiation body.signature.original body.signature.instantiation
    body.signature.supply parsed.keyword.span.startByte selector.basis target.basis (some naturals) scope
  let [firstIndex,secondIndex] := List.finRange table.arms.length | throw .request
  let some sign := original.catalogue.records.find? (fun body => body.name == "sign") | throw .request
  let some token := sign.definition.original.envelope.occurrence.body.head? | throw .request
  let empty : RuntimeContextRequest.Context := .mk [] [] [] [] []
  let phase : RuntimeContextRequest.Context := .mk [⟨token.span.startByte,0,1⟩] [] [] [] []
  let first ← RuntimePreparedArm.prepare artifact original.catalogue table firstIndex [(.pure 2,empty)] []
  let wrong := fault == .falseMeaning || fault == .dormantFalse
  let reference : RuntimeProviderHeader.Request := if wrong then (.pure 1,phase) else (.pure 2,empty)
  let providers : List RuntimeProviderHeader.Request :=
    [(.pure (if fault == .omittedFirst then 3 else 1),phase),
     (.pure (if fault == .omittedSecond then 3 else 1),phase)]
  let providers := if fault == .missing then providers.take 1 else if fault == .extra then providers ++ [(.pure 1,phase)] else providers
  let providers := if pair then providers ++ providers else providers
  let providers := if formal then (.pure 1,phase) :: providers else providers
  let references := if formal then
      [[if fault == .wrongFormalArgument then (.pure 1,phase) else (.pure 2,empty)],[reference]]
    else if pair then
      [[if fault == .pairWrongFirst then (.pure 1,phase) else (.pure 2,empty)],
       [if fault == .pairWrongSecond then (.pure 1,phase) else (.pure 2,empty)]]
    else [[reference]]
  let second ← RuntimePreparedArm.prepare artifact original.catalogue table secondIndex providers references
  let rows := original.signature.sourceRows ++ body.summary.staticRows ++ call.target.sourceRows ++ first.rows ++ second.rows
  let roots := (artifact.root :: first.roots ++ second.roots).eraseDups
  let order := if omitted then #[0,1,2,3] else #[0,1,2]
  let root ← Validity.checkRootFromRoots artifact order rows roots
  let checked ← RuntimePreparedArm.read second root
  match checked with
  | .constructed _ actual _ markers _ =>
    if fault == .none then
      let tree := markers.tree
      let initial := Sigma.mk tree.index tree.tree
      -- Use the actual production association's tree and original marker,
      -- rather than building an independent diagnostic traversal.
      let first ← RuntimeOperationOccurrenceTree.follow initial [.child 0,.actual 0,.child 0]
      let second ← RuntimeOperationOccurrenceTree.follow initial [.child 0,.actual 0,.child 1]
      guard (first.2.located.occurrence.ordinal.val == 0 &&
        second.2.located.occurrence.ordinal.val == 1) .request
      guard (first.2.located.occurrence.index == 0 && second.2.located.occurrence.index == 1) .request
      let [entry] := markers.entries | throw .request
      let marker := markers.markers[entry.index.val]'entry.index.isLt
      guard (marker.tokens.head?.map (·.span.startByte) == some 325) .request
      guard (entry.target.2.located.position.val == 4 && entry.assertion.binding.index.val == 4 &&
        entry.assertion.child.index == 3 && entry.assertion.requirement.index.val == 0) .request
      guard (entry.assertion.requirement.request.declarationName == "Identity") .request
    if fault == .pair then
      -- Equal requests must retain both original occurrences. The offsets
      -- come from the preserved two-equal .qli; positions follow both edges.
      guard (markers.entries.map (·.target.2.located.position.val) == [4,9] &&
        markers.entries.map (·.assertion.binding.index.val) == [4,9]) .request
      let offsets := markers.entries.map fun entry =>
        (markers.markers[entry.index.val]'entry.index.isLt).tokens.head?.map (·.span.startByte)
      guard (offsets == [some 333,some 356]) .request
    if fault == .dormantTrue then
      let [entry] := markers.entries | throw .request
      let marker := markers.markers[entry.index.val]'entry.index.isLt
      guard (marker.path == [.child 0] &&
        marker.tokens.head?.map (·.span.startByte) == some 331) .request
      guard (entry.target.2.located.position.val == 4 && entry.assertion.binding.index.val == 4) .request
    if formal then
      let slots := actual.outcome.records.flatMap fun record =>
        match record.checked.requirements with
        | .arguments _ meanings _ => meanings.map (·.slot)
        | _ => []
      guard (slots == [1]) .request
    let providers := actual.outcome.records.filterMap fun record =>
      match record.checked.provider with
      | .absent _ => none
      | .present _ _ checked _ => some (record.occurrence.index,record.demand.controllable,controlPresent checked.paths)
    let subjects := actual.outcome.records.filterMap fun record =>
      match record.checked.requirements with
      | .none .. | .arguments .. => none
      | .requested child .. => some child.index
    let identity ← lift (arithmetic (Exact.Matrix.identity 2))
    return (actual.outcome.records.map (·.occurrence.index),providers,subjects,decide (actual.action = identity))
  | _ => throw .request

-- One initial calibrated whole-study budget; every call includes original
-- discovery, actual caller supplies, headers, one graph and both provider bodies.
private def run (fault : Fault) := ((inspect fault).run 16000000).1

#guard (run .none).toOption == some ([0,1,2,3,4],[(0,true,true),(1,true,true)],[3],true)
#guard [Fault.falseMeaning,.dormantFalse,.omittedFirst,.omittedSecond].all fun fault =>
  match run fault with | .error .equation => true | _ => false
#guard [Fault.missing,.extra].all fun fault =>
  match run fault with | .error .request => true | _ => false

-- First whole-study budget for the new assertion experiments is the
-- production 20M cap; the original sixteen-million controls stay unchanged.
private def productionRun (fault : Fault) := ((inspect fault).run 20000000).1
#guard (productionRun .pair).toOption.map (fun (order,providers,subjects,identity) =>
  (order.length,providers.length,subjects.length,identity)) == some (11,4,2,true)
#guard [Fault.pairWrongFirst,.pairWrongSecond].all fun fault =>
  match productionRun fault with | .error .equation => true | _ => false
#guard (productionRun .formalArgument).toOption.map (fun (_,_,_,identity) => identity) == some true
#guard (match productionRun .wrongFormalArgument with | .error .equation => true | _ => false)
#guard (productionRun .dormantTrue).toOption.map (fun (order,providers,subjects,identity) =>
  (order.length,providers.length,subjects.length,identity)) == some (6,2,1,true)

end QleisliKernel.Tests.RuntimeOperationTree
