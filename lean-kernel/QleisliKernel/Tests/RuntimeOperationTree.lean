import QleisliKernel.Qirf.RuntimePreparedArm

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
private def z : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[.pure (.gate .z 0 1)],[1],[],.unitary⟩
private def identity : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[],[0],[],.unitary⟩
private def erased : Semantics.Observation.Program := ⟨[⟨0,[0],1⟩],[],[.pure (.applyUnitary 0 1 [])],[1],[],.unitary⟩
private def selected : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩,⟨1,[1],1⟩],[],[.pure (.quantumIf 0 1 2 3 [] [])],[2,3],[],.unitary⟩

private inductive Fault where
  | none | falseMeaning | dormantFalse | omittedFirst | omittedSecond | missing | extra
  deriving BEq

private def controlPresent {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderPaths.Checked artifact context description graph index request header root demand) : Bool :=
  match checked.paths with
  | .forwardOnly .. => false
  | .transformed _ _ _ _ _ _ _ controlled _ => controlled.isSome

private abbrev Summary := List Nat × List (Nat × Bool × Bool) × List Nat × Bool

private def inspect (fault : Fault) : WorkM Summary := do
  let text := if fault == .falseMeaning then falseSource else if fault == .dormantFalse then dormantSource else source
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
  let second ← RuntimePreparedArm.prepare artifact original.catalogue table secondIndex providers [[reference]]
  let rows := original.signature.sourceRows ++ body.summary.staticRows ++ call.target.sourceRows ++ first.rows ++ second.rows
  let roots := (artifact.root :: first.roots ++ second.roots).eraseDups
  let order := if omitted then #[0,1,2,3] else #[0,1,2]
  let root ← Validity.checkRootFromRoots artifact order rows roots
  let checked ← RuntimePreparedArm.read second root
  match checked with
  | .constructed _ actual _ =>
    let providers := actual.outcome.records.filterMap fun record =>
      match record.checked.provider with
      | .absent _ => none
      | .present _ _ checked _ => some (record.occurrence.index,record.demand.controllable,controlPresent checked.paths)
    let subjects := actual.outcome.records.filterMap fun record =>
      match record.checked.requirements with
      | .none .. => none
      | .requested child .. => some child.index
    let identity ← lift (arithmetic (Exact.Matrix.identity 2))
    return (actual.outcome.records.map (·.occurrence.index),providers,subjects,decide (actual.action = identity))
  | _ => throw .request

-- One initial calibrated whole-study budget; every call includes original
-- discovery, actual caller supplies, headers, one graph and both provider bodies.
private def run (fault : Fault) := ((inspect fault).run 26000000).1

#guard (run .none).toOption == some ([0,1,2,3,4],[(0,true,true),(1,true,true)],[3],true)
#guard [Fault.falseMeaning,.dormantFalse,.omittedFirst,.omittedSecond].all fun fault =>
  match run fault with | .error .equation => true | _ => false
#guard [Fault.missing,.extra].all fun fault =>
  match run fault with | .error .request => true | _ => false

end QleisliKernel.Tests.RuntimeOperationTree
