import QleisliKernel.Qirf.RuntimeSelectionMeaning

/-! One original two-arm selection checked against its literal interval, arm
programs, controlled implementations and independent Meaning in the same
dependency graph. The relative phase control has the same Gram matrix.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeSelectionMeaning
open QleisliKernel Finite SourceTypes Qirf
private def source : String := "#![no_implicit_prelude]\nunitary fn keep(q:Q<Bit>)->Q<Bit>{q}\nunitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\nmeaning Sign:Bit=reference(sign);\npub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qmatch(s,q){0=>keep,1=>checked_op(sign,Sign)}}\n"
private def wrongSource := source.replace "reference(sign)" "reference(keep)"
private def port (token wire : Nat) : Semantics.Raw.Port := ⟨token,[wire],1⟩
private def single (sign : Bool) : Semantics.Observation.Program :=
  ⟨[port 0 0],[],if sign then [.pure (.gate .z 0 1)] else [],[if sign then 1 else 0],[],.unitary⟩
private def select (one : List Semantics.Raw.UnitaryStep) : Semantics.Observation.Program :=
  ⟨[port 0 0,port 1 1],[],[.pure (.quantumIf 0 1 2 3 [] one)],[2,3],[],.unitary⟩
private def iface : Semantics.CarrierInterface.Interface :=
  ⟨[⟨port 0 0,[.bit]⟩,⟨port 1 1,[.bit]⟩],[⟨port 2 0,[.bit]⟩,⟨port 3 1,[.bit]⟩],.unitary⟩

private inductive Fault where
  | none | reversed | falseMeaning | omitted | relativePhase | staleControl | swappedArms | staleReturn | omittedRoot
  deriving BEq

private def controlPresent {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderPaths.Checked artifact context description graph index request header root demand) : Bool :=
  match checked.paths with
  | .forwardOnly .. => false
  | .transformed _ _ _ _ _ _ _ controlled _ => controlled.isSome

private def control {artifact catalogue owner name offset selector target table index implementations references prepared root}
    (checked : @RuntimePreparedArm.Checked artifact catalogue owner name offset selector target table index implementations references prepared root) : Bool :=
  match checked with
  | .plain _ actual _ => controlPresent actual.subject.paths
  | .requested _ actual _ => controlPresent actual.subject.paths

private def inspect (fault : Fault) (onlyPrepare : Bool := false) : WorkM (List Nat) := do
  let z := [.gate .z 0]
  let actual := match fault with | .omitted => [] | .relativePhase => .phase .minusOne :: z | _ => z
  let text := match fault with
    | .falseMeaning => wrongSource
    | .reversed => source.replace "0=>keep,1=>checked_op(sign,Sign)" "1=>checked_op(sign,Sign),0=>keep"
    | _ => source
  let artifact : Artifact := ⟨#[select actual,single false,select [],single true,
    select (if fault == .staleControl then [] else z),single (fault != .falseMeaning)],
    #[],#[("main",text)],0,none⟩
  let original ← RuntimeBodyDiscovery.prepareSource artifact "main" "route" {}
  let empty : RuntimeContextRequest.Context := .mk [] [] [] [] []
  let phase : RuntimeContextRequest.Context := .mk [⟨95,0,1⟩] [] [] [] []
  let pos : SourceSequence.Position := ⟨201,0,1⟩
  let arms : List RuntimeContextRequest.Arm := [⟨1,2⟩,⟨3,4⟩]
  let site : RuntimeContextRequest.Site := ⟨iface,iface,pos,if fault == .swappedArms || fault == .reversed then arms.reverse else arms⟩
  let providers : List RuntimeProviderHeader.Request := [(.pure 1,empty),(.pure 3,phase)]
  let ctx : RuntimeContextRequest.Context := .mk [pos] [site] [] []
    (if fault == .reversed then providers.reverse else providers)
  let references : List (List (List RuntimeProviderHeader.Request)) :=
    [[],[[(.pure 5,if fault == .falseMeaning then empty else phase)]]]
  let prepared ← RuntimeSelectionMeaning.prepare original ctx (if fault == .reversed then references.reverse else references)
  if onlyPrepare then return prepared.roots
  let tree := Semantics.RuntimeType.owner [.bit]
  let out0 := port (if fault == .staleReturn then 3 else 2) 0
  let runtime : RuntimeFamily.Request := ⟨.exported,"main","route",[tree,tree],
    [[.quantum ⟨port 0 0,[.bit]⟩],[.quantum ⟨port 1 1,[.bit]⟩]],[[]],Semantics.RuntimeType.tuple 2 [tree,tree],
    [.tuple 2,.quantum ⟨out0,[.bit]⟩,.quantum ⟨port 3 1,[.bit]⟩],.unitary,{}⟩
  let order := if fault == .omittedRoot then #[0,1,2,3,4] else #[0,1,2,3,4,5]
  let checked ← RuntimeSelectionMeaning.read prepared order runtime
  guard (checked.reverseArms.all fun arm => arm.2.checked.demand.controllable && control arm.2.checked) .request
  return checked.reverseArms.reverse.map (fun arm => arm.1.prepared.label) ++
    checked.returned.finalBindings.map (·.port.token)

private def run (fault : Fault) := ((inspect fault).run 10000000).1

#guard ((inspect .none true).run 10000000).1.toOption == some [0,1,2,3,4,5]
#guard (run .none).toOption == some [0,1,2,3]
#guard (run .reversed).toOption == some [1,0,2,3]
#guard [Fault.falseMeaning,.omitted,.relativePhase,.staleControl,.swappedArms].all fun fault =>
  match run fault with | .error .equation => true | _ => false
#guard run .staleReturn matches .error .request
#guard run .omittedRoot matches .error .invalid

end QleisliKernel.Tests.RuntimeSelectionMeaning
