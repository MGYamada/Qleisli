import QleisliKernel

/-! Pure kernel regressions. Copyright 2026 Masahiko G. Yamada. Apache-2.0. -/

open QleisliKernel

namespace InterferenceTests
open QleisliKernel.Interference

example : Interference.normalize [.hadamard 0, .hadamard 0] = [] := by decide
example : Interference.normalize [.hadamard 0, .hadamard 1] =
    [.hadamard 0, .hadamard 1] := by decide
example : Interference.normalize [.hadamard 0, .hadamard 1, .hadamard 1, .hadamard 0] =
    [] := by decide
example : Interference.normalize [.diagonal [⟨[0], 16⟩, ⟨[0], 16⟩]] =
    [.diagonal [⟨[0], 32⟩]] := by decide +kernel
-- An unconditional half-turn must not disappear, even though probabilities agree.
example : Interference.normalize [.diagonal [⟨[], 128⟩]] =
    [.diagonal [⟨[], 128⟩]] := by decide +kernel
-- Invalid axes belong to the original IR validation, not this internal equality rule.
#guard Interference.normalize [.hadamard 1000000, .hadamard 1000000] == []
#guard Interference.normalize (List.replicate 4096 (.hadamard 15)) == []

end InterferenceTests

namespace QftTests

example : Qft.matchCircuit 1 [.hadamard 0] [0] = true := by decide
example : Qft.matchCircuit 0 [] [] = false := by decide
example : Qft.matchCircuit 9 [] [] = false := by decide
#guard Qft.matchCircuit 8 (Qft.template 8) (Qft.finalAxes 8)
#guard !(Qft.matchCircuit 3 (Qft.template 3) [0, 1, 2])
#guard !(Qft.matchCircuit 1 [.hadamard 1] [0])
#guard !(Qft.matchCircuit 2 [.hadamard 1, .diagonal [⟨[0, 1], 192⟩], .hadamard 0] [1, 0])
#guard (PathSum.compile 1 [.hadamard 0, .hadamard 0]).isSome
#guard (PathSum.compile 0 []).isSome
#guard (PathSum.compile 1 [.hadamard 1]).isNone
#guard (PathSum.compile 1 [.diagonal [⟨[0], 256⟩]]).isNone
#guard (PathSum.compile 1 [.diagonal [⟨[1], 16⟩]]).isNone

end QftTests

example : verify [] identitySummary identitySummary = true := by decide
example : verify [.x, .x] identitySummary identitySummary = true := by decide
example : verify [.phase 16, .phase 16] ⟨false, 0, 32⟩ ⟨false, 0, 32⟩ = true := by decide
example : verify [.phase 16, .phase 240] identitySummary identitySummary = true := by decide
example : verify [.phase 255, .phase 2] ⟨false, 0, 1⟩ ⟨false, 0, 1⟩ = true := by decide
example : verify [.x, .phase 16, .x, .phase 16] ⟨false, 16, 16⟩
    ⟨false, 16, 16⟩ = true := by decide
-- The same basis permutation and measurement probabilities are insufficient.
example : verify [.x, .phase 16, .x, .phase 16] ⟨false, 16, 16⟩
    identitySummary = false := by decide
-- Changing both circuit and provider claim cannot change the independent requirement.
example : verify [.x] ⟨true, 0, 0⟩ ⟨false, 0, 128⟩ = false := by decide
example : verify [.phase 16] ⟨false, 0, 32⟩ ⟨false, 0, 32⟩ = false := by decide
example : verify [.phase 32] ⟨false, 0, 32⟩ ⟨false, 0, 16⟩ = false := by decide
example : verify [.phase 256] identitySummary identitySummary = false := by decide
example : verify [] ⟨false, 0, 256⟩ ⟨false, 0, 256⟩ = false := by decide
example : verify [] identitySummary ⟨false, 256, 0⟩ = false := by decide
example : run [.x, .phase 16, .x, .phase 16] false 511 = ⟨false, 15⟩ := by decide
example : run [.x, .phase 16, .x, .phase 16] true 511 = ⟨true, 15⟩ := by decide

-- Exercise the native evaluator at the public word boundary; these are tests,
-- while verify_sound covers every accepted word independently of these cases.
#guard verify (List.replicate 4096 .x) identitySummary identitySummary
#guard !(verify (List.replicate 4097 .x) ⟨true, 0, 0⟩ ⟨true, 0, 0⟩)

open QleisliKernel.Dag QleisliKernel.Hierarchy

private def phaseLeaf (ticks : Nat) : Definition :=
  ⟨.bit, .leaf [.phase ticks], ⟨false, 0, ticks⟩⟩
private def identityRequest : Request := ⟨.bit, identitySummary⟩

#guard match check [phaseLeaf 16, ⟨.bit, .repeatOp 2 0, ⟨false, 0, 32⟩⟩]
    1 ⟨.bit, ⟨false, 0, 32⟩⟩ with
  | .ok stats => stats == ⟨2, 1, 26, 2, 2⟩
  | .error _ => false

#guard (check [phaseLeaf 16, ⟨.bit, .repeatOp 0 0, identitySummary⟩] 1 identityRequest).isOk
#guard !(check [phaseLeaf 256, ⟨.bit, .repeatOp 0 0, identitySummary⟩] 1 identityRequest).isOk
#guard !(check [⟨.bit, .repeatOp 0 0, identitySummary⟩] 0 identityRequest).isOk
#guard !(check [⟨.bit, .call 1 [0] [0], identitySummary⟩,
  ⟨.bit, .call 0 [0] [0], identitySummary⟩] 1 identityRequest).isOk
#guard !(check [phaseLeaf 32, ⟨.bit, .leaf [], identitySummary⟩] 1 identityRequest).isOk
#guard !(check [⟨.unit, .leaf [], identitySummary⟩,
  ⟨.bits0, .call 0 [0] [0], identitySummary⟩] 1 ⟨.bits0, identitySummary⟩).isOk
#guard (check [⟨.unit, .leaf [], identitySummary⟩,
  ⟨.unit, .call 0 [0] [0], identitySummary⟩] 1 ⟨.unit, identitySummary⟩).isOk
#guard !(check [⟨.unit, .leaf [], identitySummary⟩,
  ⟨.unit, .call 0 [] [], identitySummary⟩] 1 ⟨.unit, identitySummary⟩).isOk
-- The public pure API enforces aggregate work even without the byte-bounded decoder.
#guard match preflight (List.replicate 164
    ⟨.bit, .leaf (List.replicate 4096 .x), identitySummary⟩) 163 identityRequest with
  | .error failure => failure.kind == .limit
  | .ok _ => false

namespace LayoutTests
open QleisliKernel.Layout

private def ports : Interface := [⟨[.unit], []⟩, ⟨[.bit], [0]⟩,
  ⟨[.tuple 3, .bit, .unit, .bit], [1, 2]⟩]
private def moved : Rewire := ⟨ports,
  [⟨[.tuple 3, .bit, .unit, .bit], [0, 1]⟩, ⟨[.unit], []⟩, ⟨[.bit], [2]⟩],
  [2, 0, 1], [1, 2, 0]⟩
private def witness : Witness := ⟨[1, 2, 0], [2, 0, 1]⟩

example : basisWidth [.tuple 3, .bit, .unit, .bit] = some 2 := by decide
example : basisWidth [.tuple 2, .tuple 2, .bit, .unit, .bit] = some 2 := by decide
example : basisWidth [.tuple 1, .unit] = none := by decide
example : basisWidth [.unit, .unit] = none := by decide
example : basisWidth [.bits 9] = none := by decide
example : basisWidth [.bits 0] = some 0 := by decide
example : Layout.check moved witness moved = .ok ⟨3, 3, 12, 2888⟩ := by rfl
example : Layout.check moved ⟨[0, 1, 2], [2, 0, 1]⟩ moved = .error .invalidIr := by rfl
example : Layout.check {moved with owners := [2, 1]} witness moved = .error .invalidIr := by rfl
example : Layout.check moved witness {moved with axes := [0, 1, 2]} = .error .contract := by rfl

-- Width-zero is not an empty owner list; the pure API independently checks limits.
#guard (Layout.check ⟨[⟨[.unit], []⟩], [⟨[.unit], []⟩], [0], []⟩ ⟨[0], []⟩
  ⟨[⟨[.unit], []⟩], [⟨[.unit], []⟩], [0], []⟩).isOk
#guard !(Layout.check ⟨[⟨[.unit], []⟩], [], [], []⟩ ⟨[], []⟩
  ⟨[⟨[.unit], []⟩], [], [], []⟩).isOk
#guard match Layout.check {moved with inputs := List.replicate 65 ⟨[.unit], []⟩}
    witness moved with
  | .error .limit => true
  | _ => false
#guard match Layout.check moved {witness with inverseOwners := List.replicate 65 0} moved with
  | .error .limit => true
  | _ => false

end LayoutTests

namespace LayoutDagTests
open QleisliKernel.Layout QleisliKernel.LayoutDag

private def ports : Interface := [⟨[.bit], [0]⟩, ⟨[.bit], [1]⟩, ⟨[.unit], []⟩]
private def identity : Certified := ⟨⟨ports, ports, [0, 1, 2], [0, 1]⟩, ⟨[0, 1, 2], [0, 1]⟩⟩
private def swapped : Certified := ⟨⟨ports, ports, [1, 0, 2], [1, 0]⟩, ⟨[1, 0, 2], [1, 0]⟩⟩
private def shared : List LayoutDag.Definition := [⟨.leaf swapped.layout, swapped⟩,
  ⟨.call 0 identity identity, swapped⟩, ⟨.then 1 1, identity⟩]

#guard (LayoutDag.check shared 2 identity.layout).isOk
#guard !(LayoutDag.check shared 2 swapped.layout).isOk
#guard !(LayoutDag.check shared 1 swapped.layout).isOk -- No unreachable declarations.
#guard !(LayoutDag.check [⟨.leaf swapped.layout, swapped⟩,
  ⟨.call 1 identity identity, swapped⟩] 1 swapped.layout).isOk
#guard !(LayoutDag.check [⟨.leaf swapped.layout, identity⟩] 0 identity.layout).isOk
#guard !(LayoutDag.check [⟨.leaf swapped.layout, swapped⟩,
  ⟨.call 0 {identity with witness := ⟨[0, 0, 2], [0, 1]⟩} identity, swapped⟩]
  1 swapped.layout).isOk
-- Public API leaves cannot bypass the byte decoder's capacity checks or hide in claims.
#guard match LayoutDag.preflight [⟨.leaf {identity.layout with axes := List.replicate 17 0},
    identity⟩] 0 identity.layout with
  | .error failure => failure.kind == .limit
  | .ok _ => false
#guard match LayoutDag.preflight (List.replicate 257 ⟨.leaf identity.layout, identity⟩)
    0 identity.layout with
  | .error failure => failure.kind == .limit
  | .ok _ => false

end LayoutDagTests

namespace PhaseLayoutTests
open QleisliKernel.PhasePolynomial QleisliKernel.PhaseLayout

private def ports : Layout.Interface := [⟨[.bit], [0]⟩, ⟨[.bit], [1]⟩, ⟨[.unit], []⟩]
private def identity : LayoutDag.Certified :=
  ⟨⟨ports, ports, [0, 1, 2], [0, 1]⟩, ⟨[0, 1, 2], [0, 1]⟩⟩
private def swapped : LayoutDag.Certified :=
  ⟨⟨ports, ports, [1, 0, 2], [1, 0]⟩, ⟨[1, 0, 2], [1, 0]⟩⟩
private def first : PhaseLayout.Definition :=
  ⟨⟨.leaf swapped.layout, swapped⟩, [⟨[0], 16⟩, ⟨[], 7⟩], [⟨[], 7⟩, ⟨[0], 16⟩]⟩
private def expected : PhaseLayout.Summary :=
  ⟨identity.layout, [⟨[], 14⟩, ⟨[0], 16⟩, ⟨[1], 16⟩]⟩
private def second : PhaseLayout.Definition :=
  ⟨⟨.then 0 0, identity⟩, [], expected.phases⟩

example : PhasePolynomial.normalize [⟨[0], 16⟩, ⟨[], 7⟩, ⟨[0], 240⟩] = [⟨[], 7⟩] := by decide +kernel
example : PhasePolynomial.normalize [⟨[], 255⟩, ⟨[], 2⟩] = [⟨[], 1⟩] := by decide +kernel
example : remap (fun i => 1 - i) [⟨[0, 1], 16⟩] = [⟨[0, 1], 16⟩] := by
  simp [remap, List.mergeSort]
#guard (PhaseLayout.check [first, second] 1 expected).isOk
#guard !(PhaseLayout.check [first, second] 1 {expected with phases := [⟨[0], 16⟩, ⟨[1], 16⟩]}).isOk
#guard !(PhaseLayout.check [{first with claimedPhases := []}, second] 1 expected).isOk
#guard !(PhaseLayout.check [first, {second with sourcePhases := [⟨[], 0⟩]}] 1 expected).isOk
#guard !(PhaseLayout.check [{first with sourcePhases := [⟨[0, 0], 16⟩]}] 0 first.claim).isOk
#guard !(PhaseLayout.check [{first with sourcePhases := [⟨[0], 256⟩]}] 0 first.claim).isOk
-- Invalid axes are rejected before computing binary condition keys, even through the pure API.
#guard !(PhaseLayout.check [{first with claimedPhases := [⟨[1000000], 1⟩]}] 0 first.claim).isOk
#guard match PhaseLayout.preflight
    [{first with sourcePhases := List.replicate 129 ⟨[0], 1⟩}] 0 first.claim with
  | .error failure => failure.kind == .limit
  | .ok _ => false
#guard match PhaseLayout.preflight [first] 0
    {first.claim with phases := List.replicate 129 ⟨[0], 1⟩} with
  | .error failure => failure.kind == .limit
  | .ok _ => false

end PhaseLayoutTests

namespace QftGraphTests
open QleisliKernel.QftGraph

private def single : List QftGraph.Definition :=
  [⟨boundary 1, .gate (.hadamard 0)⟩, ⟨boundary 1, .permute [0]⟩,
   ⟨boundary 1, .sequence 0 1⟩]
example : (QftGraph.check single 2 1).isSome = true := by cbv
example : (QftGraph.check single 2 0).isSome = false := by cbv
example : (QftGraph.check single 2 9).isSome = false := by cbv
example : (QftGraph.check single 3 1).isSome = false := by cbv
example : (QftGraph.check (single ++ [⟨boundary 1, .identity⟩]) 2 1).isSome = false := by cbv
example : (QftGraph.check (single.set 2 ⟨boundary 1, .sequence 1 0⟩) 2 1).isSome = false := by cbv
example : (QftGraph.check (single.set 0 ⟨{boundary 1 with effect := .observe},
    .gate (.hadamard 0)⟩) 2 1).isSome = false := by cbv
example : (QftGraph.check (single.set 0 ⟨{boundary 1 with inputs := [⟨[.bit], [0]⟩]},
    .gate (.hadamard 0)⟩) 2 1).isSome = false := by cbv
example : (QftGraph.check (single.set 0 ⟨boundary 1, .call 2 (interface 1) (interface 1)⟩)
    2 1).isSome = false := by cbv
#guard !(QftGraph.preflight (List.replicate 257 ⟨boundary 1, .identity⟩) 0).isSome

end QftGraphTests

namespace QpeTests
open QleisliKernel

example : ControlledPowers.check 8 7 (ControlledPowers.template 8 7) = true := by cbv
example : ControlledPowers.check 0 7 [] = false := by cbv
example : ControlledPowers.check 9 7 [] = false := by cbv
example : ControlledPowers.check 1 7 [⟨0,7,0,true⟩] = false := by cbv
example : ControlledPowers.check 1 7 [⟨0,8,1,true⟩] = false := by cbv
example : ControlledPowers.check 1 7 [⟨0,7,1,false⟩] = false := by cbv
example : ControlledPowers.check 1 7 [⟨1,7,1,true⟩] = false := by cbv
example : ControlledPowers.maximumUses (ControlledPowers.template 8 7) = 255 := by
  have bound := ControlledPowers.maximumUses_template 8 7
  change ControlledPowers.maximumUses (ControlledPowers.template 8 7) + 1 = 256 at bound
  omega
example (choices : Interference.Bits) :
    (PathSum.runFrom (Uniform.word 8) choices Uniform.zero).phase = 0 := by
  rw [Uniform.run_word]; rfl

private def single : List QftGraph.Definition :=
  [⟨QftGraph.boundary 1, .gate (.hadamard 0)⟩, ⟨QftGraph.boundary 1, .permute [0]⟩,
   ⟨QftGraph.boundary 1, .sequence 0 1⟩]
private def plan : Qpe.Plan := ⟨Qpe.header 1 1, [false], [.hadamard 0], [⟨0,7,1,true⟩], single, 2⟩
example : (Qpe.check 1 1 7 plan).isSome = true := by cbv
example : (Qpe.check 1 1 8 plan).isSome = false := by cbv
example : (Qpe.check 1 1 7 {plan with precisionInitial := [true]}).isSome = false := by cbv
example : (Qpe.check 1 1 7 {plan with preparation := []}).isSome = false := by cbv
example : (Qpe.check 1 1 7 {plan with boundary := {plan.boundary with targetExit := .discard}}).isSome = false := by cbv
example : (Qpe.check 1 1 7 {plan with boundary := {plan.boundary with orientation := .forward}}).isSome = false := by cbv
example : (Qpe.check 1 1 7 {plan with boundary := {plan.boundary with classicalOutputs := [.bit]}}).isSome = false := by cbv
example : (Qpe.check 1 1 7 {plan with boundary := {plan.boundary with precisionOwner := 0}}).isSome = false := by cbv
example : (Qpe.check 1 1 7 {plan with boundary := {plan.boundary with precisionAxes := [0]}}).isSome = false := by cbv

end QpeTests

namespace SchemaTests
open QleisliKernel
private def proposal : Schema.Proposal :=
  ⟨"controlled-power/1", 1, [1,7], .power ⟨0,7,2,true⟩⟩
example : (Schema.check (.power 1 7) proposal).isSome = true := by decide
example : (Schema.check (.power 1 8) proposal).isSome = false := by cbv
example : (Schema.check (.power 1 7) {proposal with rule := "controlled-power/2"}).isSome = false := by cbv
example : (Schema.check (.power 1 7) {proposal with templateVersion := 2}).isSome = false := by cbv
example : (Schema.check (.power 1 7) {proposal with parameters := [1,7,0]}).isSome = false := by cbv
example : (Schema.check (.power 1 7) {proposal with witness := .power ⟨0,7,0,true⟩}).isSome = false := by decide
example : (Schema.check (.power 1 4294967296)
    ⟨"controlled-power/1",1,[1,4294967296],.power ⟨0,4294967296,2,true⟩⟩).isSome = false := by cbv
end SchemaTests

namespace HierarchicalGraphTests
open QleisliKernel.Hierarchical.Graph
example : (check #[[1], []] [0] #[1,0]).isOk = true := by cbv
example : (check #[[1], []] [0] #[0,1]).isOk = false := by cbv
example : (check #[[1], [0]] [0] #[1,0]).isOk = false := by cbv
example : (check #[[], []] [0] #[0,1]).isOk = false := by cbv
example : (check #[[], [0]] [1] #[0,0]).isOk = false := by cbv
end HierarchicalGraphTests

namespace HierarchicalArtifactTests
open QleisliKernel.Hierarchical
open Artifact

private def side : Side := ⟨#[⟨7,#[.bits 0],#[]⟩],#[]⟩
private def artifact : Artifact :=
  ⟨#[⟨⟨side,side⟩,.unitary,.rewire ⟨#[0],#[],#[]⟩⟩],
   #[⟨⟨side,side⟩,.identity⟩],#[⟨side,side,.identity⟩],
   #[⟨.equation,.rewire,#[],0,0,0,0,⟨1,#[],#[]⟩⟩],⟨0,0⟩⟩

example : index artifact ⟨.definition,1⟩ = none := by cbv
example : index artifact ⟨.meaning,0⟩ = some 1 := by cbv
example : (Body.repeatOp 0 9).references = #[⟨.definition,9⟩] := rfl
example : (prepare artifact #[0,1,2,3]).isOk = true := by decide +kernel
example : (prepare artifact #[3,0,1,2]).isOk = false := by cbv
example : (Graph.checkWithBudget #[[]] [0] #[0] 13).isOk = true := by cbv
example : (Graph.checkWithBudget #[[]] [0] #[0] 12).isOk = false := by cbv
example : (Ports.check side side ⟨#[0],#[],#[]⟩ 592).isOk = true := by decide +kernel
example : (Ports.check side side ⟨#[0],#[],#[]⟩ 591).isOk = false := by cbv
example : (Ports.check side side ⟨#[],#[],#[]⟩ 2000000).isOk = false := by cbv

end HierarchicalArtifactTests

namespace HierarchicalNodeTypingTests
open QleisliKernel.Hierarchical
open Artifact

private def side : Side := ⟨#[⟨0,#[.bit],#[0]⟩],#[]⟩
private def definition : Artifact.Definition := ⟨⟨side,side⟩,.unitary,.dyadicPhase 0 1 3⟩
private def data : Artifact := ⟨#[definition],#[],#[],#[],⟨0,0⟩⟩

example : NodeTyping.conditions data definition = true := by decide +kernel
example : NodeTyping.conditions data {definition with body := .dyadicPhase 1 1 3} = false := by cbv
example : (NodeTyping.check data 0 0).isOk = false := by cbv
example : NodeTyping.join .iso .observe = .observe := rfl

end HierarchicalNodeTypingTests

namespace HierarchicalContractTypingTests
open QleisliKernel.Hierarchical
open Artifact

private def side : Side := ⟨#[⟨0,#[.bits 1],#[0]⟩],#[]⟩
private def data : Artifact :=
  ⟨#[],#[⟨⟨side,side⟩,.qft 1⟩],#[⟨side,side,.identity⟩],#[],⟨0,0⟩⟩
example : (ContractTyping.check data ⟨.meaning,0⟩ 2000000).isOk = true := by decide +kernel
example : (ContractTyping.check data ⟨.encoding,0⟩ 2000000).isOk = true := by decide +kernel
example : (ContractTyping.check data ⟨.definition,0⟩ 2000000).isOk = false := by cbv
example : ContractTyping.meaningConditions data ⟨⟨side,side⟩,.phase 1 3⟩ = false := by cbv

end HierarchicalContractTypingTests

namespace HierarchicalStructuralTests
open QleisliKernel.Hierarchical
open Artifact
private def split : Interface :=
  ⟨⟨#[⟨0,#[.bits 1],#[7]⟩],#[]⟩,
    ⟨#[⟨1,#[.bit],#[7]⟩,⟨2,#[.bits 0],#[]⟩],#[]⟩⟩
example : (Structural.check (.takeBit 1 0) split 888).isOk = true := by decide +kernel
example : (Structural.check (.takeBit 1 0) split 887).isOk = false := by cbv
example : (Structural.check (.putBit 1 0) (Structural.swapped split) 888).isOk = true := by decide +kernel
example : (Structural.check (.takeBit 1 1) split 2000000).isOk = false := by cbv
example : (Structural.check .packEmptyBits ⟨⟨#[],#[]⟩,⟨#[⟨0,#[.bits 0],#[]⟩],#[]⟩⟩ 2000000).isOk = true := by decide +kernel
end HierarchicalStructuralTests

namespace CoherentPowerTests
open QleisliKernel
private def rotate (_ : Nat) (z : Int × Int) : Int × Int := (-z.2,z.1)
private def controls (bit : Bool) (axis : Nat) : Bool := axis == 0 && bit
private def state (_ : Bool) : Int × Int := (1,0)
example : ControlledPowers.coherentStage rotate controls state ⟨0,7,2,true⟩ false = (1,0) := by cbv
example : ControlledPowers.coherentStage rotate controls state ⟨0,7,2,true⟩ true = (-1,0) := by cbv
example : ControlledPowers.coherentRun rotate controls (ControlledPowers.template 1 7) state true = (0,1) := by cbv
end CoherentPowerTests

namespace HierarchicalPowerTests
open QleisliKernel.Hierarchical
open Artifact
private def target : Side := ⟨#[⟨0,#[.bits 1],#[7]⟩],#[]⟩
private def full : Side := ⟨#[⟨1,#[.bit],#[8]⟩,⟨0,#[.bits 1],#[7]⟩],#[]⟩
private def data : Artifact :=
  {definitions := #[⟨⟨target,target⟩,.unitary,.rewire ⟨#[0],#[0],#[]⟩⟩,
                    ⟨⟨target,target⟩,.unitary,.repeatOp 2 0⟩,
                    ⟨⟨full,full⟩,.unitary,.control 1 true⟩]
   meanings := #[⟨⟨target,target⟩,.identity⟩,⟨⟨target,target⟩,.power 0 2⟩,⟨⟨full,full⟩,.control 1 true⟩]
   encodings := #[⟨target,target,.identity⟩,⟨full,full,.identity⟩]
   proofs := #[⟨.equation,.rewire,#[],0,0,0,0,⟨1,#[],#[]⟩⟩,
               ⟨.equation,.schema "controlled-power/1",#[0],2,2,1,1,⟨1,#[1,0],#[]⟩⟩]
   entry := ⟨2,1⟩}
example : Power.implementationStage data 2 = some ⟨0,0,2,true⟩ := by cbv
example : (Power.inspect data 1 1 0 15633).isOk = true := by decide +kernel
example : (Power.inspect data 1 1 0 15632).isOk = false := by cbv
example : (Power.inspect data 1 0 0 2000000).isOk = false := by decide +kernel
example : (Power.inspect data 1 1 1 2000000).isOk = false := by decide +kernel
example : (Derivation.checkAll data (Array.range 10)).isOk = true := by decide +kernel
example : (Derivation.powerEntry data (Array.range 10) 1 0).isOk = true := by decide +kernel
example : (Derivation.powerEntry data (Array.range 10) 0 0).isOk = false := by decide +kernel
private def falseProvider : Artifact :=
  {data with proofs := data.proofs.mapIdx (fun i p => if i==0 then {p with rule := .finite} else p)}
example : (Power.inspect falseProvider 1 1 0 2000000).isOk = true := by decide +kernel
example : (Derivation.checkAll falseProvider (Array.range 10)).isOk = false := by decide +kernel
end HierarchicalPowerTests

-- Focused reshape sentinels complement the audit of every compiled declaration.
-- Future size-normalization/bit-segment theorems need their own sentinels when implemented.
/-- info: 'QleisliKernel.Reshape.check_encoding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms QleisliKernel.Reshape.check_encoding

/-- info: 'QleisliKernel.Reshape.check_reference_coefficients' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms QleisliKernel.Reshape.check_reference_coefficients
