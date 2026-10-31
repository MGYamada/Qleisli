import QleisliKernel
import QleisliKernel.Tests.FiniteRestriction
import QleisliKernel.Tests.RawSector
import QleisliKernel.Tests.QirfSector
import QleisliKernel.Tests.ComputedSectors
import QleisliKernel.Tests.NominalSector
import QleisliKernel.Tests.SectorArms
import QleisliKernel.Tests.SourceQuantum
import QleisliKernel.Tests.SourceEntries
import QleisliKernel.Tests.QuantumMoves
import QleisliKernel.Tests.QuantumBody
import QleisliKernel.Tests.QuantumSequence
import QleisliKernel.Tests.RawOwnerFlow
import QleisliKernel.Tests.PureInterval
import QleisliKernel.Tests.SourceSequence
import QleisliKernel.Tests.SequenceSector
import QleisliKernel.Tests.CallSyntaxTests
import QleisliKernel.Tests.StatementSyntaxTests
import QleisliKernel.Tests.SourceLookupTests
import QleisliKernel.Tests.CallNameTests
import QleisliKernel.Tests.SourceContextTests
import QleisliKernel.Tests.SourceTraceTests
import QleisliKernel.Tests.SourceTraceCacheTests
import QleisliKernel.Tests.PrimitiveActionTests
import QleisliKernel.Tests.RawTraceTests
import QleisliKernel.Tests.OwnerBoundariesTests
import QleisliKernel.Tests.ContextSectorTests
import QleisliKernel.Tests.ContextSectorCost
import QleisliKernel.Tests.RawTraceCost
import QleisliKernel.Tests.RawTraceMeterTests
import QleisliKernel.Tests.CallCoordinateTests
import QleisliKernel.Tests.PreparedIntervalTests
import QleisliKernel.Tests.SequenceSectorSharingTests
import QleisliKernel.Tests.ContextIntervalContinuity
import QleisliKernel.Tests.OriginalSelectionContinuity
import QleisliKernel.Tests.RawTraceMeterContinuity
import QleisliKernel.Tests.RuntimeSignature
import QleisliKernel.Tests.RuntimeStaticHeader
import QleisliKernel.Tests.RuntimeStorage
import QleisliKernel.Tests.RuntimeCode
import QleisliKernel.Tests.RuntimeFamily
import Protocol.ExecutionView.CheckedQmatch
import QleisliKernel.Tests.SourceMembers
import QleisliKernel.Tests.OrdinaryInputs
import QleisliKernel.Qirf.ControlAccess
import Protocol.NativeContext.Bindings

/-! Pure kernel regressions. Copyright 2026 Qleisli Project Contributors. Apache-2.0. -/

open QleisliKernel

namespace IsometryVocabularyTests

-- Use the real public aliases in exhaustive patterns. Historical constructor
-- spellings below test compatibility; they are not a second canonical name.
namespace Raw
open QleisliKernel.Semantics.Raw
private def classify : Effect → Nat
  | .unitary => 0
  | .isometry => 1
  | .observe => 2
example : Effect.isometry = Effect.iso := rfl
example : classify .iso = 1 := rfl
example : classify .isometry = 1 := rfl
example : classify .unitary = 0 := rfl
example : classify .observe = 2 := rfl
end Raw

namespace Hierarchical
open QleisliKernel.Hierarchical.Artifact
private def classify : Effect → Nat
  | .unitary => 0
  | .isometry => 1
  | .observe => 2
example : Effect.isometry = Effect.iso := rfl
example : classify .iso = 1 := rfl
example : classify .isometry = 1 := rfl
example : classify .unitary = 0 := rfl
example : classify .observe = 2 := rfl
end Hierarchical

namespace QftGraph
open QleisliKernel.QftGraph
private def classify : Effect → Nat
  | .unitary => 0
  | .isometry => 1
  | .observe => 2
example : Effect.isometry = Effect.iso := rfl
example : classify .iso = 1 := rfl
example : classify .isometry = 1 := rfl
example : classify .unitary = 0 := rfl
example : classify .observe = 2 := rfl
end QftGraph

end IsometryVocabularyTests

namespace RawUnitTests
open QleisliKernel.Raw

-- One suspended physical owner, one empty owner and a consumed identity.
private def frame : Raw.State :=
  ⟨[⟨7,[3],1⟩,⟨8,[],0⟩],[7,8,5],[3],[3],true⟩

example : (Unit.pack {} 0).map (fun t => (t.state,t.events)) =
    .ok (⟨[⟨0,[],0⟩],[0],[],[],false⟩,[]) := by cbv
example : Unit.pack frame 5 = .error .invalid := by rfl
example : Unit.pack frame 7 = .error .invalid := by rfl
example : Unit.pack frame 4294967296 = .error .invalid := by rfl
example : Unit.unpack frame 7 = .error .invalid := by rfl
example : Unit.unpack frame 5 = .error .invalid := by rfl
example : (Unit.unpack frame 8).map (fun t => (t.state,t.events)) =
    .ok (⟨[⟨7,[3],1⟩],[7,8,5],[3],[3],true⟩,[]) := by cbv
example : ((Unit.pack frame 9).bind (fun t => Unit.unpack t.state 9)).map (·.state) =
    .ok {frame with seenTokens := [7,8,5,9]} := by cbv
-- An empty wire list never justifies an invalid recorded bit count.
example : Unit.unpack ⟨[⟨0,[],1⟩],[0],[],[],false⟩ 0 = .error .invalid := by rfl

-- The real dispatcher, including globally issued empty owners.
example : (Raw.dispatch [] frame (.packUnit 9)).map (fun t => (t.state,t.events)) =
    .ok (⟨[⟨7,[3],1⟩,⟨8,[],0⟩,⟨9,[],0⟩],[7,8,5,9],[3],[3],true⟩,[]) := by cbv
example : Raw.dispatch [] frame (.packUnit 5) = .error .invalid := by rfl
example : Raw.dispatch [] frame (.unpackUnit 7) = .error .invalid := by rfl
example : (Raw.dispatch [] frame (.unpackUnit 8)).map (·.state) =
    .ok (⟨[⟨7,[3],1⟩],[7,8,5],[3],[3],true⟩) := by cbv
example : (Raw.prepare [] ⟨[],[.packUnit 0,.unpackUnit 0],[],.unitary⟩).map (·.state.iso) =
    .ok false := by cbv
example : Raw.prepare [] ⟨[],[.packUnit 0,.unpackUnit 0,.packUnit 0],[0],.unitary⟩ =
    .error .invalid := by rfl
example : Raw.prepare [] ⟨[],[.packUnit 0,.unpackUnit 0,.unpackUnit 0],[],.unitary⟩ =
    .error .invalid := by rfl

end RawUnitTests

namespace ExactTests
open QleisliKernel.Semantics.Exact QleisliKernel.Exact

example : Coefficient.make 8 3 = .ok (.integer 1) := by cbv
example : Coefficient.make 0 4294967295 = .ok (.integer 0) := by cbv
example : Coefficient.make 1 127 = .error .arithmeticCapacity := by cbv
example : Coefficient.make 2 127 = .ok ⟨1, 126⟩ := by cbv
example : Coefficient.neg ⟨-(2 ^ 127), 0⟩ = .error .arithmeticCapacity := by cbv
example : (charge 3).run 2 = (.error .workLimit, 2) := by cbv
example : (charge 3).run 4 = (.ok (), 1) := by cbv
example : Scalar.phase 4 ≠ Scalar.one := by decide
example : Matrix.identity 0 = .error .dimension := by cbv

end ExactTests

namespace ControlAccessTests
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Observation QleisliKernel.Qirf

-- These original bodies pass graph, ownership, interface and reconstruction
-- checks. No proposed matrix or producer acceptance flag is supplied.
private def body (bits : Nat) (steps : List Step) : Program :=
  ⟨[⟨0,List.range bits,bits⟩],[],[.pure (.applyUnitary 0 1 steps)],
    [1],[],.unitary⟩

private def original (signature : Basis) (steps : List Step) : Qirf.Artifact :=
  ⟨#[body (width signature) steps],#[],#[],0,some (signature,signature)⟩

private def accepts (artifact : Qirf.Artifact) (signature : Basis) (axes : List Nat) : Bool :=
  ((Qirf.ControlAccess.check artifact #[0] signature axes).run 2000000).1.isOk

private def pair : Basis := [.pair,.bit,.bit]
private def cnot : List Step := [⟨[],.monomial [0,1] [0,3,2,1] [0,0,0,0]⟩]
private def phase : List Step := [⟨[],.monomial [0,1] [0,1,2,3] [0,0,0,4]⟩]

example : accepts (original pair cnot) pair [0] = true := by decide +kernel
-- The target sector changes even though the complete operation is unitary.
example : accepts (original pair cnot) pair [1] = false := by decide +kernel
example : accepts (original pair phase) pair [0,1] = true := by decide +kernel
example : accepts (original [.bit] [⟨[],.hadamard 0⟩]) [.bit] [0] = false := by decide +kernel
example : accepts (original pair cnot) pair [0,0] = false := by decide +kernel
example : accepts (original pair cnot) pair [2] = false := by decide +kernel
example : accepts (original pair cnot) [.bits 2] [0] = false := by decide +kernel
-- A quantum Unit retains its logical owner and exact nontrivial phase.
example : accepts (original [.unit] [⟨[],.monomial [] [0] [4]⟩]) [.unit] [] = true := by decide +kernel
example : accepts {(original pair cnot) with root := 1} pair [0] = false := by decide +kernel
example : accepts {(original pair cnot) with programs := #[body 2 [⟨[],.hadamard 0⟩]]}
    pair [0] = false := by decide +kernel

-- A closed dependency is freshly checked against its original specification.
private def dependency (implementation : List Step) : Qirf.Artifact :=
  ⟨#[body 2 implementation,body 2 cnot,body 2 [⟨[],.contract [0,1] 0 false⟩]],
    #[⟨pair,0,.circuit 1,"implementation","specification",[]⟩],#[],2,some (pair,pair)⟩
example : ((Qirf.ControlAccess.check (dependency cnot) #[0,1,3,2] pair [0]).run 2000000).1.isOk = true :=
  by decide +kernel
example : ((Qirf.ControlAccess.check (dependency [⟨[],.hadamard 0⟩]) #[0,1,3,2] pair [0]).run 2000000).1.isOk = false :=
  by decide +kernel
example : ((Qirf.ControlAccess.check (original pair cnot) #[0] pair [0]).run 0).1.isOk = false := by cbv
example : ((Qirf.ControlAccess.check (original pair cnot) #[] pair [0]).run 2000000).1.isOk = false := by decide +kernel

-- Matrix cardinality and coordinate checks precede the sector traversal.
example : ((Qirf.ControlAccess.checkMatrix 1 ⟨2,2,[]⟩ [0]).run 2000000).1.isOk = false := by cbv
example : ((Qirf.ControlAccess.checkMatrix 0 ⟨1,1,[Scalar.one]⟩ [0]).run 2000000).1.isOk = false := by cbv

-- Multi-owner checks retain original ports; no packing wrapper is constructed.
private def separateCnot : Qirf.Artifact :=
  ⟨#[⟨[⟨0,[7],1⟩,⟨1,[19],1⟩],[],[.pure (.cnot 0 1 2 3)],
    [2,3],[],.unitary⟩],#[],#[],0,none⟩
private def acceptsOwners (artifact : Qirf.Artifact) (signatures : List Basis)
    (axes : List Nat) : Bool :=
  ((Qirf.ControlAccess.checkOwners artifact #[0] signatures axes).run 2000000).1.isOk
example : acceptsOwners separateCnot [[.bit],[.bit]] [0] = true := by decide +kernel
example : acceptsOwners separateCnot [[.bit],[.bit]] [1] = false := by decide +kernel
example : acceptsOwners separateCnot [[.bit],[.bit]] [0,0] = false := by decide +kernel
example : acceptsOwners separateCnot [[.bit],[.bit]] [2] = false := by decide +kernel
example : acceptsOwners separateCnot [[.pair,.bit,.bit]] [0] = false := by decide +kernel
example : acceptsOwners separateCnot [[.unit],[.bits 2]] [0] = false := by decide +kernel
example : acceptsOwners separateCnot [] [0] = false := by decide +kernel
example : acceptsOwners {separateCnot with programs :=
    #[⟨[⟨0,[7],1⟩,⟨1,[19],1⟩],[],[.pure (.cnot 0 1 2 3)],
      [3,2],[],.unitary⟩]} [[.bit],[.bit]] [0] = false := by decide +kernel
example : acceptsOwners {separateCnot with rootInterface := some (pair,pair)}
    [[.bit],[.bit]] [0] = false := by decide +kernel
example : acceptsOwners {separateCnot with programs :=
    #[⟨[⟨0,[7],1⟩,⟨1,[19],1⟩],[],[.pure (.gate .h 0 2)],
      [2,1],[],.unitary⟩]} [[.bit],[.bit]] [0] = false := by decide +kernel
-- Logical zero-width owners and their ordered partition are retained.
private def unitControl : Qirf.Artifact :=
  ⟨#[⟨[⟨0,[],0⟩,⟨1,[19],1⟩],[],
    [.pure (.applyUnitary 0 2 [⟨[],.monomial [] [0] [4]⟩])],
    [2,1],[],.unitary⟩],#[],#[],0,none⟩
example : acceptsOwners unitControl [[.unit],[.bit]] [] = true := by decide +kernel
example : acceptsOwners unitControl [[.bit],[.unit]] [] = false := by decide +kernel
example : acceptsOwners {unitControl with programs :=
    #[⟨[⟨0,[],0⟩,⟨1,[19],1⟩],[],
      [.pure (.applyUnitary 0 2 [⟨[],.monomial [] [0] [4]⟩])],
      [1,2],[],.unitary⟩]} [[.unit],[.bit]] [] = false := by decide +kernel
example : ((Qirf.ControlAccess.checkOwners separateCnot #[0] [[.bit],[.bit]] [0]).run 0).1.isOk = false := by cbv

end ControlAccessTests

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
example : Qft.matchCompiledCircuit 2
    [.hadamard 1, .diagonal [⟨[0, 1], 32⟩, ⟨[0, 1], 32⟩], .hadamard 0]
    [1, 0] = true := by cbv
example : Qft.matchCompiledCircuit 2
    [.hadamard 1, .diagonal [⟨[0, 1], 192⟩], .hadamard 0]
    [1, 0] = false := by cbv
example : Qft.matchCompiledCircuit 2 (Qft.template 2) [0, 1] = false := by cbv
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

namespace RawPureTests
open QleisliKernel.Semantics.Raw
private def identity (bits : Nat) : Program :=
  ⟨[⟨0,List.range bits,bits⟩],[],[0],.unitary⟩
-- These inspect metadata only: no maximum-size quantum matrix is generated.
example : (QleisliKernel.Raw.prepare [] (identity 12)).isOk = true := by decide +kernel
example : (QleisliKernel.Raw.prepare [] (identity 13)).isOk = false := by decide +kernel
example : (QleisliKernel.Raw.prepare []
  ⟨[⟨0,List.range 12,12⟩,⟨1,(List.range 12).map (·+12),12⟩],[],[1,0],.unitary⟩).isOk = true := by decide +kernel
example : (QleisliKernel.Raw.prepare [] ⟨[⟨0,[],0⟩,⟨1,[],0⟩],[],[0],.unitary⟩).isOk = false := by decide +kernel
example : (QleisliKernel.Raw.prepare [] ⟨[⟨0,[],0⟩,⟨1,[],0⟩],[],[1,0],.unitary⟩).isOk = true := by decide +kernel
example : (QleisliKernel.Raw.prepare [] ⟨[],[.init0 0 1],[0],.unitary⟩).isOk = false := by decide +kernel
example : (QleisliKernel.Raw.prepare [] ⟨[⟨0,[0],1⟩],[.gate .h 0 0],[0],.unitary⟩).isOk = false := by decide +kernel
example : (QleisliKernel.Raw.eventMatrix [] (.init0 4294967295)).run 0 = (.error .limit,0) := by rfl
example : (QleisliKernel.Raw.eventMatrix [] (.circuit 4294967295 [])).run 0 = (.error .limit,0) := by rfl
example : (QleisliKernel.Raw.eventMatrix [] (.protectedComputed 12 (List.range 12) 12 1 [] [])).run 0 = (.error .limit,0) := by rfl

-- A controlled scalar on Unit must remain visible on the control qubit.
private def controlledUnitPhase : Program :=
  ⟨[⟨0,[17],1⟩,⟨1,[],0⟩],[.quantumIf 0 1 2 3 [] [.phase .minusOne]],[3,2],.unitary⟩
example : QleisliKernel.Semantics.RawTrace.run controlledUnitPhase =
    some ⟨⟨[⟨2,[17],1⟩,⟨3,[],0⟩],[17]⟩,
      [.circuit 1 [⟨[⟨0,true⟩],.monomial [] [0] [4]⟩],.reorder 1 [0]],1⟩ := by decide +kernel
example : (match (QleisliKernel.Raw.reconstruct [] controlledUnitPhase).run 100000 with
    | (.error _,_) => false
    | (.ok matrix,_) => (matrix.rows,matrix.cols,matrix.entries) ==
      (2,2,[QleisliKernel.Semantics.Exact.Scalar.one,.zero,.zero,
        ⟨.integer (-1),.integer 0,.integer 0,.integer 0⟩])) = true := by decide +kernel

-- Splitting and an empty owner do not erase final output-coordinate order.
private def reorderedSplit : Program :=
  ⟨[⟨5,[9,4],2⟩,⟨0,[],0⟩],[.split 5 1 2 1],[2,0,1],.unitary⟩
example : (QleisliKernel.Semantics.RawTrace.run reorderedSplit).map (·.events) =
    some [.reorder 2 [1,0]] := by decide +kernel
example : (match (QleisliKernel.Raw.reconstruct [] reorderedSplit).run 100000 with
    | (.error _,_) => false
    | (.ok matrix,_) => ((List.range 4).map fun column =>
        (List.range 4).filter fun row => matrix.entry row column == QleisliKernel.Semantics.Exact.Scalar.one) ==
      [[0],[2],[1],[3]]) = true := by decide +kernel

-- Original-trace refinement is independent of the six-bit dense profile.
example : (match QleisliKernel.Raw.prepare [] (identity 12) with
    | .error _ => false
    | .ok prepared => QleisliKernel.Semantics.RawTrace.run (identity 12) == some prepared.reference) = true := by decide +kernel
end RawPureTests

namespace RawObservationTests
open QleisliKernel.Semantics.Observation
-- Fast append-only histories and the old membership fallback agree even on
-- reordered/duplicate identities; scope pairs must remain exactly equal.
example : Raw.Observation.historySubset ([] : List Nat) [1] = true := by decide
example : Raw.Observation.historySubset [1,2] [1,2,3] = true := by decide
example : Raw.Observation.historySubset [1,2] [2,1,3] = true := by decide
example : Raw.Observation.historySubset [1,1] [1] = true := by decide
example : Raw.Observation.historySubset [1,2] [1,3] = false := by decide
example : Raw.Observation.historySubset [(1,0),(2,1)] [(2,1),(1,0)] = true := by decide
example : Raw.Observation.historySubset [(1,0)] [(1,1)] = false := by decide
private def nested : Nat → List Op
  | 0 => []
  | n+1 => [.branch 0 (nested n) [] [] []]
private def program (depth : Nat) : Program :=
  ⟨[],[0],nested depth,[],[0],.unitary⟩
private def accepts (value : Program) : Bool :=
  match (QleisliKernel.Raw.Observation.verify [] value).run 1000000 with
  | (.ok _,_) => true
  | _ => false
-- Depth and owner sentinels inspect structure only; no quantum matrices.
example : accepts (program 64) = true := by decide +kernel
example : accepts (program 65) = false := by decide +kernel
example : accepts ⟨[⟨0,[],0⟩],[0],[.branch 0 [] [] [] []],[],[],.unitary⟩ = false := by decide +kernel
example : accepts ⟨[⟨0,[],0⟩],[0],
    [.branch 0 [] [] [⟨0,0,1,[]⟩] []],[1],[],.unitary⟩ = true := by decide +kernel
end RawObservationTests


/- Bounded engineering arithmetic regressions only; these issue no program,
Meaning, capability, cleanup, resource or constitutional acceptance. -/
namespace EngineeringArithmeticTests
open QleisliKernel.Semantics.Exact QleisliKernel.Engineering.Pure

private def id2 : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩
private def diagonal (phase : Int) : Matrix :=
  ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,QleisliKernel.Exact.Scalar.phase phase]⟩
private def scalarMatrix (phase : Int) : Matrix := ⟨1,1,[QleisliKernel.Exact.Scalar.phase phase]⟩
private def budget : Coefficient := ⟨7,3⟩
private def succeeds (a u : Matrix) (e : Coefficient) (work : Nat := 200000) : Bool :=
  ((checkMatrices a u e).run work).1.isOk

-- The seven independently recorded exact host cases.
example : succeeds (diagonal 1) id2 budget = true := by decide +kernel
example : succeeds (diagonal 1) id2 ⟨1,1⟩ = false := by decide +kernel
example : succeeds (diagonal 7) (diagonal 1) budget = false := by decide +kernel
example : succeeds (scalarMatrix 4) (scalarMatrix 0) (.integer 1) = false := by decide +kernel
example : succeeds (diagonal 1) (diagonal 1) (.integer 0) = true := by decide +kernel
private def tensorT : Matrix := ⟨4,4,[
  Scalar.one,Scalar.zero,Scalar.zero,Scalar.zero,
  Scalar.zero,QleisliKernel.Exact.Scalar.phase 1,Scalar.zero,Scalar.zero,
  Scalar.zero,Scalar.zero,Scalar.one,Scalar.zero,
  Scalar.zero,Scalar.zero,Scalar.zero,QleisliKernel.Exact.Scalar.phase 1]⟩
private def id4 : Matrix := ⟨4,4,[
  Scalar.one,Scalar.zero,Scalar.zero,Scalar.zero,
  Scalar.zero,Scalar.one,Scalar.zero,Scalar.zero,
  Scalar.zero,Scalar.zero,Scalar.one,Scalar.zero,
  Scalar.zero,Scalar.zero,Scalar.zero,Scalar.one]⟩
example : succeeds tensorT id4 budget = false := by decide +kernel
example : succeeds (diagonal 2) id2 ⟨7,2⟩ = true := by decide +kernel

-- Rectangular acceptance and shape rejection, without maximum-size cases.
private def prepare0 : Matrix := ⟨2,1,[Scalar.one,Scalar.zero]⟩
private def phasedPrepare : Matrix := ⟨2,1,[QleisliKernel.Exact.Scalar.phase 1,Scalar.zero]⟩
example : succeeds prepare0 prepare0 (.integer 0) = true := by decide +kernel
example : succeeds phasedPrepare prepare0 budget = true := by decide +kernel
example : succeeds prepare0 ⟨1,2,[Scalar.one,Scalar.zero]⟩ budget = false := by decide +kernel

-- Malformed inputs, too-small complex-phase bounds, invalid precision and work fail closed.
example : succeeds ⟨2,2,[Scalar.one]⟩ id2 budget = false := by decide +kernel
example : succeeds ⟨0,1,[]⟩ (scalarMatrix 0) budget = false := by decide +kernel
example : succeeds ⟨1,1,[⟨⟨2,1⟩,.integer 0,.integer 0,.integer 0⟩]⟩
    (scalarMatrix 0) budget = false := by decide +kernel
example : succeeds (scalarMatrix 2) (scalarMatrix 0) (.integer 1) = false := by decide +kernel
example : succeeds id2 id2 (.integer (-1)) = false := by decide +kernel
example : succeeds id2 id2 ⟨2,1⟩ = false := by decide +kernel
example : succeeds id2 id2 (.integer (2^100)) = false := by decide +kernel
example : succeeds id2 id2 (.integer 0) 0 = false := by decide +kernel
example : succeeds id2 id2 (.integer 0) 10000001 = true := by decide +kernel
private def signResult (a b : Coefficient) : Option Bool :=
  match realNonneg a b with | .ok answer => some answer | .error _ => none
example : signResult (.integer 1) (.integer (-1)) = some false := by decide +kernel
example : signResult (.integer (-1)) (.integer 1) = some true := by decide +kernel
example : (match realNonneg (.integer (2^100)) (.integer (-1)) with
    | .error .arithmeticCapacity => true | _ => false) = true := by decide +kernel


end EngineeringArithmeticTests


namespace EngineeringArtifactTests
open QleisliKernel QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Observation QleisliKernel.Qirf.EngineeringPure

private def identityMatrix : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩
private def phaseMatrix (exponent : Nat) : Matrix :=
  ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,QleisliKernel.Exact.Scalar.phase exponent]⟩
private def body (steps : List Step) : Program :=
  ⟨[⟨0,[0],1⟩],[],[.pure (.applyUnitary 0 1 steps)],[1],[],.unitary⟩
private def original (basis : Basis) (steps : List Step) : Qirf.Artifact :=
  ⟨#[body steps],#[],#[],0,some (basis,basis)⟩
private def phaseSteps (exponent : Nat) : List Step :=
  [⟨[],.monomial [0] [0,1] [0,exponent]⟩]
private def leaf (basis : Basis) (steps : List Step) (required : Matrix) : LeafRequest :=
  ⟨original basis steps,#[0],⟨0,[0],1⟩,⟨1,[0],1⟩,required⟩
private def compare : QleisliKernel.Qirf.EngineeringPure.Request :=
  ⟨[.bit],[.bit],leaf [.bit] [] identityMatrix,
    leaf [.bit] (phaseSteps 1) (phaseMatrix 1),⟨7,3⟩⟩
private def accepts (request : QleisliKernel.Qirf.EngineeringPure.Request)
    (work : Nat := 2000000) : Bool :=
  ((QleisliKernel.Qirf.EngineeringPure.check request).run work).1.isOk

-- I versus T has squared Frobenius error 2-sqrt(2); 7/8 is sufficient.
example : accepts compare = true := by decide +kernel
-- An exact equality case still returns the engineering-only Checked type.
example : accepts {compare with ideal := compare.actual,epsilon := ⟨0,0⟩} = true := by decide +kernel
example : accepts {compare with epsilon := ⟨1,1⟩} = false := by decide +kernel
-- T-dagger is valid against its own exact request, but differs from T by more
-- than the same 7/8 engineering budget. Standalone validity is insufficient.
example : ((Qirf.PureLeaf.check (original [.bit] (phaseSteps 7)) #[0]
    [.bit] [.bit] ⟨0,[0],1⟩ ⟨1,[0],1⟩ (phaseMatrix 7)).run 2000000).1.isOk = true :=
  by decide +kernel
example : accepts {compare with actual := leaf [.bit] (phaseSteps 7) (phaseMatrix 7)} = false :=
  by decide +kernel
-- The original T body cannot be paired with an identity matrix assertion.
example : accepts {compare with ideal := {compare.ideal with required := identityMatrix}} = false :=
  by decide +kernel
-- Changing a body cannot reuse its old requested matrix even at a loose bound.
example : accepts {compare with ideal :=
    {compare.ideal with artifact := original [.bit] (phaseSteps 7)}} = false := by decide +kernel
example : accepts {compare with actual :=
    {compare.actual with output := ⟨1,[1],1⟩}} = false := by decide +kernel
-- Bits<1> and Bit each have width one and valid separate exact leaves. Their
-- full root interfaces cannot satisfy the same common Basis request.
example : ((Qirf.PureLeaf.check (original [.bits 1] []) #[0]
    [.bits 1] [.bits 1] ⟨0,[0],1⟩ ⟨1,[0],1⟩ identityMatrix).run 2000000).1.isOk = true :=
  by decide +kernel
example : accepts {compare with ideal := leaf [.bits 1] [] identityMatrix} = false := by decide +kernel
private def hiddenBody (effect : QleisliKernel.Semantics.Raw.Effect) : Program :=
  ⟨[⟨0,[0],1⟩],[],[.measure 0 0,.pure (.init0 1 1)],[1],[],effect⟩
private def hiddenObserve : Qirf.Artifact :=
  ⟨#[hiddenBody .unitary],#[],#[],0,none⟩
-- Measurement is internal: no public classical output exposes the false pure
-- label. Correcting only the effect makes ordinary native root validity pass.
private def correctlyObserving : Qirf.Artifact :=
  {hiddenObserve with programs := hiddenObserve.programs.map fun program =>
    {program with effect := .observe}}
-- Effect checking itself detects hidden observation before any port-interface
-- gate or pure matrix reconstruction. All three have the identical body.
example : ((Raw.Observation.verify [] (hiddenBody .observe)).run 2000000).1.isOk = true :=
  by decide +kernel
example : ((Raw.Observation.verify [] (hiddenBody .unitary)).run 2000000).1.isOk = false :=
  by decide +kernel
example : ((Raw.Observation.verify [] (hiddenBody .iso)).run 2000000).1.isOk = false :=
  by decide +kernel
example : ((Qirf.Validity.checkRoot correctlyObserving #[0]).run 2000000).1.isOk = true :=
  by decide +kernel
example : ((Qirf.Validity.checkRoot hiddenObserve #[0]).run 2000000).1.isOk = false :=
  by decide +kernel
-- Pure-leaf candidates additionally assert their full quantum Basis interface;
-- their rejection cannot be supplied merely by a missing pure root interface.
private def pureHiddenObserve : Qirf.Artifact :=
  {hiddenObserve with rootInterface := some ([.bit],[.bit])}
example : accepts {compare with actual :=
    {compare.actual with artifact := pureHiddenObserve,output := ⟨1,[1],1⟩}} = false := by decide +kernel
private def falselyIsometric : Qirf.Artifact :=
  {hiddenObserve with programs := hiddenObserve.programs.map fun program =>
    {program with effect := .iso}}
example : ((Qirf.Validity.checkRoot falselyIsometric #[0]).run 2000000).1.isOk = false :=
  by decide +kernel
private def pureFalselyIsometric : Qirf.Artifact :=
  {falselyIsometric with rootInterface := some ([.bit],[.bit])}
example : accepts {compare with actual :=
    {compare.actual with artifact := pureFalselyIsometric,output := ⟨1,[1],1⟩}} = false := by decide +kernel
example : accepts compare 0 = false := by decide +kernel
example : accepts {compare with actual := {compare.actual with order := #[]}} = false :=
  by decide +kernel

-- A genuine rectangular Unit -> Bit preparation uses distinct common ports.
private def preparation : Qirf.Artifact :=
  ⟨#[⟨[⟨0,[],0⟩],[],[.pure (.unpackUnit 0),.pure (.init0 1 0)],[1],[],.iso⟩],
    #[],#[],0,some ([.unit],[.bit])⟩
private def preparedLeaf : LeafRequest :=
  ⟨preparation,#[0],⟨0,[],0⟩,⟨1,[0],1⟩,⟨2,1,[Scalar.one,Scalar.zero]⟩⟩
private def rectangular : QleisliKernel.Qirf.EngineeringPure.Request :=
  ⟨[.unit],[.bit],preparedLeaf,preparedLeaf,⟨0,0⟩⟩
example : accepts rectangular = true := by decide +kernel
example : accepts {rectangular with codomain := [.bits 1]} = false := by decide +kernel

end EngineeringArtifactTests

/- Complete instrument engineering checks are separate from exact equality,
pure capabilities, cleanup, resource evidence and native/public acceptance. -/
namespace EngineeringInstrumentTests
open QleisliKernel.Semantics.Exact QleisliKernel.Engineering.Instrument

private def oneCell (value : Scalar) : Matrix := ⟨1,1,[value]⟩
private def half : Scalar := ⟨⟨1,1⟩,.integer 0,.integer 0,.integer 0⟩
private def actualUnit : List Raw.InstrumentEquality.History :=
  [⟨[false],oneCell half⟩,⟨[false],oneCell half⟩,
   ⟨[false],oneCell half⟩,⟨[true],oneCell half⟩]
private def idealUnit : List Raw.InstrumentEquality.History :=
  [⟨[false],oneCell Scalar.one⟩,⟨[true],oneCell Scalar.zero⟩]
private def quarter : Coefficient := ⟨1,2⟩
private def acceptsUnit (epsilon : Coefficient) (majorants : List Coefficient)
    (work : Nat := 2000000) : Bool :=
  ((checkHistories 1 1 1 actualUnit idealUnit epsilon majorants).run work).1.isOk

-- Unnormalized branch probabilities are 3/4 and 1/4, against 1 and 0.
-- The independently predicted sufficient bound is 1/2, not a squared budget.
example : acceptsUnit ⟨1,1⟩ [quarter,quarter] = true := by decide +kernel
example : acceptsUnit quarter [quarter,quarter] = false := by decide +kernel
example : acceptsUnit ⟨1,1⟩ [quarter,.integer 0] = false := by decide +kernel
example : acceptsUnit (.integer 0) [.integer 0,.integer 0] = false := by decide +kernel
example : acceptsUnit (.integer 2) [quarter] = false := by decide +kernel
example : acceptsUnit (.integer 2) [quarter,quarter,quarter] = false := by decide +kernel
example : acceptsUnit (.integer 2) [⟨2,3⟩,quarter] = false := by decide +kernel
example : acceptsUnit (.integer 2) [.integer (-1),quarter] = false := by decide +kernel
example : acceptsUnit (.integer (-1)) [quarter,quarter] = false := by decide +kernel
example : acceptsUnit ⟨0,1⟩ [quarter,quarter] = false := by decide +kernel
example : acceptsUnit (.integer (2^126)) [.integer (2^126),quarter] = false := by decide +kernel
example : acceptsUnit ⟨1,1⟩ [quarter,quarter] 0 = false := by decide +kernel

-- All four coordinates matter. The two off-diagonal Choi coefficients of T
-- differ from identity by conjugate nonreal values, each bounded by 7/8.
private def id2 : Matrix := ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.one]⟩
private def t : Matrix :=
  ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,QleisliKernel.Exact.Scalar.phase 1]⟩
private def phaseMajorants (budget : Coefficient) : List Coefficient :=
  (cells 2 2 [[false]]).map fun cell =>
    if (cell.row == 0 && cell.col == 0 && cell.otherRow == 1 && cell.otherCol == 1) ||
       (cell.row == 1 && cell.col == 1 && cell.otherRow == 0 && cell.otherCol == 0)
    then budget else .integer 0
private def phaseAccepts (budget epsilon : Coefficient) : Bool :=
  ((checkHistories 2 2 1 [⟨[false],t⟩] [⟨[false],id2⟩]
      epsilon (phaseMajorants budget)).run 2000000).1.isOk
example : phaseAccepts ⟨7,3⟩ ⟨7,2⟩ = true := by decide +kernel
example : phaseAccepts ⟨1,1⟩ ⟨7,2⟩ = false := by decide +kernel
example : phaseAccepts ⟨7,3⟩ ⟨7,3⟩ = false := by decide +kernel
private def minusId : Matrix := ⟨2,2,[
  QleisliKernel.Exact.Scalar.phase 4,Scalar.zero,Scalar.zero,QleisliKernel.Exact.Scalar.phase 4]⟩
-- Equal instruments may have different pure global phases: this success
-- supplies no pure phase agreement or coherent-control permission.
example : ((checkHistories 2 2 1 [⟨[false],minusId⟩] [⟨[false],id2⟩]
    (.integer 0) (List.replicate 16 (.integer 0))).run 2000000).1.isOk = true := by decide +kernel
private def halfId : Matrix := ⟨2,2,[half,Scalar.zero,Scalar.zero,half]⟩
private def residualActual : List Raw.InstrumentEquality.History :=
  [⟨[false],halfId⟩,⟨[false],halfId⟩,⟨[false],halfId⟩,⟨[true],halfId⟩]
private def residualMajorants : List Coefficient :=
  (cells 2 2 [[false],[true]]).map fun cell =>
    if cell.row == cell.col && cell.otherRow == cell.otherCol then quarter else .integer 0
-- Every residual density-matrix coordinate remains present. This sufficient
-- coefficient bound is conservative: its sum is 2, while the exact norm is 1/2.
example : ((checkHistories 2 2 1 residualActual [⟨[false],id2⟩]
    (.integer 2) residualMajorants).run 2000000).1.isOk = true := by decide +kernel
example : ((checkHistories 2 2 1 residualActual [⟨[false],id2⟩]
    (.integer 1) residualMajorants).run 2000000).1.isOk = false := by decide +kernel
private def resetHistories : List Raw.InstrumentEquality.History :=
  [⟨[false],⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Scalar.zero]⟩⟩,
   ⟨[false],⟨2,2,[Scalar.zero,Scalar.one,Scalar.zero,Scalar.zero]⟩⟩]
-- Reset and identity both return false with probability one; an entangled
-- input distinguishes their residual channels, so zero distance must refuse.
example : ((checkHistories 2 2 1 resetHistories [⟨[false],id2⟩]
    (.integer 0) (List.replicate 16 (.integer 0))).run 2000000).1.isOk = false := by decide +kernel
-- Invalid matrices, public labels, and omitted/impossible outcomes refuse.
example : ((checkHistories 1 1 1 [] idealUnit (.integer 2) [quarter,quarter]).run 2000000).1.isOk =
    false := by decide +kernel
example : ((checkHistories 1 1 1 [⟨[],oneCell half⟩] idealUnit (.integer 2) [quarter,quarter]).run
    2000000).1.isOk = false := by decide +kernel
example : ((checkHistories 1 1 1 [⟨[false],⟨1,1,[]⟩⟩] idealUnit (.integer 2) [quarter,quarter]).run
    2000000).1.isOk = false := by decide +kernel

open QleisliKernel.Semantics.Observation
private def randomBody : Program := ⟨[⟨0,[],0⟩],[],
  [.pure (.unpackUnit 0),.pure (.init0 1 1),.pure (.gate .h 1 2),.measure 2 0,
   .pure (.init0 3 2),.pure (.gate .h 3 4),.measure 4 1,.and 0 1 2],[],[2],.observe⟩
private def falseBody : Program := ⟨[⟨0,[],0⟩],[],
  [.pure (.unpackUnit 0),.pure (.init0 1 1),.measure 1 2],[],[2],.observe⟩
private def artifact (body : Program) : Qirf.Artifact := ⟨#[body],#[],#[],0,none⟩
private def request : Qirf.EngineeringInstrument.Request :=
  ⟨artifact randomBody,#[0],artifact falseBody,#[0],⟨[.unit],[.bit]⟩,
    ⟨[.unit],[.bit]⟩,⟨"actual","ideal",[]⟩,⟨1,1⟩,[quarter,quarter]⟩
private def originalAccepts (value : Qirf.EngineeringInstrument.Request) : Bool :=
  ((Qirf.EngineeringInstrument.check value).run 2000000).1.isOk
example : originalAccepts request = true := by decide +kernel
example : originalAccepts {request with epsilon := quarter} = false := by decide +kernel
example : originalAccepts {request with expectedSignature := ⟨[.bits 0],[.bit]⟩} = false := by decide +kernel
example : originalAccepts {request with expectedSignature := ⟨[.unit],[.bits 1]⟩} = false := by decide +kernel
example : originalAccepts {request with actualOrder := #[]} = false := by decide +kernel
example : originalAccepts {request with actual := artifact {randomBody with effect := .unitary}} =
    false := by decide +kernel
example : originalAccepts {request with actual := artifact {randomBody with effect := .iso}} =
    false := by decide +kernel
example : originalAccepts {request with actual := artifact {randomBody with operations := randomBody.operations.drop 1}} =
    false := by decide +kernel
-- The unchanged exact gate still rejects this nonzero difference.
example : ((Qirf.InstrumentContract.check request.actual request.actualOrder request.expected
    request.expectedOrder request.actualSignature request.expectedSignature request.identity).run
    2000000).1.isOk = false := by decide +kernel
end EngineeringInstrumentTests


/-! Small executable carrier/encoding regressions for #64. These do not check
source syntax, original-body equations, qmatch, protocol integration or ownership.
The largest generated matrix is 8x6 (three physical bits), below the six-bit
finite profile; rejected huge widths never enumerate a code.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace FiniteCarrierExamples
open QleisliKernel.Semantics.FiniteCarrier QleisliKernel.Semantics.Exact

deriving instance DecidableEq for Except

def origin : Origin := ⟨"labels","Tri","pub enum Tri { A, B, C }"⟩
def tri : Basis := [.enumeration origin ["A","B","C"]]
def four : Basis := [.enumeration ⟨"labels","Four","pub enum Four { A, B, C, D }"⟩ ["A","B","C","D"]]
def emptyRecord : Basis := [.record ⟨"labels","Empty","pub struct Empty {}"⟩ []]
def one : Basis := [.enumeration ⟨"labels","One","pub enum One { Only }"⟩ ["Only"]]

def value {α : Type} (action : QleisliKernel.Finite.WorkM α) := (action.run 1000000).1

example : layout tri = some ⟨2,[0,1,2]⟩ := by decide
example : layout four = some ⟨2,[0,1,2,3]⟩ := by decide
example : dimension tri = some 3 ∧ dimension four = some 4 := by decide

def embedding : Matrix := ⟨4,3,([1,0,0, 0,1,0, 0,0,1, 0,0,0] : List Int).map fun n =>
  ⟨.integer n,.integer 0,.integer 0,.integer 0⟩⟩

example : value (QleisliKernel.FiniteCarrier.code tri) = .ok embedding := by decide
example : ((QleisliKernel.Exact.Matrix.isometryWork embedding).run 1000000).1 = .ok true := by decide

-- Complete nominal trees stay distinct even when physical matrices coincide.
def reordered : Basis := [.enumeration origin ["B","A","C"]]
example : tri ≠ reordered := by decide
example : layout tri = layout reordered := by decide
example : one ≠ [.unit] ∧ one ≠ [.bits 0] ∧ one ≠ emptyRecord := by decide
example : layout one = some singleton ∧ layout emptyRecord = some singleton := by decide
example : value (QleisliKernel.FiniteCarrier.code emptyRecord) = .ok ⟨1,1,[Scalar.one]⟩ := by decide

def record : Basis :=
  .record ⟨"labels","Tagged","pub struct Tagged { tag: Tri, flag: Bit }"⟩ ["tag","flag"] :: tri ++ [.bit]
def reversedRecord : Basis :=
  [.record ⟨"labels","Reversed","pub struct Reversed { flag: Bit, tag: Tri }"⟩ ["flag","tag"],.bit] ++ tri

example : layout record = some ⟨3,[0,1,2,4,5,6]⟩ := by decide
example : dimension record = some 6 := by decide
example : layout reversedRecord = some ⟨3,[0,1,2,3,4,5]⟩ := by decide
example : layout record ≠ layout reversedRecord := by decide
example : value (QleisliKernel.FiniteCarrier.code record) =
    .ok (encoding ⟨3,[0,1,2,4,5,6]⟩) := by decide +kernel

example : value (QleisliKernel.FiniteCarrier.read [.enumeration origin []]) = .error .invalid := by decide
example : value (QleisliKernel.FiniteCarrier.read [.enumeration origin ["A","A"]]) = .error .invalid := by decide
example : value (QleisliKernel.FiniteCarrier.read [.record origin ["a","b"],.bit]) = .error .invalid := by decide
example : value (QleisliKernel.FiniteCarrier.read [.tuple 1,.bit]) = .error .invalid := by decide
example : value (QleisliKernel.FiniteCarrier.read [.bits 100000]) = .error .limit := by decide
example : ((QleisliKernel.FiniteCarrier.read tri).run 0).1 =
    .error (.arithmetic .workLimit) := by decide

#print axioms QleisliKernel.FiniteCarrier.read_reference
#print axioms QleisliKernel.FiniteCarrier.code_conditions

end FiniteCarrierExamples

/-! Original-body equations on proper finite code spaces; no native or source
API is enabled. Largest new physical matrix: 4x4 (two bits).
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace CarrierBodyExamples
open QleisliKernel QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.CarrierInterface QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Observation

private def matrix (rows cols : Nat) (values : List Int) : Matrix :=
  ⟨rows,cols,values.map fun n => ⟨.integer n,.integer 0,.integer 0,.integer 0⟩⟩
private def cycle : Matrix := matrix 3 3 [0,0,1, 1,0,0, 0,1,0]
private def identity3 : Matrix := matrix 3 3 [1,0,0, 0,1,0, 0,0,1]
private def input : Owner := ⟨⟨0,[7,19],2⟩,FiniteCarrierExamples.tri⟩
private def output : Owner := ⟨⟨1,[7,19],2⟩,FiniteCarrierExamples.tri⟩
private def interface : Interface := ⟨[input],[output],.unitary⟩
private def body (steps : List Step) : Program :=
  ⟨[input.port],[],[.pure (.applyUnitary 0 1 steps)],[1],[],.unitary⟩
private def step (axes permutation phases : List Nat) : List Step :=
  [⟨[],.monomial axes permutation phases⟩]
private def cycleSteps : List Step := step [0,1] [1,2,0,3] [0,0,0,0]
private def artifact (steps : List Step) : Qirf.Artifact :=
  ⟨#[body steps],#[],#[],0,none⟩
private def accepts (data : Qirf.Artifact) (attached required : Interface)
    (logical : Matrix) (order : Array Nat := #[0]) (work : Nat := 2000000) : Bool :=
  ((Qirf.Carrier.check data order attached required logical).run work).1.isOk

example : accepts (artifact cycleSteps) interface interface cycle = true := by decide +kernel
example : accepts (artifact []) interface interface identity3 = true := by decide +kernel
-- Caller-visible Isometry remains Isometry after checking a square pure map.
example : ((Qirf.Carrier.check (artifact []) #[0]
    {interface with publicEffect := .iso} {interface with publicEffect := .iso} identity3).run 2000000).1.map
    (fun checked => checked.interface.publicEffect) = .ok .iso := by decide +kernel
-- A physically valid four-cycle leaks the third logical basis state out of
-- the three-state code. Equal width and whole-space unitarity do not suffice.
example : accepts (artifact (step [0,1] [1,2,3,0] [0,0,0,0]))
    interface interface cycle = false := by decide +kernel
example : accepts (artifact (step [0,1] [1,2,0,3] [0,0,1,0]))
    interface interface cycle = false := by decide +kernel
example : accepts (artifact (step [1,0] [1,2,0,3] [0,0,0,0]))
    interface interface cycle = false := by decide +kernel
example : accepts (artifact cycleSteps) interface interface identity3 = false := by decide +kernel

private def threeToFour : Interface :=
  {interface with outputs := [⟨output.port,FiniteCarrierExamples.four⟩],publicEffect := .iso}
example : accepts (artifact []) threeToFour threeToFour FiniteCarrierExamples.embedding = true :=
  by decide +kernel
-- The same physical 4x4 identity is not a logical 3->4 Unitary operation.
example : accepts (artifact []) {threeToFour with publicEffect := .unitary}
    {threeToFour with publicEffect := .unitary} FiniteCarrierExamples.embedding = false :=
  by decide +kernel
example : accepts (artifact []) threeToFour interface identity3 = false := by decide +kernel
-- Same code matrix, different original variant order: stale interface refuses.
example : accepts (artifact cycleSteps) interface
    {interface with inputs := [⟨input.port,FiniteCarrierExamples.reordered⟩]} cycle = false :=
  by decide +kernel
example : accepts (artifact cycleSteps) interface
    {interface with outputs := [⟨⟨1,[19,7],2⟩,FiniteCarrierExamples.tri⟩]} cycle = false :=
  by decide +kernel
example : accepts (artifact cycleSteps) {interface with publicEffect := .observe}
    {interface with publicEffect := .observe} cycle = false := by decide +kernel

-- Fresh dependency checking retains original implementations/specifications.
private def dependency (implementation : List Step) : Qirf.Artifact :=
  ⟨#[body implementation,body cycleSteps,body [⟨[],.contract [0,1] 0 false⟩]],
    #[⟨[.bits 2],0,.circuit 1,"implementation","specification",[]⟩],#[],2,none⟩
example : accepts (dependency cycleSteps) interface interface cycle #[0,1,3,2] = true :=
  by decide +kernel
example : accepts (dependency []) interface interface cycle #[0,1,3,2] = false :=
  by decide +kernel
example : accepts (dependency cycleSteps) interface interface cycle #[0,1,2,3] = false :=
  by decide +kernel

-- An empty record remains an owner despite contributing no matrix axes. Its
-- scalar phase acts on the complete live frame and must not disappear.
private def empty : Owner := ⟨⟨0,[],0⟩,FiniteCarrierExamples.emptyRecord⟩
private def bit : Owner := ⟨⟨1,[19],1⟩,[.bit]⟩
private def zeroInterface : Interface := ⟨[empty,bit],[{empty with port := ⟨2,[],0⟩},bit],.unitary⟩
private def scalarBody : Program :=
  ⟨[empty.port,bit.port],[],[.pure (.applyUnitary 0 2 [⟨[],.monomial [] [0] [4]⟩])],
    [2,1],[],.unitary⟩
private def scalar : Qirf.Artifact := ⟨#[scalarBody],#[],#[],0,none⟩
private def minusIdentity : Matrix := matrix 2 2 [-1,0,0,-1]
example : accepts scalar zeroInterface zeroInterface minusIdentity = true := by decide +kernel
example : accepts scalar zeroInterface zeroInterface (matrix 2 2 [1,0,0,1]) = false :=
  by decide +kernel
private def dropped : Interface := ⟨[bit],[bit],.unitary⟩
example : accepts scalar dropped dropped minusIdentity = false := by decide +kernel
example : accepts scalar zeroInterface
    {zeroInterface with inputs := [⟨empty.port,[.unit]⟩,bit]} minusIdentity = false :=
  by decide +kernel
example : accepts scalar {zeroInterface with outputs := [bit,⟨⟨2,[],0⟩,empty.basis⟩]}
    {zeroInterface with outputs := [bit,⟨⟨2,[],0⟩,empty.basis⟩]} minusIdentity = false :=
  by decide +kernel

-- Hidden observation may not acquire a pure carrier label, whether the raw
-- label is honest or falsely Unit/Isometry. No public result exposes it.
private def observing (effect : Semantics.Raw.Effect) : Qirf.Artifact :=
  ⟨#[⟨[bit.port],[],[.discard 1,.pure (.init0 2 23)],[2],[],effect⟩],#[],#[],0,none⟩
private def observingInterface : Interface := ⟨[bit],[⟨⟨2,[23],1⟩,[.bit]⟩],.iso⟩
example : accepts (observing .observe) observingInterface observingInterface
    (matrix 2 2 [1,0,0,1]) = false := by decide +kernel
example : accepts (observing .unitary) observingInterface observingInterface
    (matrix 2 2 [1,0,0,1]) = false := by decide +kernel
example : accepts (observing .iso) observingInterface observingInterface
    (matrix 2 2 [1,0,0,1]) = false := by decide +kernel
example : accepts (artifact cycleSteps) interface interface cycle #[] = false := by decide +kernel
example : accepts (artifact cycleSteps) interface interface cycle #[0] 0 = false := by decide +kernel
-- Width metadata cannot substitute for the complete original wire list.
example : ((Qirf.Carrier.ownerCode [{input with port := ⟨0,[7],2⟩}]).run 2000000).1.isOk = false :=
  by decide +kernel
-- Concatenation would form a valid pair, but the first owner's incomplete
-- tree may not steal the second owner's Unit node to finish its own shape.
private def stolen : List Owner :=
  [⟨⟨0,[0],1⟩,[.pair,.bit]⟩,⟨⟨1,[1],1⟩,[.unit,.bit]⟩]
example : Semantics.FiniteCarrier.layout (forest stolen) = some ⟨2,[0,1,2,3]⟩ := by decide
example : ((QleisliKernel.FiniteCarrier.code (forest stolen)).run 2000000).1.isOk = true :=
  by decide +kernel
example : ((Qirf.Carrier.ownerCode stolen).run 2000000).1.isOk = false :=
  by decide +kernel

#print axioms Qirf.Carrier.ownerCode_conditions
#print axioms Qirf.Carrier.readOwners_conditions
#print axioms Qirf.Carrier.check_postcondition
end CarrierBodyExamples

namespace CarrierSourceExamples
open Semantics.FiniteCarrier

def text := "// enum Tri { Wrong }\npub enum Tri { A, B, C, }\n/* struct Box { wrong: Bit } */\npub struct Box { pub tag: Tri, flag: Bit }\nstruct Empty {}\nclassical fn f(x: Bit) -> Bit { x }"
def sources : SourceTypes.Sources := #[("labels",text)]
def tri : Basis := [.enumeration ⟨"labels","Tri",text⟩ ["A","B","C"]]
def boxType : Basis := .record ⟨"labels","Box",text⟩ ["tag","flag"] :: tri ++ [.bit]
def value {α : Type} (action : Finite.WorkM α) := (action.run 10000000).1
def refused {α : Type} (action : Finite.WorkM α) := !(value action).isOk

example : value (SourceTypes.check sources tri) = .ok () := by decide +kernel
example : value (SourceTypes.check sources boxType) = .ok () := by decide +kernel
example : value (SourceTypes.check sources [.record ⟨"labels","Empty",text⟩ []]) = .ok () := by decide +kernel
example : refused (SourceTypes.check sources [.enumeration ⟨"labels","Tri",text⟩ ["A","C","B"]]) := by decide +kernel
example : refused (SourceTypes.check sources [.enumeration ⟨"labels","Tri",text⟩ ["A","B","C","D"]]) := by decide +kernel
example : refused (SourceTypes.check sources [.enumeration ⟨"other","Tri",text⟩ ["A","B","C"]]) := by decide +kernel
example : refused (SourceTypes.check sources [.enumeration ⟨"labels","f",text⟩ ["A","B","C"]]) := by decide +kernel
example : refused (SourceTypes.check sources [.enumeration ⟨"labels","Tri",text ++ " "⟩ ["A","B","C"]]) := by decide +kernel
example : refused (SourceTypes.check sources (.record ⟨"labels","Box",text⟩ ["flag","tag"] :: [.bit] ++ tri)) := by decide +kernel
example : refused (SourceTypes.check sources (.record ⟨"labels","Box",text⟩ ["tag","flag"] :: [.bits 2,.bit])) := by decide +kernel
example : refused (SourceTypes.check #[("labels",text),("labels",text)] tri) := by decide +kernel
example : refused (SourceTypes.check #[("labels",text ++ "\nenum Tri { D }")] tri) := by decide +kernel

-- Reserved words must be refused in the actual independently reconstructed
-- declaration/member positions, not only by the ordinary Rust parser.
def reservedDeclaration := "pub enum match { A }"
example : value (SourceTypes.check #[("labels",reservedDeclaration)]
    [.enumeration ⟨"labels","match",reservedDeclaration⟩ ["A"]]) = .error .request := by decide +kernel
def reservedVariant := "pub enum Label { match }"
example : value (SourceTypes.check #[("labels",reservedVariant)]
    [.enumeration ⟨"labels","Label",reservedVariant⟩ ["match"]]) = .error .request := by decide +kernel
def reservedField := "pub struct Label { match: Unit }"
example : value (SourceTypes.check #[("labels",reservedField)]
    [.record ⟨"labels","Label",reservedField⟩ ["match"],.unit]) = .error .request := by decide +kernel

-- qmatch is also reserved by the shared source grammar. These assertions
-- exercise the actual independent declaration/member reader.
def reservedQmatchDeclaration := "pub enum qmatch { A }"
example : value (SourceTypes.check #[("labels",reservedQmatchDeclaration)]
    [.enumeration ⟨"labels","qmatch",reservedQmatchDeclaration⟩ ["A"]]) = .error .request := by decide +kernel
def reservedQmatchVariant := "pub enum Label { qmatch }"
example : value (SourceTypes.check #[("labels",reservedQmatchVariant)]
    [.enumeration ⟨"labels","Label",reservedQmatchVariant⟩ ["qmatch"]]) = .error .request := by decide +kernel
def reservedQmatchField := "pub struct Label { qmatch: Unit }"
example : value (SourceTypes.check #[("labels",reservedQmatchField)]
    [.record ⟨"labels","Label",reservedQmatchField⟩ ["qmatch"],.unit]) = .error .request := by decide +kernel

def nested := "pub struct Pair { flags: (Bit, Bits<0>), tag: labels::Tri }"
def nestedType : Basis := [.record ⟨"main","Pair",nested⟩ ["flags","tag"],.pair,.bit,.bits 0] ++ tri
example : value (SourceTypes.check (sources.push ("main",nested)) nestedType) = .ok () := by decide +kernel
example : value (SourceTypes.literalWidth "6") = .ok 6 := by decide
example : value (SourceTypes.literalWidth "7") = .error .limit := by decide
example : value (SourceTypes.literalWidth "00") = .error .request := by decide
example : value (SourceTypes.literalWidth "0006") = .error .request := by decide
example : value (SourceTypes.literalWidth "0007") = .error .request := by decide
example : value (SourceTypes.literalWidth "0x") = .error .request := by decide

def noncanonicalDecimal := "struct Word { bits: Bits<02> }"
example : refused (SourceTypes.check #[("main",noncanonicalDecimal)]
    [.record ⟨"main","Word",noncanonicalDecimal⟩ ["bits"],.bits 2]) := by decide +kernel
def recursive := "struct Loop { again: Loop }"
example : refused (SourceTypes.check #[("main",recursive)]
    [.record ⟨"main","Loop",recursive⟩ ["again"],.unit]) := by decide +kernel
def imported := "use labels::{Tri}; struct Box { tag: Tri }"
example : value (SourceTypes.check (sources.push ("main",imported))
    (.record ⟨"main","Box",imported⟩ ["tag"] :: tri)) = .ok () := by decide +kernel
example : (SourceTypes.lex "/* enum X {} /* nested */ */ enum Y { A }").isOk := by decide
example : !(SourceTypes.lex "/* unfinished").isOk := by decide
example : !(SourceTypes.lex "enum X { A }\r").isOk := by decide
example : (SourceTypes.lex "enum X { A }\r\n").isOk := by decide
example : (SourceTypes.lex "// enum X { A }\nenum Y { B }") =
    .ok ["enum","Y","{","B","}"] := by decide

-- Imported spellings must reconstruct the original declaration, not a facade.
def facade := "pub use labels::{Tri};"
def qualifiedFacade := "struct Box { tag: bridge::Tri }"
def importedFacade := "use bridge::Tri; struct Box { tag: Tri }"
def aliasSources : SourceTypes.Sources := sources.push ("bridge",facade)
def box (source : String) (child : Basis := tri) : Basis :=
  .record ⟨"main","Box",source⟩ ["tag"] :: child
example : value (SourceTypes.check (aliasSources.push ("main",qualifiedFacade))
    (box qualifiedFacade)) = .ok () := by decide +kernel
example : value (SourceTypes.check (aliasSources.push ("main",importedFacade))
    (box importedFacade)) = .ok () := by decide +kernel
example : refused (SourceTypes.check (aliasSources.push ("main",importedFacade))
    (box importedFacade [.enumeration ⟨"bridge","Tri",facade⟩ ["A","B","C"]])) := by decide +kernel
example : refused (SourceTypes.check (aliasSources.push ("main",importedFacade))
    (box importedFacade [.enumeration ⟨"labels","Tri",text⟩ ["C","B","A"]])) := by decide +kernel
example : refused (SourceTypes.check (sources.push ("main",importedFacade))
    (box importedFacade)) := by decide +kernel
-- A private import is visible unqualified in its own module, never a member.
def privateFacade := "use labels::Tri; struct Box { tag: Tri }"
example : value (SourceTypes.check (sources.push ("main",privateFacade))
    (box privateFacade)) = .ok () := by decide +kernel
example : refused (SourceTypes.check ((sources.push ("bridge",privateFacade)).push ("main",qualifiedFacade))
    (box qualifiedFacade)) := by decide +kernel
def selfQualified := "use labels::Tri; struct Box { tag: main::Tri }"
example : refused (SourceTypes.check (sources.push ("main",selfQualified))
    (box selfQualified)) := by decide +kernel
-- Canonical lookup has no category, visibility or same-width fallback.
def privateType := "enum Tri { A, B, C }"
example : refused (SourceTypes.check #[("labels",privateType),("main",imported)]
    (box imported [.enumeration ⟨"labels","Tri",privateType⟩ ["A","B","C"]])) := by decide +kernel
example : refused (SourceTypes.check #[("labels",privateType),("bridge",facade),("main",importedFacade)]
    (box importedFacade [.enumeration ⟨"labels","Tri",privateType⟩ ["A","B","C"]])) := by decide +kernel
-- Public self-reexports cannot promote even an otherwise same-module private type.
def selfPromoted := "enum Tri { A, B, C } pub use labels::Tri;"
example : refused (SourceTypes.check #[("labels",selfPromoted),("main",imported)]
    (box imported [.enumeration ⟨"labels","Tri",selfPromoted⟩ ["A","B","C"]])) := by decide +kernel
def wrongCategory := "pub classical fn Tri(x: Bit) -> Bit { x }"
example : refused (SourceTypes.check #[("labels",wrongCategory),("main",imported)]
    (box imported)) := by decide +kernel
def collision := "use labels::Tri; enum Tri { A, B, C } struct Box { tag: Tri }"
example : refused (SourceTypes.check (sources.push ("main",collision))
    (box collision)) := by decide +kernel
def duplicate := "use labels::{Tri,Tri}; struct Box { tag: Tri }"
example : refused (SourceTypes.check (sources.push ("main",duplicate))
    (box duplicate)) := by decide +kernel
def cycleA := "pub use bridge::Tri;"
def cycleB := "pub use labels::Tri;"
example : refused (SourceTypes.check #[("labels",cycleA),("bridge",cycleB),("main",imported)]
    (box imported)) := by decide +kernel
-- Module qualification never treats a local declaration as a module alias.
def moduleShadow := "enum bridge { Only } struct Box { tag: bridge::Tri }"
example : value (SourceTypes.check (aliasSources.push ("main",moduleShadow))
    (box moduleShadow)) = .ok () := by decide +kernel
-- Nested/grouped paths retain source order and contextual std module keywords.
def importPaths (text : String) := SourceTypes.lex text >>= SourceTypes.Imports.read
example : importPaths "a::{b::{Tri,Four,},One},c::Empty" = .error "unexpected import separator" := by decide
example : importPaths "{a::{b::{Tri,Four,},One},c::Empty,}" =
    .ok [["Tri","b","a"],["Four","b","a"],["One","a"],["Empty","c"]] := by decide
example : importPaths "std::{basis::Tri,observe::Tri,classical::Tri}" =
    .ok [["Tri","basis","std"],["Tri","observe","std"],["Tri","classical","std"]] := by decide
example : !(importPaths "a::{}").isOk := by decide
example : !(importPaths "a::{Tri,,Four}").isOk := by decide
example : !(importPaths "a::{Tri,::Four}").isOk := by decide
example : !(importPaths "a::Tri as Other").isOk := by decide
example : !(importPaths "a::*").isOk := by decide
example : !(importPaths "::a::Tri").isOk := by decide
example : !(importPaths "a::_").isOk := by decide
example : !(importPaths "a::basis::Tri").isOk := by decide
example : !(SourceTypes.Imports.read ((List.replicate 65 "{") ++ ["a","::","Tri"] ++
    List.replicate 65 "}")).isOk := by decide

end CarrierSourceExamples


namespace CarrierSourceCoverageExamples
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
set_option Elab.async false

open Semantics.FiniteCarrier Semantics.CarrierInterface Semantics.Exact

private def original := "pub enum Tri { A, B, C }"
private def basis : Basis := [.enumeration ⟨"labels","Tri",original⟩ ["A","B","C"]]
private def owner : Owner := ⟨⟨0,[0,1],2⟩,basis⟩
private def interface : Interface := ⟨[owner],[owner],.unitary⟩
private def identity : Matrix := ⟨3,3,[1,0,0,0,1,0,0,0,1].map fun n =>
  ⟨.integer n,.integer 0,.integer 0,.integer 0⟩⟩
-- The actual root has no circuit evidence. Its declarations are consumed only
-- by the typed source reader, not by an invented self-comparison dependency.
private def artifact (rows : Array (String × String)) : Qirf.Artifact :=
  ⟨#[⟨[owner.port],[],[],[0],[],.unitary⟩],#[],rows,0,none⟩
private def data := artifact #[("labels",original)]
private def rows := Qirf.Carrier.sourceRows interface interface
private def request : Protocol.Carrier.Request := ⟨interface,interface,identity⟩
private def typed (value : Qirf.Artifact) (required : Protocol.Carrier.Request := request) := do
  Protocol.Carrier.checkSources value.sources required
  Qirf.Carrier.check value #[0] required.attached required.required required.logical
private def accepts {α : Type} (action : Finite.WorkM α) : Bool :=
  (action.run 2000000).1.isOk

-- Source-coverage rejection tests use the actual checker postconditions.
-- The carrier proof follows the retained root check; the typed proof passes
-- the source check's actual remaining work to the carrier check.
private theorem ordinary_refuses (value : Qirf.Artifact) (order : Array Nat)
    (coverage : Qirf.Validity.sourcesUsed value = false) (work : Nat) :
    ((Qirf.Validity.checkRoot value order).run work).1.isOk = false := by
  cases checked : (Qirf.Validity.checkRoot value order).run work with
  | mk result left =>
    cases result with
    | error error => rfl
    | ok root =>
      have facts := Qirf.Validity.checkRoot_postcondition value order root work left checked
      have impossible : (true : Bool) = false := facts.sources.symm.trans coverage
      cases impossible

private theorem carrier_refuses (value : Qirf.Artifact) (order : Array Nat)
    (attached required : Interface) (logical : Matrix)
    (coverage : Qirf.Validity.sourcesUsedWithSources value
      (Qirf.Carrier.sourceRows attached required) = false) (work : Nat) :
    ((Qirf.Carrier.check value order attached required logical).run work).1.isOk = false := by
  cases checked : (Qirf.Carrier.check value order attached required logical).run work with
  | mk result left =>
    cases result with
    | error error => rfl
    | ok accepted =>
      have facts := Qirf.Carrier.check_postcondition value order attached required logical
        accepted work left checked
      obtain ⟨beforeRoot,afterRoot,root⟩ := facts.root
      obtain ⟨afterCharges,checkedRoot⟩ := Qirf.Carrier.sourceRoot_result value order
        attached required accepted.root beforeRoot afterRoot root
      have actual := Qirf.Validity.checkRootWithSources_postcondition value order
        (Qirf.Carrier.sourceRows attached required) accepted.root afterCharges afterRoot checkedRoot
      have impossible : (true : Bool) = false := actual.sources.symm.trans coverage
      cases impossible

private theorem typed_refuses (value : Qirf.Artifact) (required : Protocol.Carrier.Request)
    (refuses : ∀ work, ((Qirf.Carrier.check value #[0] required.attached
      required.required required.logical).run work).1.isOk = false) (work : Nat) :
    ((typed value required).run work).1.isOk = false := by
  change ((Protocol.Carrier.checkSources value.sources required >>=
    fun _ => Qirf.Carrier.check value #[0] required.attached required.required
      required.logical).run work).1.isOk = false
  rw [Finite.bind_run]
  cases sourceStep : (Protocol.Carrier.checkSources value.sources required).run work with
  | mk result remaining =>
    cases result with
    | error error => rfl
    | ok sourceValue => exact refuses remaining

example : Qirf.Validity.sourcesUsed data = false := by decide_cbv
example : Qirf.Validity.sourcesUsedWithSources data rows = true := by decide_cbv
example : accepts (Qirf.Validity.checkRoot data #[0]) = false := by
  change ((Qirf.Validity.checkRoot data #[0]).run 2000000).1.isOk = false
  exact ordinary_refuses data #[0] (by decide_cbv) 2000000
example : accepts (typed data) = true := by decide_cbv
-- The policy compares complete module/text rows, not labels or width alone.
example : Qirf.Validity.sourcesUsedWithSources
    (artifact #[("other",original)]) rows = false := by decide_cbv
example : Qirf.Validity.sourcesUsedWithSources
    (artifact #[("labels","pub enum Tri { A, C, B }")]) rows = false := by decide_cbv
example : accepts (typed (artifact #[("other",original)])) = false := by decide_cbv
example : accepts (typed (artifact #[("",original)])) = false := by decide_cbv
example : accepts (Qirf.Validity.checkRootWithSources
    (artifact #[("",original)]) #[0] [("",original)]) = false := by decide_cbv
example : accepts (typed (artifact #[("labels","pub enum Tri { A, C, B }")])) = false :=
  by decide_cbv
-- Unrelated and helper-only dependencies are not nominal-origin references.
private def helper := "pub static fn width() -> Nat {1}"
example : Qirf.Validity.sourcesUsedWithSources
    (artifact #[("labels",original),("helper",helper)]) rows = false := by decide_cbv
example : accepts (typed (artifact #[("labels",original),("helper",helper)])) = false :=
  by
    have coverage : Qirf.Validity.sourcesUsedWithSources
        (artifact #[("labels",original),("helper",helper)])
        (Qirf.Carrier.sourceRows request.attached request.required) = false := by decide_cbv
    change ((typed (artifact #[("labels",original),("helper",helper)]) request).run 2000000).1.isOk = false
    exact typed_refuses (artifact #[("labels",original),("helper",helper)]) request
      (fun remaining => carrier_refuses (artifact #[("labels",original),("helper",helper)])
        #[0] request.attached request.required request.logical coverage remaining) 2000000
-- An exact row reference cannot launder a fabricated nominal member order.
private def reordered : Owner :=
  ⟨owner.port,[.enumeration ⟨"labels","Tri",original⟩ ["A","C","B"]]⟩
private def badInterface : Interface := ⟨[reordered],[reordered],.unitary⟩
example : accepts (typed data ⟨badInterface,badInterface,identity⟩) = false := by decide_cbv

#print axioms ordinary_refuses
#print axioms carrier_refuses
#print axioms typed_refuses
#print axioms Qirf.checkGraphReceipts_freshWithSources
#print axioms Qirf.Validity.checkRootWithSources_postcondition
#print axioms Qirf.Carrier.sourceRoot_result
end CarrierSourceCoverageExamples

#print axioms SourceTypes.nominal_original
#print axioms SourceTypes.check_original_declarations
#print axioms Protocol.Carrier.check_binding
#print axioms Protocol.ExecutionView.CheckedCarrier.check_binding
#print axioms Protocol.ExecutionView.CheckedCarrier.Binding.root_safe
#print axioms Protocol.NativeContext.run_carrier_binding

namespace SourceNaturalSyntaxExamples
open Semantics.SourceNatural
-- Existing Nat syntax/reference only. Callback names have no original helper
-- authority until separate source binding and generic obligations are checked.
-- Large values/depth examples below are metadata, not quantum cases.
def parsed (text : String) := SourceTypes.lex text >>= SourceTypes.NaturalSyntax.read


def n := Expr.number
example : parsed "2+3*2-6" = .ok (.sub (.add (n 2) (.mul (n 3) (n 2))) (n 6)) := by rfl
example : parsed "8-3-3" = .ok (.sub (.sub (n 8) (n 3)) (n 3)) := by rfl
example : parsed "(1+2)*2-4" = .ok (.sub (.mul (.add (n 1) (n 2)) (n 2)) (n 4)) := by rfl
example : parsed "previous[3]()" = .ok (.call ["previous"] [n 3]) := by rfl
example : parsed "helper::p[add[1,1](),(3-1)]()"
    = .ok (.call ["helper","p"] [.call ["add"] [n 1,n 1],.sub (n 3) (n 1)]) := by rfl
example : parsed "f()" = .ok (.call ["f"] []) := by rfl
example : parsed "f[]()" = .ok (.call ["f"] []) := by rfl
example : parsed "f[1,2]()+3" = .ok (.add (.call ["f"] [n 1,n 2]) (n 3)) := by rfl
example : parsed "std::classical::f[1]()" = .ok (.call ["std","classical","f"] [n 1]) := by rfl
example : parsed "n" = .ok (.name ["n"]) := by rfl
example : (SourceTypes.NaturalSyntax.decimal "170141183460469231731687303715884105727").toOption =
    some 170141183460469231731687303715884105727 := by decide +kernel
example : !(SourceTypes.NaturalSyntax.decimal "170141183460469231731687303715884105728").isOk := by decide +kernel
example : (["", "00", "02", "+1", "-1", "1 2", "1**2", "1+", "(1", "1)",
    "f[1,]()", "f(1)", "f[1]", "f[1]()()", "f[1)", "f::", "_", "a::basis[1]()"].all
    (fun text => !(parsed text).isOk)) := by decide +kernel
example : (parsed (String.intercalate "+" (List.replicate 128 "1"))).isOk := by decide +kernel
example : !(parsed (String.intercalate "+" (List.replicate 129 "1"))).isOk := by decide +kernel
example : (parsed (String.ofList (List.replicate 63 '(') ++ "1" ++
    String.ofList (List.replicate 63 ')'))).isOk := by decide +kernel
example : !(parsed (String.ofList (List.replicate 64 '(') ++ "1" ++
    String.ofList (List.replicate 64 ')'))).isOk := by decide +kernel

def emptyNames : Names := fun _ => none
def emptyCalls : Calls := fun _ _ => none
def mathematical (text : String) := (parsed text).toOption >>= evaluate 128 emptyNames emptyCalls
example : mathematical "2+3*2-6" = some 2 := by decide +kernel
example : mathematical "4294967295+1-4294967294" = some 2 := by decide +kernel
example : mathematical "1-2+3" = none := by decide +kernel
example : mathematical "previous[3]()" = none := by decide +kernel
example : Value emptyNames emptyCalls (.sub (.add (n 2) (.mul (n 3) (n 2))) (n 6)) 2 :=
  evaluate_value 128 emptyNames emptyCalls _ _ (by decide +kernel)
#print axioms evaluate_value

end SourceNaturalSyntaxExamples

namespace SourceNaturalAffineExamples
open QleisliKernel
open Semantics.SourceAffine
open SourceTypes

def value {α : Type} (action : Finite.WorkM α) := (action.run 10000000).1

def row (constant : Int) (coefficients : List Int) : Form := ⟨constant,coefficients⟩
def x := row 0 [1]
def y := row 0 [0,1]
def found (rows : List Form) : Except Finite.Error Bool :=
  match value (NaturalConstraints.check rows) with
  | .ok none => .ok false
  | .ok (some _) => .ok true
  | .error error => .error error

def observed (rows : List Form) : Option Bool := (found rows).toOption

-- Metadata and symbolic arithmetic only; no quantum matrix/case is generated.
example : value (NaturalAffine.add x (row 2 [3])) = .ok (row 2 [4]) := by rfl
example : value (NaturalAffine.sub x x) = .ok (row 0 [0]) := by rfl
example : value (NaturalAffine.multiply (row 2 [0]) x) = .ok (row 0 [2]) := by rfl
example : !(value (NaturalAffine.multiply x x)).isOk := by rfl
example : !(value (NaturalAffine.multiply x y)).isOk := by rfl
example : value (NaturalAffine.constant 0 4294967296) = .ok (row 4294967296 []) := by rfl
example : value (NaturalAffine.add (row 170141183460469231731687303715884105727 []) (row 1 [])) =
    .error .limit := by rfl
example : value (NaturalAffine.sub (row (-170141183460469231731687303715884105728) [])
    (row (-170141183460469231731687303715884105728) [])) = .error .limit := by rfl
example : !(value (NaturalAffine.multiply (row 0 (List.replicate 33 0)) x)).isOk := by rfl
example : !(value (NaturalAffine.parameter 0 0)).isOk := by rfl
example : value (NaturalAffine.parameter 2 1) = .ok y := by rfl
example : observed [] = some false := by decide +kernel
example : observed [row 1 []] = some true := by decide +kernel
example : observed [row (-1) []] = some false := by decide +kernel
example : observed [row 0 [-1],row 1 [-1],row 0 [1]] = some true := by decide +kernel
example : observed [row 0 [-1],row 1 [-1],row (-2) [1]] = some false := by decide +kernel
-- Rational relaxation deliberately supplies no integer-feasibility promise.
example : observed [row 0 [-1],row (-1) [2],row 1 [-2]] = some false := by decide +kernel
example : observed [row 0 [-1,1,0],row 0 [0,-1,1],row 0 [0,0,-1],row 1 [1,0,0]] =
    some true := by decide +kernel
example : observed [row 2 [-2],row 0 [2]] = some true := by decide +kernel
example : !(found [row 0 [],x]).isOk := by rfl
example : !(found [row 0 (List.replicate 33 0)]).isOk := by rfl
open QleisliKernel SourceTypes Semantics.SourceAffine
open NaturalPredicates

def result {α : Type} (action : Finite.WorkM α) := (action.run 10000000).1

def form (c : Int) (cs : List Int) : Form := ⟨c,cs⟩
def n := form 0 [1]
def number (c : Int) := form c [0]
def possible (a : Int) (op : Comparison) (b : Int) : Bool :=
  (result (do feasible (← comparison (form a []) op (form b [])))).toOption.getD false

def implied (guard : Comparison) (bound : Int) (op : Comparison) (other : Int) : Bool :=
  (result (do
    let context ← comparison n guard (number bound)
    implies context n op (number other))).isOk

-- All six exact predicates, with both polarities. These are scalar metadata.
example : [possible 0 .eq 0,possible 0 .ne 1,possible 0 .le 1,
  possible 0 .lt 1,possible 1 .ge 0,possible 1 .gt 0] = List.replicate 6 true := by decide +kernel
example : [possible 0 .eq 1,possible 1 .ne 1,possible 1 .le 0,
  possible 1 .lt 1,possible 0 .ge 1,possible 0 .gt 0] = List.replicate 6 false := by decide +kernel
example : implied .ge 1 .ge 1 := by decide +kernel
example : implied .gt 0 .ge 1 := by decide +kernel
example : !implied .ge 0 .ge 1 := by decide +kernel
example : !implied .ge 1 .ge 2 := by decide +kernel
example : implied .eq 2 .ne 1 := by decide +kernel
example : !implied .ne 1 .gt 1 := by decide +kernel
example : (result (do
  let nonnegative ← comparison n .ge (number 0)
  let distinct ← comparison n .ne (number 1)
  let positive ← comparison n .ge (number 1)
  let first ← conjunction nonnegative distinct
  let context ← conjunction first positive
  implies context n .ge (number 2))).isOk := by decide +kernel
example : (result (comparison (form (-170141183460469231731687303715884105728) [])
  .le (form 0 []))).isOk = false := by decide +kernel
example : ((comparison n .ge (number 1)).run 1).1.isOk = false := by decide +kernel

def helper (source : String) : Except String NaturalHeaders.Helper := do
  let [declaration] ← declarations source | throw "one declaration required"
  NaturalHeaders.read declaration

def shape (source : String) : Option (List String × Nat) :=
  (helper source).toOption.map fun h => (h.parameters,h.premises.length)

def validHelper : String :=
  "pub static fn previous[const n:Nat]() -> Nat requires n >= 1 {n-1}"
example : shape validHelper = some (["n"],1) := by decide +kernel
example : shape "static fn value() -> Nat {2}" = some ([],0) := by decide +kernel
example : shape "static fn value[]() -> Nat {2}" = some ([],0) := by decide +kernel
example : shape "static fn swap[const n:Nat,const m:Nat,]() -> Nat requires pair[n,m]() != pair[m,n](), n >= 0, {n+m}" =
  some (["n","m"],2) := by decide +kernel
example : shape "static fn test[const n:Nat]() -> Nat requires n == 1,n != 2,n < 3,n <= 4,n > 0,n >= 1 {n}" =
  some (["n"],6) := by decide +kernel
example : !(helper "static fn bad(q:Bit) -> Nat {1}").isOk := by decide +kernel
example : !(helper "static fn bad[const n:Basis]() -> Nat {1}").isOk := by decide +kernel
example : !(helper "static fn bad[const n:Nat,const n:Nat]() -> Nat {n}").isOk := by decide +kernel
example : !(helper "static fn bad() -> Bits<1> {1}").isOk := by decide +kernel
example : !(helper "static fn bad() -> Nat requires {1}").isOk := by decide +kernel
example : !(helper "static fn bad() -> Nat {00}").isOk := by decide +kernel
example : !(helper "fn bad() -> Nat {1}").isOk := by decide +kernel
example : !(declarations "static fn bad() -> Nat;").isOk := by decide +kernel
example : !(declarations "static fn bad() -> Nat {").isOk := by decide +kernel
-- Same original binding/category/visibility rules for both consumers.
def canonical (sources : Sources) (caller : String) (path : List String) :=
  (result (resolveReference sources caller path)).toOption.map fun r =>
    (r.moduleName,r.declaration.name,r.declaration.kind)
example : canonical #[ ("defs",validHelper),("exports","pub use defs::previous;"),
  ("main","use exports::previous;")] "main" ["previous"] =
  some ("defs","previous","static-fn") := by decide +kernel
example : canonical #[ ("defs","static fn hidden() -> Nat {1}"),
  ("main","use defs::hidden;")] "main" ["hidden"] = none := by decide +kernel
example : canonical #[ ("defs",validHelper),("private","use defs::previous;")]
  "main" ["private","::","previous"] = none := by decide +kernel
example : canonical #[ ("main",validHelper ++ " fn previous() -> Bit {0}")]
  "main" ["previous"] = none := by decide +kernel
end SourceNaturalAffineExamples


namespace OrdinaryValueKernelTests
open QleisliKernel.Semantics.OrdinaryValue

-- Exercise the public pure-kernel import without requiring the Mathlib bridge.
example : Represents [] [.unit] .unit .unit := .unit
example : Represents [] [.bits 0] (.bits []) (.bits []) := .bits [] [] .nil
example : ¬ Represents [] [.unit] (.bits []) (.bits []) := by
  intro represented
  cases represented
example : littleEndian [false,true] = 2 := rfl
example : Represents [] [.pair,.unit,.unit] (.pair .unit .unit) (.pair .unit .unit) :=
  Represents.copy (Represents.unit : Represents [] [.unit] .unit .unit)

end OrdinaryValueKernelTests


/-! Small reductions of the actual transport definitions. These are data and
framing checks; complete source/body acceptance is checked separately.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.QmatchTransport
open Lean Protocol

private def port (bits : Nat) : Json := Json.mkObj
  [("token",.num 10),("wires",.arr #[]),("bits",.num bits)]

private def owner (bits : Nat) : Json := Json.mkObj
  [("port",port bits),("basis",.arr #[Json.mkObj [("tag",.str "unit")]])]

private def interface (bits : Nat) (effect : String := "unitary") : Json := Json.mkObj
  [("inputs",.arr #[owner bits]),("outputs",.arr #[owner bits]),("public_effect",.str effect)]

private def request (arms : List Json) (source : Json) (extras : List (String × Json) := [])
    (version : Nat := 4) : Json :=
  let position := Json.mkObj [("offset",.num 137),("start",.num 0),("count",.num 1)]
  let site := Json.mkObj [("attached",interface 0),("required",interface 0),
    ("position",position),("arms",.arr arms.toArray)]
  Json.mkObj ([("format",.str "qleisli.qmatch-request"),("version",.num version),
    ("profile",.str Qmatch.profile),("source",source),
    ("positions",.arr #[position]),("sites",.arr #[site])] ++ extras)

private def source : Json := Json.mkObj
  [("module",.str "same"),("function",.str "choose")]

private def legacySource : Json := Json.mkObj
  [("module",.str "same"),("function",.str "choose"),("offset",.num 137)]

private def arm (evidence : Nat) : Json := Json.mkObj
  [("evidence",.num evidence),("controlled",.num 2)]

-- Port storage is u8, independently of the smaller semantic physical bounds.
example : (Carrier.readInterface (interface 255)).isOk = true := by decide +kernel
example : (Carrier.readInterface (interface 256)).isOk = false := by decide +kernel
example : (Carrier.readInterface (interface 0 "observe")).isOk = true := by decide +kernel
example : (Carrier.readInterface (interface 0 "iso")).isOk = false := by decide +kernel

example : ((Qmatch.decode (request [arm 0] source)).run 1000).1.isOk = true := by decide +kernel
example : (((Qmatch.decode (request [arm 0] source)).run 1000).1.toOption.map fun decoded =>
    (decoded.source.moduleName, decoded.source.functionName,
      decoded.positions.map (fun position => (position.offset,position.start,position.count)),
      decoded.sites.map (fun site => (site.position.offset,site.position.start,site.position.count)))) =
    some ("same","choose",[(137,0,1)],[(137,0,1)]) := by rfl
example : ((Qmatch.decode (request [] source)).run 1000).1.isOk = false := by decide +kernel
example : ((Qmatch.decode (request [arm 4294967296] source)).run 1000).1.isOk = false := by decide +kernel
example : ((Qmatch.decode (request [arm 0] source [("accepted",.bool true)])).run 1000).1.isOk = false := by decide +kernel
example : ((Qmatch.decode (request [arm 0] legacySource)).run 1000).1.isOk = false := by decide +kernel

-- Even a current-shaped request cannot select the retired v3 contract.
example : ((Qmatch.decode (request [arm 0] source [] 3)).run 1000).1.isOk = false := by decide +kernel

-- The retired single-site wire shape cannot regain acceptance through a fallback.
private def legacyRequest : Json := Json.mkObj
  [("format",.str "qleisli.qmatch-request"),("version",.num 2),
    ("profile",.str "finite-source-qmatch-named-v2"),
    ("attached",interface 0),("required",interface 0),
    ("source",legacySource),("arms",.arr #[arm 0])]
example : ((Qmatch.decode legacyRequest).run 1000).1.isOk = false := by decide +kernel

private def framedInput (scope : ExecutionView.Packet.Scope) : ExecutionView.Packet.Input :=
  ⟨.e2026,scope,ByteArray.empty,ByteArray.empty,ByteArray.empty,[]⟩

example : (ExecutionView.CheckedQmatch.input (framedInput .inspection)).run 1000 =
    (.error .packet,1000) := rfl
example : (ExecutionView.CheckedQmatch.input (framedInput .caller)).run 1000 =
    (.error .packet,1000) := rfl

-- An unframed view is refused before source checking, not accepted as a receipt.
example : (ExecutionView.CheckedQmatch.check ByteArray.empty ByteArray.empty).run 1000 =
    (.error .invalidView,1000) := rfl

#print axioms Protocol.Qirf.readAll_original
#print axioms Qmatch.check_binding
#print axioms ExecutionView.CheckedQmatch.check_binding
#print axioms ExecutionView.CheckedQmatch.Binding.root_safe
#print axioms ExecutionView.CheckedQmatch.run_binding
end QleisliKernel.Tests.QmatchTransport
