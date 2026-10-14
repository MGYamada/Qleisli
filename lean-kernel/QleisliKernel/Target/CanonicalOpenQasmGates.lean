import QleisliKernel.Raw.BranchFunction
import QleisliKernel.Semantics.CanonicalTerminalQasm

/-! Exact one-qubit standard-gate matrices, before terminal observation.
Mathematical standard-library meanings are
an explicit specification assumption, not an include-loader/hardware claim.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Target.CanonicalOpenQasmGates
open QleisliKernel QleisliKernel.Semantics.Exact Semantics.CanonicalTerminalQasm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def gates : List Semantics.CanonicalTerminalQasm.Gate := [.h,.x,.y,.z,.s,.sdg,.t,.tdg]

def expected : Semantics.CanonicalTerminalQasm.Gate → Matrix
  | .h =>
    let rootHalf : Scalar := ⟨⟨0,0⟩,⟨1,1⟩,⟨0,0⟩,⟨0,0⟩⟩
    let negativeRootHalf : Scalar := ⟨⟨0,0⟩,⟨-1,1⟩,⟨0,0⟩,⟨0,0⟩⟩
    ⟨2,2,[rootHalf,rootHalf,rootHalf,negativeRootHalf]⟩
  | .x => ⟨2,2,[Scalar.zero,Scalar.one,Scalar.one,Scalar.zero]⟩
  | .y => ⟨2,2,[Scalar.zero,Exact.Scalar.phase 6,Exact.Scalar.phase 2,Scalar.zero]⟩
  | .z => ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Exact.Scalar.phase 4]⟩
  | .s => ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Exact.Scalar.phase 2]⟩
  | .sdg => ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Exact.Scalar.phase 6]⟩
  | .t => ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Exact.Scalar.phase 1]⟩
  | .tdg => ⟨2,2,[Scalar.one,Scalar.zero,Scalar.zero,Exact.Scalar.phase 7]⟩

def original (g : Semantics.CanonicalTerminalQasm.Gate) : Semantics.Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],[gateOp g 0 1],[1],[],.unitary⟩

def reconstructed (g : Semantics.CanonicalTerminalQasm.Gate) : Except Finite.Error Matrix :=
  ((Raw.BranchFunction.reconstruct [] (original g)).run 2000000).1

def agrees (g : Semantics.CanonicalTerminalQasm.Gate) : Bool :=
  match reconstructed g with
  | .error _ => false
  | .ok actual => actual == expected g


/-- Every gate's literal matrix is fixed before any CP-map phase quotient. -/
theorem gate_matrix (g : Semantics.CanonicalTerminalQasm.Gate) :
    (reconstructed g).toOption = some (expected g) := by
  cases g <;> decide +kernel

theorem all_gate_matrices : gates.all agrees = true := by decide +kernel

/-- Negating Y has the same standalone CP map but the wrong exact phase.
This literal comparison is made before the observing-instrument metric. -/
def wrongGlobalY : Matrix :=
  ⟨2,2,[Scalar.zero,Exact.Scalar.phase 2,Exact.Scalar.phase 6,Scalar.zero]⟩

theorem wrong_y_phase_refused :
    ((reconstructed .y).map (fun matrix => matrix == wrongGlobalY)).toOption = some false := by decide +kernel

theorem wrong_s_direction_refused :
    ((reconstructed .s).map (fun matrix => matrix == expected .sdg)).toOption = some false := by decide +kernel

theorem wrong_t_direction_refused :
    ((reconstructed .t).map (fun matrix => matrix == expected .tdg)).toOption = some false := by decide +kernel

end QleisliKernel.Target.CanonicalOpenQasmGates
