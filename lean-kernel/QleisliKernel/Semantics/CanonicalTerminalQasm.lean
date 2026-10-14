import QleisliKernel.Semantics.Observation
import QleisliKernel.Semantics.InstrumentContract

/-! Independent data/Raw meaning for a closed one-qubit terminal target word.
The standard h/x/y/z/s/sdg/t/tdg mathematical meanings are the declared profile
assumption; no include file is loaded or hardware behavior certified. This is
an explicit closed/reset adapter, not an arbitrary-input pure operation. The
zero-width logical Unit owner remains present and is explicitly consumed.
No acceptance checker, transport or producer evidence is imported here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.CanonicalTerminalQasm
open QleisliKernel QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Observation

inductive Gate where
  | h | x | y | z | s | sdg | t | tdg
  deriving BEq, DecidableEq, Repr

def Gate.name : Gate → String
  | .h => "h" | .x => "x" | .y => "y" | .z => "z"
  | .s => "s" | .sdg => "sdg" | .t => "t" | .tdg => "tdg"

private def phaseStep (phase : Nat) : Semantics.Finite.Step :=
  ⟨[],.monomial [0] [0,1] [0,phase]⟩

def gateOp (g : Gate) (input output : Nat) : Semantics.Observation.Op := .pure <| match g with
  | .h => .gate .h input output
  | .x => .gate .x input output
  | .y => .applyUnitary input output [⟨[],.monomial [0] [1,0] [2,6]⟩]
  | .z => .gate .z input output
  | .s => .applyUnitary input output [phaseStep 2]
  | .sdg => .applyUnitary input output [phaseStep 6]
  | .t => .gate .t input output
  | .tdg => .applyUnitary input output [phaseStep 7]

def program (gates : List Gate) : Semantics.Observation.Program :=
  let (owner,ops) := gates.foldl (fun (owner,ops) g =>
    (owner+1,ops ++ [gateOp g owner (owner+1)])) (1,[])
  ⟨[⟨0,[],0⟩],[],[.pure (.unpackUnit 0),.pure (.init0 1 0)] ++ ops ++ [.measure owner 0],
    [],[0],.observe⟩

theorem logical_unit_input (gates : List Gate) :
    (program gates).inputs = [⟨0,[],0⟩] := rfl

theorem logical_unit_consumed (gates : List Gate) :
    (program gates).operations.head? = some (.pure (.unpackUnit 0)) := by
  simp [program]

theorem terminal_result (gates : List Gate) :
    (program gates).outputs = [] ∧ (program gates).classicalOutputs = [0] ∧
      (program gates).effect = .observe := ⟨rfl,rfl,rfl⟩

def signature : Semantics.InstrumentContract.Signature := ⟨[.unit],[.bit]⟩

end QleisliKernel.Semantics.CanonicalTerminalQasm
