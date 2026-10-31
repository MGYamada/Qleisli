import QleisliKernel.Tests.RawTraceTests

/-! Actual one-bit source plus Raw component costs. The 10M run uses one shared
work state, not two independent allowances. The larger diagnostic budget has the
same asserted work and does not authorize native acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceTraceCost
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics

def original := RawTraceTests.single (String.join (List.replicate 129 "let q=h(q);") ++ "q")
def sources := RawTraceTests.sources original
def program : Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],(List.range 129).map (fun i => .pure (.gate .h i (i+1))),[129],[],.unitary⟩

def composed : Finite.WorkM (Nat × Nat) := do
  let source ← SourceTrace.read sources "main" "route"
  let positions := RawTraceTests.positions source (List.replicate 129 1)
  let _ ← QleisliKernel.Qirf.RawTrace.check source [] program positions
  return (source.result.events.length,positions.length)

/-- Success and charged work, retained as assertions from the measured experiment. -/
def measure {α : Type} (work : Nat) (action : Finite.WorkM α) : Bool × Nat :=
  let (result,left) := action.run work
  (result.isOk,work-left)

#guard measure 10000000 (SourceTypes.QuantumSignature.read sources "main" "route") = (true,6208518)
#guard measure 10000000 (SourceTrace.read sources "main" "route") = (true,8700614)
#guard measure 2000000000 (SourceTrace.read sources "main" "route") = (true,8700614)
#guard measure 10000000 composed = (true,9837277)
#guard measure 2000000000 composed = (true,9837277)

end QleisliKernel.Tests.SourceTraceCost
