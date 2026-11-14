import QleisliKernel.Tests.RawTraceTests

/-! Actual one-bit source plus Raw component costs. The 10M refusal and
the current 20M success each use one shared work state. The 2B diagnostic
verifies the same 129 source events and Raw intervals. The first snapshots,
source and outputs are preserved in source-raw-cost-current-first and
checks/real-full-native-meter-cost-snapshots.
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

/-- Preserve the actual fixed-budget failure cause as well as charged work.
An exhausted source read cannot be reported as a successful smaller profile. -/
def outcome {α : Type} (work : Nat) (action : Finite.WorkM α) : Except Finite.Error Unit × Nat :=
  let (result,left) := action.run work
  (result.map (fun _ => ()),work-left)

#guard measure 10000000 (SourceTypes.QuantumSignature.read sources "main" "route") = (true,232131)
#guard outcome 10000000 (SourceTrace.read sources "main" "route") matches
  (.error (.arithmetic .workLimit),9998938)
#guard measure 2000000000 (SourceTrace.read sources "main" "route") = (true,14743150)
#guard outcome 10000000 composed matches (.error (.arithmetic .workLimit),9998938)
#guard measure exactWorkLimit composed = (true,15879813)
#guard measure 2000000000 composed = (true,15879813)

end QleisliKernel.Tests.SourceTraceCost
