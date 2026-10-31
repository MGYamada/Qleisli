import QleisliKernel.Tests.RawTraceTests

/-! One-bit component measurement, not a native acceptance claim. The
source reader is evaluated separately at its recorded experimental budget;
the Raw component is then measured at the actual native work budget and at
a larger diagnostic-only budget. All first output streams are preserved.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RawTraceCost
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics

def original := RawTraceTests.single (String.join (List.replicate 129 "let q=h(q);") ++ "q")
def program : Observation.Program :=
  ⟨[⟨0,[0],1⟩],[],(List.range 129).map (fun i => .pure (.gate .h i (i+1))),[129],[],.unitary⟩

/-- Separate source and Raw charged work, only when both checks succeed. -/
def measure (work : Nat) : Option (Nat × Nat) :=
  match (SourceTrace.read (RawTraceTests.sources original) "main" "route").run 2000000000 with
  | (.error _,_) => none
  | (.ok source,left) =>
    let positions := RawTraceTests.positions source (List.replicate 129 1)
    let (result,remaining) := (QleisliKernel.Qirf.RawTrace.check source [] program positions).run work
    match result with
    | .error _ => none
    | .ok _ => some (2000000000-left,work-remaining)

#guard measure 10000000 = some (8700614,1136663)
#guard measure 2000000000 = some (8700614,1136663)

end QleisliKernel.Tests.RawTraceCost
