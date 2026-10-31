import QleisliKernel.Tests.RawTraceMeterContinuity
import QleisliKernel.Tests.SourceTraceCost

/-! Small zero/one-bit width and nominal-layout controls for the separated
header accounting. Previous larger-budget failures are retained externally.
No full native/protocol budget or general runtime bound is claimed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RawTraceMeterTests
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics

def identitySource (basis : String) :=
  "pub unitary fn route(q:Q<" ++ basis ++ ">)->Q<" ++ basis ++ ">{q}"
def identityProgram (bits : Nat) (wires : List Nat) : Observation.Program :=
  ⟨[⟨10,wires,bits⟩],[],[],[10],[],.unitary⟩
def nominalSource (comment : String) :=
  comment ++ "pub enum Flag{Off,On} " ++ identitySource "Flag"

def header (original : String) (program : Observation.Program) : Option Nat :=
  ((SourceTrace.read (RawTraceTests.sources original) "main" "route").run 10000000).1.toOption.map
    fun source => QleisliKernel.Qirf.RawTrace.headerWork source program []

def accepted (original : String) (program : Observation.Program) (budget : Nat := 10000000) : Bool :=
  match ((SourceTrace.read (RawTraceTests.sources original) "main" "route").run 10000000).1 with
  | .error _ => false
  | .ok source => ((QleisliKernel.Qirf.RawTrace.check source [] program []).run budget).1.isOk

#guard accepted (identitySource "Unit") (identityProgram 0 [])
#guard !accepted (identitySource "Unit") (identityProgram 1 [3])
#guard accepted (identitySource "Bit") (identityProgram 1 [3])
#guard !accepted (identitySource "Bit") (identityProgram 0 [])
#guard accepted (identitySource "(Unit,Unit)") (identityProgram 0 [])
#guard !accepted (identitySource "(Unit,Unit)") (identityProgram 1 [3])
#guard accepted (identitySource "(Unit,Bit)") (identityProgram 1 [3])
#guard !accepted (identitySource "(Unit,Bit)") (identityProgram 0 [])
#guard accepted (nominalSource "") (identityProgram 1 [3])
#guard !accepted (nominalSource "") (identityProgram 0 [])
-- The layout itself ignores source-origin strings. Source parsing and nominal
-- owner comparisons still retain and fund those bytes in their own checks.
#guard header (nominalSource "") (identityProgram 1 [3]) =
  header (nominalSource "// A longer original source identity.\n") (identityProgram 1 [3])
#guard header (identitySource "Unit") (identityProgram 0 []) = some 640
#guard header (identitySource "(Unit,Unit)") (identityProgram 0 []) = some 2176
#guard !accepted (identitySource "Unit") (identityProgram 0 []) 0
#guard !accepted (identitySource "Unit") (identityProgram 0 []) 639
#guard (SourceTraceCost.composed.run 10000000).1.toOption = some (129,129)
#guard match (SourceTraceCost.composed.run 9000000).1 with
  | .error (.arithmetic .workLimit) => true
  | _ => false

#print axioms RawTraceMeterContinuity.afterReservation
#print axioms RawTraceMeterContinuity.funded_refinement
end QleisliKernel.Tests.RawTraceMeterTests
