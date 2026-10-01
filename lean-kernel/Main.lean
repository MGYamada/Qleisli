import Cli.Finite
import Cli.Hierarchical

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--qpe-instrument-pending"] => QleisliKernel.Cli.runQpeInstrument
  | ["--instrument-pending"] => QleisliKernel.Cli.runInstrument
  | ["--readout-check"] => QleisliKernel.Cli.runReadout
  | ["--preparation-check"] => QleisliKernel.Cli.runPreparation
  | ["--hierarchy-fourier-pending"] => QleisliKernel.Cli.runHierarchyFourier
  | ["--hierarchy-request-pending"] => QleisliKernel.Cli.runHierarchyRequest
  | ["--hierarchy-pending"] => QleisliKernel.Cli.runHierarchy
  | ["--phase-layout", artifact, requirement] => QleisliKernel.Cli.runPhaseLayout artifact requirement
  | ["--layout-dag", artifact, requirement] => QleisliKernel.Cli.runLayoutDag artifact requirement
  | ["--layout", artifact, requirement] => QleisliKernel.Cli.runLayout artifact requirement
  | ["--phase-dag", artifact, requirement] => QleisliKernel.Cli.runDag artifact requirement
  | [artifact, requirement] => QleisliKernel.Cli.run artifact requirement
  | _ => QleisliKernel.Cli.usage
