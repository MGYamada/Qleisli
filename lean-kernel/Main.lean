import Cli.Finite
import Cli.Hierarchical
import Cli.Validity
import Protocol.Product

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

private def nativeMode (mode : String) : Option (IO UInt32) :=
  match mode with
  | "--qirf-native" => some QleisliKernel.Cli.runValidity
  | "--qirf-contract" => some (QleisliKernel.Cli.runValidity true)
  | "--qpe-instrument-pending" => some QleisliKernel.Cli.runQpeInstrument
  | "--instrument-pending" => some QleisliKernel.Cli.runInstrument
  | "--readout-check" => some QleisliKernel.Cli.runReadout
  | "--preparation-check" => some QleisliKernel.Cli.runPreparation
  | "--hierarchy-fourier-pending" => some QleisliKernel.Cli.runHierarchyFourier
  | "--hierarchy-request-pending" => some QleisliKernel.Cli.runHierarchyRequest
  | "--hierarchy-pending" => some QleisliKernel.Cli.runHierarchy
  | _ => none

def main (args : List String) : IO UInt32 :=
  match args with
  | [mode, version] =>
    match nativeMode mode with
    | some action =>
      if version == QleisliKernel.Protocol.productVersion then action
      else do
        IO.println "qleisli.qirf-native 1\nerror\nversion"
        pure 1
    | none => QleisliKernel.Cli.run mode version
  | [mode] => (nativeMode mode).getD QleisliKernel.Cli.usage
  | ["--phase-layout", artifact, requirement] => QleisliKernel.Cli.runPhaseLayout artifact requirement
  | ["--layout-dag", artifact, requirement] => QleisliKernel.Cli.runLayoutDag artifact requirement
  | ["--layout", artifact, requirement] => QleisliKernel.Cli.runLayout artifact requirement
  | ["--phase-dag", artifact, requirement] => QleisliKernel.Cli.runDag artifact requirement
  | _ => QleisliKernel.Cli.usage
