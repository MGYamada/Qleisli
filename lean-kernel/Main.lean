import Protocol.ExecutionView.CheckedContract
import Protocol.ExecutionView.CheckedCaller
import Protocol.ExecutionView.CheckedHierarchy
import Protocol.ExecutionView.Contracts
import Cli.Finite
import Cli.Hierarchical
import Cli.Validity
import Cli.EngineeringPure
import Cli.EngineeringInstrument
import Protocol.Product
import Protocol.ExecutionView.CheckedFinite

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

private def nativeMode (mode : String) : Option (IO UInt32) :=
  match mode with
  | "--qirf-native" => some QleisliKernel.Cli.runValidity
  | "--qirf-contract" => some (QleisliKernel.Cli.runValidity true)
  | "--engineering-pure-check" => some QleisliKernel.Cli.runEngineeringPure
  | "--qirf-engineering-instrument-native" => some QleisliKernel.Cli.runEngineeringInstrument
  | "--qpe-instrument-pending" => some QleisliKernel.Cli.runQpeInstrument
  | "--instrument-pending" => some QleisliKernel.Cli.runInstrument
  | "--readout-check" => some QleisliKernel.Cli.runReadout
  | "--preparation-check" => some QleisliKernel.Cli.runPreparation
  | "--hierarchy-fourier-pending" => some QleisliKernel.Cli.runHierarchyFourier
  | "--hierarchy-request-pending" => some QleisliKernel.Cli.runHierarchyRequest
  | "--hierarchy-pending" => some QleisliKernel.Cli.runHierarchy
  | _ => none

private def nativeVersionError (mode : String) : IO UInt32 := do
  IO.println ((if mode == "--engineering-pure-check" then "qleisli.engineering-pure-native 1"
    else if mode == "--qirf-engineering-instrument-native" then "qleisli.engineering-instrument-native 1"
    else "qleisli.qirf-native 2") ++ "\nerror\nversion")
  pure 1

def main (args : List String) : IO UInt32 :=
  match args with
  | [mode, version] =>
    match nativeMode mode with
    | some action =>
      if version == QleisliKernel.Protocol.productVersion then action
      else nativeVersionError mode
    | none => QleisliKernel.Cli.run mode version
  -- Native modes always require the explicitly paired product version, so
  -- version agreement is enforced here rather than by caller convention.
  | [mode] =>
    match nativeMode mode with
    | some _ => nativeVersionError mode
    | none => QleisliKernel.Cli.usage
  | ["--phase-layout", artifact, requirement] => QleisliKernel.Cli.runPhaseLayout artifact requirement
  | ["--layout-dag", artifact, requirement] => QleisliKernel.Cli.runLayoutDag artifact requirement
  | ["--layout", artifact, requirement] => QleisliKernel.Cli.runLayout artifact requirement
  | ["--phase-dag", artifact, requirement] => QleisliKernel.Cli.runDag artifact requirement
  | _ => QleisliKernel.Cli.usage
