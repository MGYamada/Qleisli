import Protocol.ExecutionView.CheckedContract
import Protocol.ExecutionView.CheckedCaller
import Protocol.ExecutionView.CheckedHierarchy
import Protocol.ExecutionView.Contracts
import Cli.Finite
import Cli.NativeContext
import Cli.Validity
import Cli.Hierarchical
import Cli.EngineeringPure
import Cli.EngineeringPureTensor
import Cli.EngineeringInstrument
import Cli.EngineeringOpenQasm
import Protocol.Product
import Protocol.ExecutionView.CheckedFinite
import Protocol.ExecutionView.CheckedQmatch
import Protocol.NativeContext.Bindings

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

def main (args : List String) : IO UInt32 :=
  match args with
  | [mode, version] =>
    match QleisliKernel.Protocol.NativeContext.Mode.parse mode with
    | some selected => QleisliKernel.Cli.runNativeContext selected version
    | none => QleisliKernel.Cli.run mode version
  -- Native modes always require the explicitly paired product version, so
  -- version agreement is enforced here rather than by caller convention.
  | [mode] =>
    match QleisliKernel.Protocol.NativeContext.Mode.parse mode with
    | some selected => QleisliKernel.Cli.runNativeContext selected ""
    | none => QleisliKernel.Cli.usage
  | ["--phase-layout", artifact, requirement] => QleisliKernel.Cli.runPhaseLayout artifact requirement
  | ["--layout-dag", artifact, requirement] => QleisliKernel.Cli.runLayoutDag artifact requirement
  | ["--layout", artifact, requirement] => QleisliKernel.Cli.runLayout artifact requirement
  | ["--phase-dag", artifact, requirement] => QleisliKernel.Cli.runDag artifact requirement
  | _ => QleisliKernel.Cli.usage
