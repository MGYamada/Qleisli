import Cli.NativeContext

/-! Historical response projection for offline differential tests.
The released checker does not use this executable.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
def main (args : List String) : IO UInt32 :=
  match args with
  | [mode, version] =>
    match QleisliKernel.Protocol.NativeContext.Mode.parse mode with
    | some selected => QleisliKernel.Cli.runNativeContext selected version
    | none => pure 2
  | _ => pure 2
