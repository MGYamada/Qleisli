import Cli.Common
import Protocol.Validity
import Protocol.NativeContract

/-! Fresh stdin validity checks for the single native production gate.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Cli

private def readValidity (handle : IO.FS.Stream) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  for _ in [:Protocol.Validity.maxPacketBytes+2] do
    if bytes.size > Protocol.Validity.maxPacketBytes then throw (IO.userError "input limit")
    let chunk ← handle.read (min 4096 (Protocol.Validity.maxPacketBytes + 1 - bytes.size)).toUSize
    if chunk.isEmpty then return bytes
    bytes := bytes ++ chunk
  throw (IO.userError "input limit")

def runValidity (contract : Bool := false) : IO UInt32 := do
  let bytes ← try readValidity (← IO.getStdin)
    catch _ =>
      IO.println "qleisli.qirf-native 1\nerror\nformat"
      return (1 : UInt32)
  let (result,left) := ((if contract then Protocol.NativeContract.check else Protocol.Validity.check) bytes).run 10000000
  match result with
  | .error error =>
    let code := match error with
      | .limit => "limit" | .request | .equation => "contract" | _ => "invalid_ir"
    IO.println ("qleisli.qirf-native 1\nerror\n" ++ code)
    return 1
  | .ok requested =>
    IO.println ("qleisli.qirf-native 1\naccepted\n" ++ toString (10000000-left) ++
      "\n" ++ if requested then "1" else "0")
    return 0

end QleisliKernel.Cli
