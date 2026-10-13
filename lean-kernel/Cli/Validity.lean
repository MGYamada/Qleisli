import Cli.Common
import Protocol.ExecutionView.Native

/-! Fresh stdin validity checks for the single native production gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Cli
open Protocol.ExecutionView

private def readValidity (handle : IO.FS.Stream) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  for _ in [:Packet.maxPacketBytes+2] do
    if bytes.size > Packet.maxPacketBytes then throw (IO.userError "input limit")
    let chunk ← handle.read (min 4096 (Packet.maxPacketBytes + 1 - bytes.size)).toUSize
    if chunk.isEmpty then return bytes
    bytes := bytes ++ chunk
  throw (IO.userError "input limit")

def runValidity (contract : Bool := false) : IO UInt32 := do
  let bytes ← try readValidity (← IO.getStdin)
    catch _ =>
      IO.println "qleisli.qirf-native 2\nerror\nformat"
      return (1 : UInt32)
  let computation : Gate.CheckM (Packet.Scope × Bool) := do
    if contract then
      let (scope,_) ← Native.contract bytes
      return (scope,true)
    else
      let result ← Native.ordinary bytes
      return (result.scope,result.requested)
  let (result,left) := computation.run 10000000
  match result with
  | .error error =>
    IO.println ("qleisli.qirf-native 2\nerror\n" ++ Native.errorCode error)
    return 1
  | .ok (scope,requested) =>
    IO.println ("qleisli.qirf-native 2\naccepted\n" ++ scope.name ++ "\n" ++ toString (10000000-left) ++
      "\n" ++ if requested then "1" else "0")
    return 0

end QleisliKernel.Cli
