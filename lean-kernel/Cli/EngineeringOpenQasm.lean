import Cli.Common
import Protocol.ExecutionView.CheckedEngineeringOpenQasm
import Protocol.ExecutionView.Native

/-! Separate native response for engineering-only canonical terminal target comparisons.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Cli
open Protocol.ExecutionView

private def readEngineeringOpenQasm (handle : IO.FS.Stream) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  for _ in [:Packet.maxPacketBytes+2] do
    if bytes.size > Packet.maxPacketBytes then throw (IO.userError "input limit")
    let chunk ← handle.read (min 4096 (Packet.maxPacketBytes + 1 - bytes.size)).toUSize
    if chunk.isEmpty then return bytes
    bytes := bytes ++ chunk
  throw (IO.userError "input limit")

def runEngineeringOpenQasm : IO UInt32 := do
  let bytes ← try readEngineeringOpenQasm (← IO.getStdin)
    catch _ =>
      IO.println "qleisli.engineering-openqasm-native 1\nerror\nformat"
      return (1 : UInt32)
  let (result,left) := (CheckedEngineeringOpenQasm.run bytes).run 10000000
  match result with
  | .error error =>
    IO.println ("qleisli.engineering-openqasm-native 1\nerror\n" ++ Native.errorCode error)
    return 1
  | .ok _ =>
    IO.println ("qleisli.engineering-openqasm-native 1\nengineering-checked\nexecution\n" ++
      toString (10000000-left))
    return 0

end QleisliKernel.Cli
