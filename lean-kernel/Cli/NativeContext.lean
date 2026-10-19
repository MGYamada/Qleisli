import Protocol.NativeContext

/-! Bounded IO for the pure context-aware native dispatcher.
Native compilation, IO and host transport remain explicit assumptions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Cli
open Protocol.ExecutionView

private def readNativeInput (handle : IO.FS.Stream) : IO (Except Gate.Error ByteArray) := do
  let mut bytes := ByteArray.empty
  for _ in [:Packet.maxPacketBytes+2] do
    if bytes.size > Packet.maxPacketBytes then return .error (.native .limit)
    let chunk ← handle.read (min 4096 (Packet.maxPacketBytes + 1 - bytes.size)).toUSize
    if chunk.isEmpty then return .ok bytes
    bytes := bytes ++ chunk
  return .error (.native .limit)

def runNativeContext (mode : Protocol.NativeContext.Mode) (requestedProduct : String) : IO UInt32 := do
  let input ← if requestedProduct == Protocol.productVersion then
      try readNativeInput (← IO.getStdin)
      catch _ => pure (.error .packet)
    else pure (.ok ByteArray.empty)
  let work := 10000000
  let (result,left) := match input with
    | .error error => (.error error,work)
    | .ok bytes => (Protocol.NativeContext.run mode requestedProduct bytes).run work
  let reply := Protocol.NativeContext.reply mode work result left
  IO.println (String.intercalate "\n" reply.lines)
  return if reply.success then 0 else 1

end QleisliKernel.Cli
