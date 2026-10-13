import Cli.Common
import Protocol.ExecutionView.Native

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Cli
open Protocol.ExecutionView

private def readHierarchyBytes (handle : IO.FS.Stream) (fuel : Nat)
    (initial : ByteArray) : IO (Except Code ByteArray) :=
  Nat.rec (motive := fun _ => ByteArray → IO (Except Code ByteArray))
    (fun _ => pure (.error .limit))
    (fun _ next bytes => do
      if bytes.size > Packet.maxPacketBytes then return .error .limit
      let remaining := Packet.maxPacketBytes + 1 - bytes.size
      let chunk ← handle.read (min 4096 remaining).toUSize
      if chunk.isEmpty then return .ok bytes
      next (bytes ++ chunk)) fuel initial

private def readPacket {α : Type} (parse : ByteArray → Except Protocol.Error α) :
    IO (Except String α) := do
  let input ← try
      readHierarchyBytes (← IO.getStdin) 1000001 ByteArray.empty
    catch _ => pure (.error .io)
  return match input with
    | .error .limit => .error "limit"
    | .error _ => .error "format"
    | .ok bytes => do
      let input ← (Packet.read bytes).mapError Native.errorCode
      if input.scope != .inspection then throw "format"
      match parse input.original with
      | .error .syntax => .error "format"
      | .error .limit => .error "limit"
      | .ok packet => .ok packet

private def failure (header code : String) : IO UInt32 := do
  IO.println (header ++ "\nerror\n" ++ code)
  return 1

private def runHierarchyMode (mode : CheckedHierarchy.Modes.Mode) (header : String) : IO UInt32 := do
  let input ← try readHierarchyBytes (← IO.getStdin) 1000001 ByteArray.empty
    catch _ => pure (.error .io)
  let bytes ← match input with
    | .error .limit => return (← failure header "limit")
    | .error _ => return (← failure header "format")
    | .ok bytes => pure bytes
  let (result,left) := (Native.hierarchy mode bytes).run 10000000
  match result with
  | .error error => failure header (match error with
      | .native error => Protocol.HierarchicalFinite.errorCode error
      | _ => Native.errorCode error)
  | .ok (scope,checked) =>
    IO.println (header ++ "\npending\n" ++ scope.name)
    IO.println checked.core.visits
    IO.println (10000000-left)
    IO.println checked.core.requests.size
    for request in checked.core.requests do IO.println request.index
    if mode != .inspect then
      let indices := if mode == .fourier then checked.core.hadamards else checked.core.pairs
      IO.println indices.length
      for index in indices do IO.println index
    if mode == .qpeInstrument then
      IO.println checked.core.hadamards.length
      for index in checked.core.hadamards do IO.println index
    return 0

def runHierarchy : IO UInt32 :=
  runHierarchyMode .inspect "qleisli.hierarchy-pending 4"

def runHierarchyRequest : IO UInt32 :=
  runHierarchyMode .request "qleisli.hierarchy-request-pending 4"

def runHierarchyFourier : IO UInt32 :=
  runHierarchyMode .fourier "qleisli.hierarchy-fourier-pending 4"

def runInstrument : IO UInt32 :=
  runHierarchyMode .instrument "qleisli.instrument-pending 4"

def runQpeInstrument : IO UInt32 :=
  runHierarchyMode .qpeInstrument "qleisli.qpe-instrument-pending 4"

private def readoutFailure (code : String) : IO UInt32 :=
  failure "qleisli.readout-result 2" code

/-- Check only the supplied readout slice. This result cannot stand in for
verification of a preceding circuit, source, initialization or QPE request. -/
def runReadout : IO UInt32 := do
  let packet ← match ← readPacket Protocol.Hierarchical.parseReadout with
    | .error code => return (← readoutFailure code)
    | .ok packet => pure packet
  match Hierarchical.Readout.check packet.request packet.packet packet.budget with
  | .error error => readoutFailure (match error with
      | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir")
  | .ok checked =>
    IO.println "qleisli.readout-result 2\nchecked"
    IO.println checked.visits
    return 0

private def preparationFailure (code : String) : IO UInt32 :=
  failure "qleisli.preparation-result 2" code

def runPreparation : IO UInt32 := do
  let packet ← match ← readPacket Protocol.Hierarchical.parsePreparation with
    | .error code => return (← preparationFailure code)
    | .ok packet => pure packet
  match Hierarchical.Preparation.check packet.request packet.packet packet.budget with
  | .error error => preparationFailure (match error with
      | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir")
  | .ok checked =>
    IO.println "qleisli.preparation-result 2\nchecked"
    IO.println checked.visits
    return 0

end QleisliKernel.Cli
