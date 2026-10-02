import Cli.Common
import Protocol.HierarchicalFinite

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Cli

private def readHierarchyBytes (handle : IO.FS.Stream) (fuel : Nat)
    (initial : ByteArray) : IO (Except Code ByteArray) :=
  Nat.rec (motive := fun _ => ByteArray → IO (Except Code ByteArray))
    (fun _ => pure (.error .limit))
    (fun _ next bytes => do
      if bytes.size > Protocol.Hierarchical.maxBridgeBytes then return .error .limit
      let remaining := Protocol.Hierarchical.maxBridgeBytes + 1 - bytes.size
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
    | .ok bytes => match parse bytes with
      | .error .syntax => .error "format"
      | .error .limit => .error "limit"
      | .ok packet => .ok packet

private def failure (header code : String) : IO UInt32 := do
  IO.println (header ++ "\nerror\n" ++ code)
  return 1

private def hierarchyFailure (code : String) : IO UInt32 :=
  failure "qleisli.hierarchy-pending 3" code

/-- Fresh whole-artifact inspection, including native original-QIRF checks.
The result remains experimental, not production verification authority. -/
def runHierarchy : IO UInt32 := do
  let artifact ← match ← readPacket Protocol.Hierarchical.parse with
    | .error code => return (← hierarchyFailure code)
    | .ok packet => pure packet
  match Hierarchical.Conditional.checkAll artifact.1 artifact.2 with
  | .error error => hierarchyFailure (match error.kind with
      | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir")
  | .ok pending =>
    let (result,left) := (Protocol.HierarchicalFinite.checkLeaves pending.state.requests).run 10000000
    match result with
    | .error error => return (← hierarchyFailure (Protocol.HierarchicalFinite.errorCode error))
    | .ok _ => pure ()
    IO.println "qleisli.hierarchy-pending 3\npending"
    IO.println pending.state.visits
    IO.println (10000000 - left)
    IO.println pending.state.requests.size
    for request in pending.state.requests do IO.println request.index
    return 0

private def requestFailure (code : String) : IO UInt32 :=
  failure "qleisli.hierarchy-request-pending 3" code

/-- Fresh native binding of original QIRF leaves and independent request
matrices under one shared exact-work allowance. -/
def runHierarchyRequest : IO UInt32 := do
  let packet ← match ← readPacket Protocol.Hierarchical.parseRequest with
    | .error code => return (← requestFailure code)
    | .ok packet => pure packet
  match Hierarchical.Root.checkAll packet.artifact packet.order packet.request packet.pairs packet.pairOrder with
  | .error error => requestFailure (match error.kind with
      | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir")
  | .ok checked =>
    let (result, left) := (do
      Protocol.HierarchicalFinite.checkLeaves checked.artifact.state.requests
      Protocol.HierarchicalFinite.checkPairs packet.artifact
        packet.request packet.pairs checked.binding.requests).run 10000000
    match result with
    | .error error => return (← requestFailure (Protocol.HierarchicalFinite.errorCode error))
    | .ok _ => pure ()
    IO.println "qleisli.hierarchy-request-pending 3\npending"
    IO.println (checked.artifact.state.visits + checked.binding.visits)
    IO.println (10000000 - left)
    IO.println checked.artifact.state.requests.size
    for request in checked.artifact.state.requests do IO.println request.index
    IO.println checked.binding.requests.length
    for index in checked.binding.requests do IO.println index
    return 0

private def fourierFailure (code : String) : IO UInt32 :=
  failure "qleisli.hierarchy-fourier-pending 3" code

/-- Fresh full-artifact and named Fourier inspection with phase-fixed H.
The producer cannot redefine H by changing its own finite description. -/
def runHierarchyFourier : IO UInt32 := do
  let packet ← match ← readPacket Protocol.Hierarchical.parseFourier with
    | .error code => return (← fourierFailure code)
    | .ok packet => pure packet
  match Hierarchical.FourierRoot.checkAll packet.artifact packet.order packet.request packet.wiringOrder with
  | .error error => fourierFailure (match error.kind with
      | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir")
  | .ok checked =>
    let (result,left) := (do
      Protocol.HierarchicalFinite.checkLeaves checked.artifact.state.requests
      Protocol.HierarchicalFinite.checkHadamards packet.artifact
        (checked.binding.body.requests.map Hierarchical.Hadamard.Request.leafIndex)).run 10000000
    match result with
    | .error error => return (← fourierFailure (Protocol.HierarchicalFinite.errorCode error))
    | .ok _ => pure ()
    IO.println "qleisli.hierarchy-fourier-pending 3\npending"
    IO.println (checked.artifact.state.visits + checked.binding.visits)
    IO.println (10000000 - left)
    IO.println checked.artifact.state.requests.size
    for request in checked.artifact.state.requests do IO.println request.index
    IO.println checked.binding.body.requests.length
    for request in checked.binding.body.requests do IO.println request.leafIndex
    return 0

private def readoutFailure (code : String) : IO UInt32 :=
  failure "qleisli.readout-result 1" code

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
    IO.println "qleisli.readout-result 1\nchecked"
    IO.println checked.visits
    return 0

private def preparationFailure (code : String) : IO UInt32 :=
  failure "qleisli.preparation-result 1" code

def runPreparation : IO UInt32 := do
  let packet ← match ← readPacket Protocol.Hierarchical.parsePreparation with
    | .error code => return (← preparationFailure code)
    | .ok packet => pure packet
  match Hierarchical.Preparation.check packet.request packet.packet packet.budget with
  | .error error => preparationFailure (match error with
      | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir")
  | .ok checked =>
    IO.println "qleisli.preparation-result 1\nchecked"
    IO.println checked.visits
    return 0

private def instrumentFailure (code : String) : IO UInt32 :=
  failure "qleisli.instrument-pending 3" code

/-- Fresh composition of initialization, native finite checks and readout.
No host finite acceptance decision is consumed by this native mode. -/
def runInstrument : IO UInt32 := do
  let packet ← match ← readPacket Protocol.Hierarchical.parseInstrument with
    | .error code => return (← instrumentFailure code)
    | .ok packet => pure packet
  match Hierarchical.Instrument.checkAll packet.request packet.packet with
  | .error error => instrumentFailure (match error.kind with
      | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir")
  | .ok pending =>
    let (result, left) := (do
      Protocol.HierarchicalFinite.checkLeaves pending.circuit.artifact.state.requests
      Protocol.HierarchicalFinite.checkPairs packet.packet.artifact
        packet.request.circuit packet.packet.pairs pending.circuit.binding.requests).run 10000000
    match result with
    | .error error => return (← instrumentFailure (Protocol.HierarchicalFinite.errorCode error))
    | .ok _ => pure ()
    IO.println "qleisli.instrument-pending 3\npending"
    IO.println pending.visits
    IO.println (10000000 - left)
    IO.println pending.circuit.artifact.state.requests.size
    for request in pending.circuit.artifact.state.requests do IO.println request.index
    IO.println pending.circuit.binding.requests.length
    for index in pending.circuit.binding.requests do IO.println index
    return 0

private def qpeInstrumentFailure (code : String) : IO UInt32 :=
  failure "qleisli.qpe-instrument-pending 3" code

/-- Every original-QIRF leaf, independent provider pair and exact H role is
checked natively. This mode enables no external schema or production seal. -/
def runQpeInstrument : IO UInt32 := do
  let packet ← match ← readPacket Protocol.Hierarchical.parseQpeInstrument with
    | .error code => return (← qpeInstrumentFailure code)
    | .ok packet => pure packet
  match Hierarchical.QpeInstrument.checkAll packet.request packet.packet with
  | .error error => qpeInstrumentFailure (match error.kind with
      | .limit => "limit" | .contract => "contract" | .invalidIr => "invalid_ir")
  | .ok pending =>
    let hadamards := ((packet.packet.circuit.candidate.hadamards.toList.map (·.index)) ++
      pending.circuit.schedule.inverse.fourier.body.requests.map (·.leafIndex)).eraseDups
    let (result, left) := (do
      Protocol.HierarchicalFinite.checkLeaves pending.circuit.artifact.state.requests
      Protocol.HierarchicalFinite.checkPairs packet.packet.circuit.artifact
        packet.request.circuit.provider packet.packet.circuit.pairs pending.circuit.provider.requests
      Protocol.HierarchicalFinite.checkHadamards packet.packet.circuit.artifact hadamards).run 10000000
    match result with
    | .error error => return (← qpeInstrumentFailure (Protocol.HierarchicalFinite.errorCode error))
    | .ok _ => pure ()
    IO.println "qleisli.qpe-instrument-pending 3\npending"
    IO.println pending.visits
    IO.println (10000000 - left)
    IO.println pending.circuit.artifact.state.requests.size
    for request in pending.circuit.artifact.state.requests do IO.println request.index
    IO.println pending.circuit.provider.requests.length
    for index in pending.circuit.provider.requests do IO.println index
    IO.println hadamards.length
    for index in hadamards do IO.println index
    return 0

end QleisliKernel.Cli
