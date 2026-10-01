import Protocol
import QleisliKernel.Hierarchical.QpeInstrument

/-! Temporary diagnostic harness. Actual executable component inspectors are
evaluated individually under their existing 2,000,000 ceiling. Their sum is a
diagnostic estimate only. Actual acceptance is the unmodified checkAll result.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
open QleisliKernel.Hierarchical Artifact
set_option maxRecDepth 20000

def showResult {α : Type} (name stage : String) (result : Except Error α)
    (visits : α → Nat) : IO Unit := do
  match result with
  | .error e => IO.println s!"{name}|{stage}|error|{repr e}"
  | .ok p => IO.println s!"{name}|{stage}|ok|{visits p}"

def profile (name : String) (request : QpeInstrument.Request)
    (packet : QpeInstrument.Packet) : IO Unit := do
  let artifact := packet.circuit.artifact
  let schedule := request.circuit.circuit
  let candidate := packet.circuit.candidate
  IO.println s!"{name}|graph|{artifact.definitions.size}|{artifact.meanings.size}|{artifact.encodings.size}|{artifact.proofs.size}|{packet.circuit.order.size}"
  match QpeInstrument.checkAll request packet with
  | .error e => IO.println s!"{name}|actual-instrument|error|{repr e.kind}|{repr e.atNode}"
  | .ok p =>
    let hadamards := ((candidate.hadamards.toList.map (·.index)) ++
      p.circuit.schedule.inverse.fourier.body.requests.map (·.leafIndex)).eraseDups
    IO.println s!"{name}|actual-instrument|ok|{p.visits}|{p.circuit.artifact.state.requests.size}|{p.circuit.provider.requests.length}|{hadamards.length}"
  match QpeRoot.checkAll request.circuit packet.circuit with
  | .error e => IO.println s!"{name}|actual-qpe-root|error|{repr e.kind}|{repr e.atNode}"
  | .ok p => IO.println s!"{name}|actual-qpe-root|ok|{p.visits}"
  match Conditional.checkAll artifact packet.circuit.order with
  | .error e => IO.println s!"{name}|conditional|error|{repr e.kind}|{repr e.atNode}"
  | .ok p => IO.println s!"{name}|conditional|ok|{p.state.visits}|{p.typed.totalVisits}|{p.typed.nodes.totalVisits}|{p.typed.nodes.prepared.totalVisits}|{p.state.requests.size}"
  IO.println s!"{name}|root-charge|{QpeRoot.charge request.circuit}"
  showResult name "provider-isolated" (Root.inspect
    (QpeRoot.providerArtifact request.circuit packet.circuit) request.circuit.provider
    packet.circuit.pairs packet.circuit.pairOrder 2000000) (·.visits)
  IO.println s!"{name}|schedule-work-charge|{QpeSchedule.workCharge artifact schedule candidate}"
  showResult name "schedule-isolated" (QpeSchedule.inspect artifact schedule candidate 2000000) (·.visits)
  showResult name "parts-isolated" (QpeSchedule.checkParts artifact schedule candidate 2000000
    (List.range schedule.phase.size)) (·.visits)
  for axis in List.range schedule.phase.size do
    match candidate.hadamards[axis]?,candidate.powers[axis]?,candidate.powerOrders[axis]? with
    | some h,some power,some order =>
      match QpeSchedule.checkPart artifact schedule h power axis order 2000000 with
      | .error e => IO.println s!"{name}|power|{axis}|error|{repr e}"
      | .ok p => IO.println s!"{name}|power|{axis}|ok|{p.visits}|{p.power.wiring.visits}|{order.size}"
    | _,_,_ => IO.println s!"{name}|power|{axis}|missing"
  match QpeSchedule.checkInverse artifact schedule.phase.size candidate.inverseFourier
      candidate.fourierOrder 2000000 with
  | .error e => IO.println s!"{name}|inverse-isolated|error|{repr e}"
  | .ok p => IO.println s!"{name}|inverse-isolated|ok|{p.visits}|{p.fourier.body.visits}|{p.fourier.wiring.visits}|{candidate.fourierOrder.size}"
  let atoms := QpeSchedule.atoms candidate
  match CircuitTrace.inspect artifact atoms candidate.traceOrder 2000000 with
  | .error e => IO.println s!"{name}|trace-isolated|error|{repr e}"
  | .ok p => IO.println s!"{name}|trace-isolated|ok|{p.visits}|{candidate.traceOrder.size}"
  IO.println s!"{name}|instrument-charge|{QpeInstrument.charge request packet}"
  showResult name "preparation-isolated" (Preparation.check request.preparation packet.preparation 2000000) (·.visits)
  showResult name "readout-isolated" (Readout.check request.readout packet.readout 2000000) (·.visits)

def main (args : List String) : IO UInt32 := do
  for file in args do
    let bytes ← IO.FS.readBinFile file
    match QleisliKernel.Protocol.Hierarchical.parseQpeInstrument bytes with
    | .error e => IO.println s!"{file}|parse|error|{repr e}"
    | .ok input => profile file input.request input.packet
  return 0
