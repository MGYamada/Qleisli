import QleisliKernel.Qirf.PureInterval
import QleisliKernel.SourceTypes.QuantumArms
import QleisliKernel.Qirf.SelectionContract

/-! Shared selection header and exact equation adapter.
The header is parameterized by the original checked signature and event, not by
one particular source traversal. Core acceptance routines are unchanged.
SequenceSector and ContextSector use this single implementation. It grants
no standalone handle, guarantee or full source-preservation theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SelectionCore
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Qirf
open Finite Semantics.Exact Semantics.CarrierInterface
open QleisliKernel.Qirf.PureInterval (Witness)
abbrev Request := SelectionContract.Request
abbrev Event := SourceTypes.QuantumSequence.Event

structure Header (artifact : Artifact) {owner name} (signature : SourceTypes.QuantumSignature.Checked artifact.sources owner name) where
  event : Event
  request : Request
  ports : NominalSector.Ports
  portsRead : NominalSector.ports request.required = some ports
  interface : request.attached = request.required
  types : NominalSector.sameTypes request.required ports = true
  roles : ports.selectorIn.basis = event.selector.basis ∧ ports.targetIn.basis = event.target.basis
  table : Witness (SourceTypes.QuantumArms.readArms signature.original request.position.offset
    ports.selectorIn.basis ports.targetIn.basis)
  original : table.val.site.original.source = signature.original.source ∧ table.val.site.parsed = event.parsed
  bindings : Witness (SourceArm.readAll artifact table.val.arms request.programs)
  roots : Witness (SourceArm.readRoots artifact bindings.val)
  rows : Witness (SourceSector.readRowsWithSignature table.val signature)

def readHeader (artifact : Artifact) {owner name} (signature : SourceTypes.QuantumSignature.Checked artifact.sources owner name)
    (pair : Event × Request) : WorkM (Header artifact signature) := do
  let event := pair.1
  let request := pair.2
  guard (NominalSector.shape request.attached request.required) .request
  SourceTypes.checkMany artifact.sources (NominalSector.forests request.attached request.required)
  exactWork (Exact.charge (16*(SourceSequence.eventFields event+signature.original.source.utf8ByteSize+1)))
  match portsRead : NominalSector.ports request.required with
  | none => throw .request
  | some ports =>
    if interface : request.attached = request.required then
      if types : NominalSector.sameTypes request.required ports = true then
        if roles : ports.selectorIn.basis = event.selector.basis ∧ ports.targetIn.basis = event.target.basis then
          let table ← SourceTypes.NaturalAffine.witness (SourceTypes.QuantumArms.readArms signature.original
            request.position.offset ports.selectorIn.basis ports.targetIn.basis)
          if original : table.val.site.original.source = signature.original.source ∧
              table.val.site.parsed = event.parsed then
            let bindings ← SourceTypes.NaturalAffine.witness (SourceArm.readAll artifact table.val.arms request.programs)
            let roots ← SourceTypes.NaturalAffine.witness (SourceArm.readRoots artifact bindings.val)
            let rows ← SourceTypes.NaturalAffine.witness (SourceSector.readRowsWithSignature table.val signature)
            return ⟨event,request,ports,portsRead,interface,types,roles,table,original,bindings,roots,rows⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request

structure Prepared {artifact owner name}
    {signature : SourceTypes.QuantumSignature.Checked artifact.sources owner name}
    (header : Header artifact signature) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    {inputs outputs : List Nat}
    (interval : PureInterval.Many.Checked 2 root.dependencies root.program
      header.request.position.start header.request.position.count inputs outputs
      [header.event.selector,header.event.target]) where
  inputPorts : interval.selected = header.request.attached.inputs.map (·.port)
  outputPorts : interval.returned = header.request.attached.outputs.map (·.port)
  codes : SourceFrameSector.Codes header.ports
  restriction : Witness (QleisliKernel.Raw.Sector.read root.dependencies
    [.bits codes.selectorLayout.val.bits] [.bits codes.targetLayout.val.bits]
    (PureInterval.fragment interval.selected interval.slice outputs))
  entries : Witness (header.bindings.val.mapM fun binding =>
    SourceSector.readEntry artifact root.receipts binding fresh)

def prepare {artifact owner name}
    {signature : SourceTypes.QuantumSignature.Checked artifact.sources owner name}
    (header : Header artifact signature) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    {inputs outputs : List Nat}
    (interval : PureInterval.Many.Checked 2 root.dependencies root.program
      header.request.position.start header.request.position.count inputs outputs
      [header.event.selector,header.event.target]) :
    WorkM (Prepared header root fresh interval) := do
  exactWork (Exact.charge (64*(header.request.attached.inputs.length+
    header.request.attached.outputs.length+1)))
  if inputPorts : interval.selected = header.request.attached.inputs.map (·.port) then
    if outputPorts : interval.returned = header.request.attached.outputs.map (·.port) then
      let codes ← SourceFrameSector.readCodes header.ports
      let restriction ← SourceTypes.NaturalAffine.witness (QleisliKernel.Raw.Sector.read root.dependencies
        [.bits codes.selectorLayout.val.bits] [.bits codes.targetLayout.val.bits]
        (PureInterval.fragment interval.selected interval.slice outputs))
      let entries ← SourceTypes.NaturalAffine.witness (header.bindings.val.mapM fun binding =>
        SourceSector.readEntry artifact root.receipts binding fresh)
      return ⟨inputPorts,outputPorts,codes,restriction,entries⟩
    else throw .request
  else throw .request

/-- Equation result fields keep their executable witnesses separate to avoid
normalizing the entire preparation while elaborating later dependent fields. -/
structure Equations {artifact owner name}
    {signature : SourceTypes.QuantumSignature.Checked artifact.sources owner name}
    {header : Header artifact signature} {root : Validity.Root}
    {nodes : List Nat}
    {fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts}
    {inputs outputs : List Nat}
    {interval : PureInterval.Many.Checked 2 root.dependencies root.program
      header.request.position.start header.request.position.count inputs outputs
      [header.event.selector,header.event.target]}
    (prepared : Prepared header root fresh interval) where
  arms : List SectorArms.BoundArm
  armsRead : SelectionContract.Computed (SectorArms.readAll artifact root.dependencies header.ports.targetIn.basis
    prepared.codes.targetLayout.val.bits prepared.codes.targetIn.val prepared.codes.targetOut.val
    prepared.codes.selectorLayout.val.labels.length (header.bindings.val.map (·.reference))) arms
  logical : List Matrix
  logicalRead : SelectionContract.Computed (NominalSector.checkLogicals
    prepared.codes.targetIn.val prepared.codes.targetOut.val prepared.restriction.val.sectors
    prepared.codes.selectorLayout.val.labels (arms.map (·.checked.logical))) logical

def finish {artifact owner name}
    {signature : SourceTypes.QuantumSignature.Checked artifact.sources owner name}
    {header : Header artifact signature} {root : Validity.Root}
    {nodes : List Nat}
    {fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts}
    {inputs outputs : List Nat}
    {interval : PureInterval.Many.Checked 2 root.dependencies root.program
      header.request.position.start header.request.position.count inputs outputs
      [header.event.selector,header.event.target]}
    (prepared : Prepared header root fresh interval) : WorkM (Equations prepared) := do
  let arms ← SourceTypes.NaturalAffine.witness (SectorArms.readAll artifact root.dependencies
    header.ports.targetIn.basis prepared.codes.targetLayout.val.bits prepared.codes.targetIn.val
    prepared.codes.targetOut.val prepared.codes.selectorLayout.val.labels.length
    (header.bindings.val.map (·.reference)))
  let logical ← SourceTypes.NaturalAffine.witness (NominalSector.checkLogicals
    prepared.codes.targetIn.val prepared.codes.targetOut.val prepared.restriction.val.sectors
    prepared.codes.selectorLayout.val.labels (arms.val.map (·.checked.logical)))
  return ⟨arms.val,by with_reducible exact arms.property,
    logical.val,by with_reducible exact logical.property⟩

structure Checked {artifact owner name}
    {signature : SourceTypes.QuantumSignature.Checked artifact.sources owner name}
    (header : Header artifact signature) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    {inputs outputs : List Nat}
    (interval : PureInterval.Many.Checked 2 root.dependencies root.program
      header.request.position.start header.request.position.count inputs outputs
      [header.event.selector,header.event.target]) where
  prepared : Prepared header root fresh interval
  equations : Equations prepared

/-- Finish against an already checked literal interval and fresh graph.
The compiled arm, independent control, code and full phase equations remain the
same executable checks used by SourceFrameSector and SequenceSector. -/
def check {artifact owner name}
    {signature : SourceTypes.QuantumSignature.Checked artifact.sources owner name}
    (header : Header artifact signature) (root : Validity.Root)
    {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes root.receipts)
    {inputs outputs : List Nat}
    (interval : PureInterval.Many.Checked 2 root.dependencies root.program
      header.request.position.start header.request.position.count inputs outputs
      [header.event.selector,header.event.target]) :
    WorkM (Checked header root fresh interval) := do
  let prepared ← prepare header root fresh interval
  let equations ← finish prepared
  return ⟨prepared,equations⟩

end QleisliKernel.Qirf.SelectionCore
