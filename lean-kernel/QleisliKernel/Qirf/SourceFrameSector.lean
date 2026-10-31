import QleisliKernel.Qirf.SourceInterval
import QleisliKernel.Qirf.SourceSector

/-! Original structural qmatch contexts with a complete caller frame. Reuse
the existing graph, original arm, controlled-body and exact sector gates. The
local two-port subject is the literal checked interval of the original root;
no alternate source or artifact is synthesized. Native/QDV version pairing
and ordinary compiler integration remain separate; this module issues no handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceFrameSector
open Finite
open Semantics.Exact Semantics.CarrierInterface
open PureInterval (Witness)

structure Codes (ports : NominalSector.Ports) where
  selectorIn : Witness (Carrier.ownerCode [ports.selectorIn])
  targetIn : Witness (Carrier.ownerCode [ports.targetIn])
  selectorOut : Witness (Carrier.ownerCode [ports.selectorOut])
  targetOut : Witness (Carrier.ownerCode [ports.targetOut])
  selectorLayout : Witness (Carrier.readOwner ports.selectorIn)
  targetLayout : Witness (Carrier.readOwner ports.targetIn)

def readCodes (ports : NominalSector.Ports) : WorkM (Codes ports) := do
  let si ← SourceTypes.NaturalAffine.witness (Carrier.ownerCode [ports.selectorIn])
  let ti ← SourceTypes.NaturalAffine.witness (Carrier.ownerCode [ports.targetIn])
  let so ← SourceTypes.NaturalAffine.witness (Carrier.ownerCode [ports.selectorOut])
  let to ← SourceTypes.NaturalAffine.witness (Carrier.ownerCode [ports.targetOut])
  let sl ← SourceTypes.NaturalAffine.witness (Carrier.readOwner ports.selectorIn)
  let tl ← SourceTypes.NaturalAffine.witness (Carrier.readOwner ports.targetIn)
  return ⟨si,ti,so,to,sl,tl⟩

theorem rootFresh {artifact order attached required roots rows}
    (root : Witness (Carrier.sourceRootWithRows artifact order attached required roots rows)) :
    CheckedGraph artifact (Array.replicate artifact.entries.size none) order.toList root.val.receipts := by
  obtain ⟨work,left,ran⟩ := root.property
  obtain ⟨before,checked⟩ := Carrier.sourceRootWithRows_result _ _ _ _ _ _ _ _ _ ran
  exact (Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ checked).fresh

abbrev Computed {α : Type} (action : WorkM α) (value : α) : Prop :=
  ∃ work left, action.run work = (.ok value,left)

structure Header (artifact : Artifact) (owner name : String) (offset : Nat)
    (programs : List SourceArm.Programs) (ports : NominalSector.Ports) where
  source : SourceTypes.QuantumArms.Table artifact.sources owner name offset ports.selectorIn.basis ports.targetIn.basis
  sourceRead : Computed (SourceTypes.QuantumArms.read artifact.sources owner name offset
    ports.selectorIn.basis ports.targetIn.basis) source
  original : SourceInterval.Prepared source.site ports.selectorIn.basis ports.targetIn.basis
  originalRead : Computed (SourceInterval.read source.site ports.selectorIn.basis ports.targetIn.basis) original
  bindings : List (SourceArm.Bound artifact owner ports.selectorIn.basis ports.targetIn.basis)
  bindingsRead : Computed (SourceArm.readAll artifact source.arms programs) bindings
  roots : List Nat
  rootsRead : Computed (SourceArm.readRoots artifact bindings) roots
  rows : List (String × String)
  rowsRead : Computed (SourceSector.readRowsWithSignature source original.operands.signature) rows

def readHeader (artifact : Artifact) (owner name : String) (offset : Nat)
    (programs : List SourceArm.Programs) (ports : NominalSector.Ports) :
    WorkM (Header artifact owner name offset programs ports) := do
  let source ← SourceTypes.NaturalAffine.witness
    (SourceTypes.QuantumArms.read artifact.sources owner name offset ports.selectorIn.basis ports.targetIn.basis)
  let original ← SourceTypes.NaturalAffine.witness
    (SourceInterval.read source.val.site ports.selectorIn.basis ports.targetIn.basis)
  let bindings ← SourceTypes.NaturalAffine.witness (SourceArm.readAll artifact source.val.arms programs)
  let roots ← SourceTypes.NaturalAffine.witness (SourceArm.readRoots artifact bindings.val)
  let rows ← SourceTypes.NaturalAffine.witness
    (SourceSector.readRowsWithSignature source.val original.val.operands.signature)
  return ⟨source.val,source.property,original.val,original.property,bindings.val,bindings.property,
    roots.val,roots.property,rows.val,rows.property⟩

structure Body (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    {owner name offset programs ports} (header : Header artifact owner name offset programs ports) where
  root : Validity.Root
  rootRead : Computed (Carrier.sourceRootWithRows artifact order attached required header.roots header.rows) root
  fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) order.toList root.receipts
  context : SourceInterval.Checked header.source.site ports.selectorIn.basis ports.targetIn.basis root.dependencies root.program
  contextRead : Computed (SourceInterval.checkFrom header.original root.dependencies root.program) context
  inputs : context.interval.selected = attached.inputs.map (·.port)
  outputs : context.interval.returned = attached.outputs.map (·.port)
  codes : Codes ports
  restriction : QleisliKernel.Raw.Sector.Retained
  restrictionRead : Computed (QleisliKernel.Raw.Sector.read root.dependencies
    [.bits codes.selectorLayout.val.bits] [.bits codes.targetLayout.val.bits]
    (PureInterval.fragment context.interval.selected context.interval.slice context.outputs)) restriction
  entries : List (SourceSector.RealizedArm artifact root.receipts owner ports.selectorIn.basis ports.targetIn.basis)
  entriesRead : Computed (header.bindings.mapM fun bound =>
    SourceSector.readEntry artifact root.receipts bound fresh) entries

def prepare (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    {owner name offset programs ports} (header : Header artifact owner name offset programs ports) :
    WorkM (Body artifact order attached required header) := do
  let codes ← readCodes ports
  let root ← SourceTypes.NaturalAffine.witness
    (Carrier.sourceRootWithRows artifact order attached required header.roots header.rows)
  let context ← SourceTypes.NaturalAffine.witness
    (SourceInterval.checkFrom header.original root.val.dependencies root.val.program)
  exactWork (Exact.charge (64*(attached.inputs.length+attached.outputs.length+1)))
  if inputs : context.val.interval.selected = attached.inputs.map (·.port) then
    if outputs : context.val.interval.returned = attached.outputs.map (·.port) then
      let restriction ← SourceTypes.NaturalAffine.witness
        (QleisliKernel.Raw.Sector.read root.val.dependencies [.bits codes.selectorLayout.val.bits]
          [.bits codes.targetLayout.val.bits]
          (PureInterval.fragment context.val.interval.selected context.val.interval.slice context.val.outputs))
      let entries ← SourceTypes.NaturalAffine.witness
        (header.bindings.mapM fun bound => SourceSector.readEntry artifact root.val.receipts bound (rootFresh root))
      return ⟨root.val,root.property,rootFresh root,context.val,context.property,
        inputs,outputs,codes,restriction.val,restriction.property,entries.val,entries.property⟩
    else throw .request
  else throw .request

structure Checked (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (owner name : String) (offset : Nat) (programs : List SourceArm.Programs) where
  ports : NominalSector.Ports
  portsRead : NominalSector.ports required = some ports
  interface : attached = required
  types : NominalSector.sameTypes required ports = true
  header : Header artifact owner name offset programs ports
  body : Body artifact order attached required header
  arms : List SectorArms.BoundArm
  armsRead : Computed (SectorArms.readAll artifact body.root.dependencies ports.targetIn.basis
    body.codes.targetLayout.val.bits body.codes.targetIn.val body.codes.targetOut.val body.codes.selectorLayout.val.labels.length
    (header.bindings.map (·.reference))) arms
  logical : List Matrix
  logicalRead : Computed (NominalSector.checkLogicals body.codes.targetIn.val body.codes.targetOut.val body.restriction.sectors
    body.codes.selectorLayout.val.labels (arms.map (·.checked.logical))) logical

/-- Keep the final equations parameterized by the already checked frame.
This prevents elaboration from unfolding the complete source/graph preparation. -/
def finish {artifact order attached required owner name offset programs}
    (ports : NominalSector.Ports) (portsRead : NominalSector.ports required = some ports)
    (interface : attached = required) (types : NominalSector.sameTypes required ports = true)
    (header : Header artifact owner name offset programs ports)
    (body : Body artifact order attached required header) :
    WorkM (Checked artifact order attached required owner name offset programs) := do
  let arms ← SourceTypes.NaturalAffine.witness
    (SectorArms.readAll artifact body.root.dependencies ports.targetIn.basis body.codes.targetLayout.val.bits
      body.codes.targetIn.val body.codes.targetOut.val body.codes.selectorLayout.val.labels.length (header.bindings.map (·.reference)))
  let logical ← SourceTypes.NaturalAffine.witness
    (NominalSector.checkLogicals body.codes.targetIn.val body.codes.targetOut.val body.restriction.sectors
      body.codes.selectorLayout.val.labels (arms.val.map (·.checked.logical)))
  return ⟨ports,portsRead,interface,types,header,body,arms.val,
    by with_reducible exact arms.property,logical.val,by with_reducible exact logical.property⟩

/-- Every dependency and arm is reconstructed from the original artifact in
one graph. A source context or locally valid interval alone cannot grant this
result; code, body, phase, controlled access and sector equations still run. -/
def check (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (owner name : String) (offset : Nat) (programs : List SourceArm.Programs) :
    WorkM (Checked artifact order attached required owner name offset programs) := do
  guard (NominalSector.shape attached required) .request
  SourceTypes.checkMany artifact.sources (NominalSector.forests attached required)
  match portsRead : NominalSector.ports required with
  | none => throw .request
  | some ports =>
    if interface : attached = required then
      if types : NominalSector.sameTypes required ports = true then
        let header ← readHeader artifact owner name offset programs ports
        let body ← prepare artifact order attached required header
        finish ports portsRead interface types header body
      else throw .request
    else throw .request

theorem Checked.originalRoot {artifact order attached required owner name offset programs}
    (checked : Checked artifact order attached required owner name offset programs) :
    ∃ work, Validity.SourceRootPostconditionFromRoots artifact order
      (Carrier.sourceRows attached required ++ checked.header.rows) checked.header.roots checked.body.root work := by
  obtain ⟨work,left,ran⟩ := checked.body.rootRead
  obtain ⟨before,verified⟩ := Carrier.sourceRootWithRows_result _ _ _ _ _ _ _ _ _ ran
  exact ⟨before,Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ verified⟩

theorem Checked.publicEffect {artifact order attached required owner name offset programs}
    (checked : Checked artifact order attached required owner name offset programs)
    (isPublic : checked.body.context.operands.signature.original.declaration.isPublic = true) :
    checked.body.context.operands.signature.original.parsedHeader.effect = some checked.body.root.program.effect :=
  checked.body.context.publicEffect isPublic

end QleisliKernel.Qirf.SourceFrameSector
