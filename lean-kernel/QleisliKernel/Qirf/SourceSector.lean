import QleisliKernel.Qirf.SourceArm
import QleisliKernel.SourceTypes.QuantumBody
import QleisliKernel.Semantics.RawOwnerFlow
import QleisliKernel.Raw.OwnerFlow

/-! Informed original source/IR arm coupling. Source rows and roots are derived
from fresh queries and actual program subjects, never transport coverage flags.
General selector/target expressions, native/QDV dispatch and accepted handles
remain separate obligations; no source execution route is enabled here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceSector
open Semantics.Exact Semantics.CarrierInterface Semantics.FiniteCarrier Finite

abbrev Programs := SourceArm.Programs

/-- The independent role run consumes the literal original Raw operations.
The bound counts full source identities before comparing the final role list;
no producer-proposed owner map is accepted. -/
def readOwnerReturn (inputs outputs : List Semantics.SourceOwners.Owner)
    (program : Semantics.Raw.Program) :
    WorkM (PLift (Semantics.RawOwnerFlow.Returns inputs program outputs)) :=
  Raw.OwnerFlow.check inputs outputs program

/-- Factoring the shared checker preserves successes, errors and remaining work. -/
theorem readOwnerReturn_shared (inputs outputs : List Semantics.SourceOwners.Owner)
    (program : Semantics.Raw.Program) :
    readOwnerReturn inputs outputs program = Raw.OwnerFlow.check inputs outputs program := rfl

private def typeRowCount {sources} (read : SourceTypes.TypeRead sources) : Nat :=
  read.resolutions.foldl (fun count query => count + query.result.visited.length) 0

private def armRowCount {sources owner selector target}
    (arm : SourceTypes.QuantumArms.BoundArm sources owner selector target) : Nat :=
  (match arm.label.typeQuery with | none => 0 | some query => typeRowCount query) +
    arm.operation.resolution.visited.length + 1 +
    arm.operation.signature.parameterReads.foldl (fun count ty => count+typeRowCount ty) 0 +
    arm.operation.signature.resultReads.foldl (fun count ty => count+typeRowCount ty) 0

structure CanonicalOperands {sources owner name offset}
    (site : SourceTypes.QuantumMatch.Site sources owner name offset)
    (selector target : Semantics.FiniteCarrier.Basis) where
  read : SourceTypes.QuantumOperands.Checked site selector target
  body : SourceTypes.QuantumBody.Checked read
  declaredEffect : read.signature.original.parsedHeader.effect = none ∨
    read.signature.original.parsedHeader.effect = some .unitary
  inputOrder : read.signature.inputs = [selector,target]
  outputOrder : read.signature.outputs = [selector,target]
  selectorOrdinal : read.selector.ordinal = 0
  targetOrdinal : read.target.ordinal = 1

/-- Read the complete structural source body and retain its actual returned
roles. The independent Raw role run and physical sector gates must match that
return. Equal widths and empty wire lists cannot erase its permutation.
General call-site expressions/frames still need their own checked mapping. -/
def readOperands {sources owner name offset}
    (site : SourceTypes.QuantumMatch.Site sources owner name offset)
    (selector target : Semantics.FiniteCarrier.Basis) : WorkM (CanonicalOperands site selector target) := do
  let read ← SourceTypes.QuantumOperands.read site selector target
  if mapping : read.signature.inputs = [selector,target] ∧ read.signature.outputs = [selector,target] ∧
      read.selector.ordinal = 0 ∧ read.target.ordinal = 1 then
    if effect : read.signature.original.parsedHeader.effect = none ∨
        read.signature.original.parsedHeader.effect = some .unitary then
      let body ← SourceTypes.QuantumBody.read read
      return ⟨read,body,effect,mapping.1,mapping.2.1,mapping.2.2.1,mapping.2.2.2⟩
    else throw .request
  else throw .request

theorem CanonicalOperands.publicUnitary {sources owner name offset selector target}
    {site : SourceTypes.QuantumMatch.Site sources owner name offset}
    (operands : CanonicalOperands site selector target)
    (isPublic : operands.read.signature.original.declaration.isPublic = true) :
    operands.read.signature.original.parsedHeader.effect = some .unitary := by
  have present := operands.read.signature.publicEffect isPublic
  rcases operands.declaredEffect with absent | exactEffect
  · simp [absent] at present
  · exact exactEffect

def sourceRowsWithSignature {sources owner name offset selector target}
    (table : SourceTypes.QuantumArms.Table sources owner name offset selector target)
    (signature : SourceTypes.QuantumSignature.Checked sources owner name) : List (String × String) :=
  ((owner,table.site.original.source) :: table.arms.flatMap (·.sourceRows) ++
    signature.sourceRows).eraseDups

def sourceRows {sources owner name offset selector target}
    (table : SourceTypes.QuantumArms.Table sources owner name offset selector target)
    (operands : CanonicalOperands table.site selector target) : List (String × String) :=
  sourceRowsWithSignature table operands.read.signature

/-- Count borrowed provenance paths before allocating or deduplicating rows.
Every string compared is bounded by the original source table; the quadratic
charge precedes construction. Source queries do not cover unused helper rows. -/
def readRowsWithSignature {sources owner name offset selector target}
    (table : SourceTypes.QuantumArms.Table sources owner name offset selector target)
    (signature : SourceTypes.QuantumSignature.Checked sources owner name) : WorkM (List (String × String)) := do
  guard (sources.size ≤ 128) .limit
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  guard (bytes ≤ 1048576) .limit
  let count := 2 + table.arms.foldl (fun total arm => total+armRowCount arm) 0 +
    (signature.parameterReads ++ signature.resultReads).foldl
      (fun total ty => total+typeRowCount ty) 0
  exactWork (Exact.charge (8*(bytes+sources.size+1)*(count+1)^2))
  return sourceRowsWithSignature table signature

def readRows {sources owner name offset selector target}
    (table : SourceTypes.QuantumArms.Table sources owner name offset selector target)
    (operands : CanonicalOperands table.site selector target) : WorkM (List (String × String)) :=
  readRowsWithSignature table operands.read.signature

structure RealizedArm (artifact : Artifact) (slots : Slots) (owner : String)
    (selector target : Semantics.FiniteCarrier.Basis) where
  bound : SourceArm.Bound artifact owner selector target
  checked : SourceArm.Realized artifact slots bound

def readEntry (artifact : Artifact) (slots : Slots) {owner selector target}
    (bound : SourceArm.Bound artifact owner selector target) {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes slots) :
    WorkM (RealizedArm artifact slots owner selector target) := do
  let checked ← SourceArm.realize artifact slots bound fresh
  return ⟨bound,checked⟩

theorem readEntry_bound (artifact : Artifact) (slots : Slots) {owner selector target}
    (bound : SourceArm.Bound artifact owner selector target) {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes slots)
    (result : RealizedArm artifact slots owner selector target) (work left : Nat)
    (ok : (readEntry artifact slots bound fresh).run work = (.ok result,left)) : result.bound = bound := by
  obtain ⟨checked,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  have same := (pure_success _ _ _ _ h).1
  subst result
  rfl

structure Checked (artifact : Artifact) (owner name : String) (offset : Nat) where
  ports : NominalSector.Ports
  source : SourceTypes.QuantumArms.Table artifact.sources owner name offset
    ports.selectorIn.basis ports.targetIn.basis
  operands : CanonicalOperands source.site ports.selectorIn.basis ports.targetIn.basis
  bindings : List (SourceArm.Bound artifact owner ports.selectorIn.basis ports.targetIn.basis)
  references : List SectorArm.Reference
  roots : List Nat
  rows : List (String × String)
  subject : NominalSector.Prepared
  sourceOwners : Semantics.RawOwnerFlow.Returns [operands.read.selector,operands.read.target]
    subject.program (Semantics.SourceOwners.valueOwners operands.body.outcome.value)
  entries : List (RealizedArm artifact subject.root.receipts owner ports.selectorIn.basis ports.targetIn.basis)
  arms : List SectorArms.BoundArm
  logical : List Matrix

def check (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (owner name : String) (offset : Nat) (programs : List Programs) :
    WorkM (Checked artifact owner name offset) := do
  let ports ← lift (readOption (NominalSector.ports required))
  let source ← SourceTypes.QuantumArms.read artifact.sources owner name offset
    ports.selectorIn.basis ports.targetIn.basis
  let operands ← readOperands source.site ports.selectorIn.basis ports.targetIn.basis
  let bindings ← SourceArm.readAll artifact source.arms programs
  let references := bindings.map (·.reference)
  let roots ← SourceArm.readRoots artifact bindings
  let rows ← readRows source operands
  let prepared ← SourceTypes.NaturalAffine.witness
    (NominalSector.prepareWithRows artifact order attached required roots rows)
  let subject := prepared.val
  let sourceOwners ← readOwnerReturn [operands.read.selector,operands.read.target]
    (Semantics.SourceOwners.valueOwners operands.body.outcome.value) subject.program
  have fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none)
      order.toList subject.root.receipts := by
    obtain ⟨work,left,ran⟩ := prepared.property
    obtain ⟨_,facts⟩ := (NominalSector.prepareWithRows_bound _ _ _ _ _ _ _ _ _ ran).root
    exact facts.fresh
  let entries ← bindings.mapM (fun bound => readEntry artifact subject.root.receipts bound fresh)
  let arms ← SectorArms.readAll artifact subject.root.dependencies subject.ports.targetIn.basis
    subject.targetLayout.bits subject.targetInCode subject.targetOutCode subject.selectorLayout.labels.length references
  let logical ← NominalSector.checkLogicals subject.targetInCode subject.targetOutCode subject.restriction.sectors
    subject.selectorLayout.labels (arms.map (·.checked.logical))
  return ⟨ports,source,operands,bindings,references,roots,rows,subject,sourceOwners.down,entries,arms,logical⟩

theorem readRows_value {sources owner name offset selector target}
    (table : SourceTypes.QuantumArms.Table sources owner name offset selector target)
    (operands : CanonicalOperands table.site selector target)
    (rows : List (String × String)) (work left : Nat)
    (ok : (readRows table operands).run work = (.ok rows,left)) : rows = sourceRows table operands := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  exact (pure_success _ _ _ _ h).1

theorem sourceRows_only {sources owner name offset selector target}
    (table : SourceTypes.QuantumArms.Table sources owner name offset selector target)
    (operands : CanonicalOperands table.site selector target)
    (row : String × String) (member : row ∈ sourceRows table operands) :
    row = (owner,table.site.original.source) ∨ (∃ arm ∈ table.arms, row ∈ arm.sourceRows) ∨
      row ∈ operands.read.signature.sourceRows := by
  simpa only [sourceRows,sourceRowsWithSignature,List.mem_eraseDups,List.mem_cons,List.mem_append,List.mem_flatMap,or_assoc] using member


structure Postcondition (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (owner name : String) (offset : Nat) (programs : List Programs) (checked : Checked artifact owner name offset) : Prop where
  ports : NominalSector.ports required = some checked.ports
  originalSource : ∃ a b, (SourceTypes.QuantumArms.read artifact.sources owner name offset
    checked.ports.selectorIn.basis checked.ports.targetIn.basis).run a = (.ok checked.source,b)
  operands : ∃ a b, (readOperands checked.source.site checked.ports.selectorIn.basis checked.ports.targetIn.basis).run a =
    (.ok checked.operands,b)
  originalBindings : checked.source.arms.length = programs.length ∧ QleisliKernel.Exact.ListRel
    (fun pair result => result.source = pair.1 ∧ result.programs = pair.2)
    (checked.source.arms.zip programs) checked.bindings
  references : checked.references = checked.bindings.map (·.reference)
  roots : checked.roots = SourceArm.subjectRoots artifact checked.bindings
  rows : checked.rows = sourceRows checked.source checked.operands
  subject : NominalSector.PreparedPostconditionWithRows artifact order attached required checked.roots checked.rows checked.subject
  entries : QleisliKernel.Exact.ListRel (fun bound result => result.bound = bound) checked.bindings checked.entries
  partition : SectorArms.partition checked.subject.selectorLayout.labels.length checked.references = true
  arms : QleisliKernel.Exact.ListRel
    (SectorArms.AtBinding artifact checked.subject.root.dependencies checked.subject.ports.targetIn.basis
      checked.subject.targetLayout.bits checked.subject.targetInCode checked.subject.targetOutCode checked.references)
    (List.range checked.subject.selectorLayout.labels.length) checked.arms
  logical : QleisliKernel.Exact.ListRel
    (NominalSector.LogicalBinding checked.subject.targetInCode checked.subject.targetOutCode checked.subject.restriction.sectors)
    (checked.subject.selectorLayout.labels.zip (checked.arms.map (·.checked.logical))) checked.logical

theorem check_bound (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (owner name : String) (offset : Nat) (programs : List Programs) (checked : Checked artifact owner name offset)
    (work left : Nat) (ok : (check artifact order attached required owner name offset programs).run work = (.ok checked,left)) :
    Postcondition artifact order attached required owner name offset programs checked := by
  obtain ⟨ports,w₁,hp,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨source,w₂,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨operands,operandWork,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨bindings,w₃,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨roots,w₄,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨rows,w₅,hw,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨prepared,w₆,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨sourceOwners,ownerWork,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨entries,w₇,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨arms,w₈,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨logical,w₉,hl,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have portsFound : NominalSector.ports required = some ports := by
    have found := (lift_success _ _ _ _ hp).1
    cases selected : NominalSector.ports required <;> simp_all [readOption]
  obtain ⟨a,b,ran⟩ := prepared.property
  have subject := NominalSector.prepareWithRows_bound _ _ _ _ _ _ _ _ _ ran
  have armFacts := SectorArms.readAll_bound _ _ _ _ _ _ _ _ _ _ _ ha
  have logicalFacts := NominalSector.checkLogicals_bound _ _ _ _ _ _ _ _ hl
  refine ⟨portsFound,⟨w₁,w₂,hs⟩,⟨w₂,operandWork,ho⟩,SourceArm.readAll_bound _ _ _ _ _ _ hb,rfl,
    SourceArm.readRoots_value _ _ _ _ _ hr,readRows_value _ _ _ _ _ hw,subject,?_,
    armFacts.2.1,armFacts.2.2,logicalFacts.2⟩
  exact FiniteRestriction.mapM_relation _ _ (fun bound result before after ok =>
    readEntry_bound _ _ bound _ result before after ok) bindings entries ownerWork w₇ he

/-- The retained complete source return is associated with the original Raw
token flow, rather than inferred from coincident physical wire lists. -/
theorem Checked.originalOwnerReturn {artifact owner name offset}
    (checked : Checked artifact owner name offset) :
    Semantics.RawOwnerFlow.Returns [checked.operands.read.selector,checked.operands.read.target]
      checked.subject.program (Semantics.SourceOwners.valueOwners checked.operands.body.outcome.value) :=
  checked.sourceOwners

end QleisliKernel.Qirf.SourceSector
