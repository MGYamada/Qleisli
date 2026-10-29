import QleisliKernel.Qirf.FreshEntries
import QleisliKernel.Qirf.SectorArms
import QleisliKernel.SourceTypes.QuantumArms

/-! Original source-arm association with actual function-evidence entries.
The complete original input and fresh graph receipt remain bound together.
Source-body lowering and native/runtime preservation remain separate duties.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceArm
open Semantics.Exact Semantics.ObservingFunction Finite

structure Programs where
  evidence : Nat
  controlled : Nat
  deriving BEq, DecidableEq, Repr

def canonical {sources owner selector target}
    (arm : SourceTypes.QuantumArms.BoundArm sources owner selector target) : String :=
  arm.operation.resolution.moduleName ++ "::" ++ arm.operation.resolution.declaration.name

structure Binding (artifact : Artifact) {owner selector target}
    (arm : SourceTypes.QuantumArms.BoundArm artifact.sources owner selector target)
    (programs : Programs) where
  entry : Entry
  identity : Semantics.Function.Identity
  original : artifact.entries[programs.evidence]? = some entry
  named : entry.implementationName = canonical arm
  row : (arm.operation.resolution.moduleName,arm.operation.signature.original.source) ∈ identity.sources
  identityRead : ∃ before after, (Qirf.identity artifact entry).run before = (.ok identity,after)

/-- The entry supplies the implementation index. Names and original bytes bind
the source query to that entry; the one fresh graph independently checks its
complete implementation, specification and actual dependency snapshot. -/
def read (artifact : Artifact) {owner selector target}
    (arm : SourceTypes.QuantumArms.BoundArm artifact.sources owner selector target)
    (programs : Programs) : WorkM (Binding artifact arm programs) := do
  guard (artifact.sources.size ≤ 128) .limit
  let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  guard (bytes ≤ 1048576) .limit
  match original : artifact.entries[programs.evidence]? with
  | none => throw .request
  | some entry =>
    guard (entry.implementationName.utf8ByteSize ≤ 4096) .limit
    guard (entry.sources.length ≤ 128) .limit
    exactWork (Exact.charge (8*(bytes+4097)*(entry.sources.length+1)))
    let identity ← SourceTypes.NaturalAffine.witness (Qirf.identity artifact entry)
    if named : entry.implementationName = canonical arm then
      if row : (arm.operation.resolution.moduleName,arm.operation.signature.original.source) ∈ identity.val.sources then
        return ⟨entry,identity.val,original,named,row,by with_reducible exact identity.property⟩
      else throw .request
    else throw .request

structure Bound (artifact : Artifact) (owner : String) (selector target : Semantics.FiniteCarrier.Basis) where
  source : SourceTypes.QuantumArms.BoundArm artifact.sources owner selector target
  programs : Programs
  binding : Binding artifact source programs

def Bound.reference {artifact owner selector target} (bound : Bound artifact owner selector target) : SectorArm.Reference :=
  ⟨bound.source.label.ordinal,target,.unitary,bound.binding.entry.implementation,bound.programs.controlled⟩

def readOne (artifact : Artifact) {owner selector target}
    (pair : SourceTypes.QuantumArms.BoundArm artifact.sources owner selector target × Programs) :
    WorkM (Bound artifact owner selector target) := do
  let binding ← read artifact pair.1 pair.2
  return ⟨pair.1,pair.2,binding⟩

def readAll (artifact : Artifact) {owner selector target}
    (arms : List (SourceTypes.QuantumArms.BoundArm artifact.sources owner selector target))
    (programs : List Programs) : WorkM (List (Bound artifact owner selector target)) := do
  guard (programs.length ≤ 64 && arms.length ≤ 64) .limit
  exactWork (Exact.charge (8*(arms.length+programs.length+1)))
  guard (arms.length == programs.length) .request
  (arms.zip programs).mapM (readOne artifact)

/-- Each evidence subject is an actual QIRF entry node, alongside the original
main, implementation and separately checked controlled implementation. -/
def subjectRoots (artifact : Artifact) {owner selector target}
    (arms : List (Bound artifact owner selector target)) : List Nat :=
  (artifact.root :: arms.flatMap (fun arm => [arm.binding.entry.implementation,
    arm.programs.controlled,artifact.programs.size+arm.programs.evidence])).eraseDups

def readRoots (artifact : Artifact) {owner selector target}
    (arms : List (Bound artifact owner selector target)) : WorkM (List Nat) := do
  guard (arms.length ≤ 64 && artifact.programs.size+artifact.entries.size ≤ 65536) .limit
  exactWork (Exact.charge (16*(3*arms.length+1)^2))
  return subjectRoots artifact arms

structure Realized (artifact : Artifact) (slots : Slots) {owner selector target}
    (bound : Bound artifact owner selector target) where
  receipt : Receipt
  present : slots[bound.programs.evidence]?.join = some receipt
  origin : EntryOrigin artifact bound.programs.evidence receipt

def realize (artifact : Artifact) (slots : Slots) {owner selector target}
    (bound : Bound artifact owner selector target) {nodes : List Nat}
    (fresh : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes slots) :
    WorkM (Realized artifact slots bound) := do
  match present : slots[bound.programs.evidence]?.join with
  | none => throw .request
  | some receipt => return ⟨receipt,present,fresh.originalEntry _ _ present⟩

theorem Realized.originalInput {artifact slots owner selector target}
    {bound : Bound artifact owner selector target} (checked : Realized artifact slots bound) :
    ∃ actual previous a b c d,
      (input artifact bound.binding.entry).run a = (.ok actual,b) ∧
      (Raw.BranchFunction.checkEntry (before previous) actual actual).run c = (.ok checked.receipt,d) ∧
      checked.receipt.input = actual := by
  obtain ⟨entry,actual,previous,a,b,c,d,found,decoded,verified⟩ := checked.origin
  have same : entry = bound.binding.entry := Option.some.inj (found.symm.trans bound.binding.original)
  subst entry
  exact ⟨actual,previous,a,b,c,d,decoded,verified,
    (Raw.BranchFunction.checkEntry_conditions _ _ _ _ _ _ verified).2.1⟩


theorem readOne_bound (artifact : Artifact) {owner selector target}
    (pair : SourceTypes.QuantumArms.BoundArm artifact.sources owner selector target × Programs)
    (bound : Bound artifact owner selector target) (work left : Nat)
    (ok : (readOne artifact pair).run work = (.ok bound,left)) :
    bound.source = pair.1 ∧ bound.programs = pair.2 := by
  obtain ⟨binding,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  have same := (pure_success _ _ _ _ h).1
  subst bound
  exact ⟨rfl,rfl⟩

theorem readAll_bound (artifact : Artifact) {owner selector target}
    (arms : List (SourceTypes.QuantumArms.BoundArm artifact.sources owner selector target))
    (programs : List Programs) (bound : List (Bound artifact owner selector target)) (work left : Nat)
    (ok : (readAll artifact arms programs).run work = (.ok bound,left)) :
    arms.length = programs.length ∧ QleisliKernel.Exact.ListRel
      (fun pair result => result.source = pair.1 ∧ result.programs = pair.2)
      (arms.zip programs) bound := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hcount,h⟩ := bind_success _ _ _ _ _ h
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ hcount).1,
    FiniteRestriction.mapM_relation (readOne artifact)
      (fun pair result => result.source = pair.1 ∧ result.programs = pair.2)
      (readOne_bound artifact) (arms.zip programs) bound w₃ left h⟩

theorem Realized.inputBinding {artifact slots owner selector target}
    {bound : Bound artifact owner selector target} (checked : Realized artifact slots bound) :
    checked.receipt.input.identity = bound.binding.identity ∧
    checked.receipt.input.signature = bound.binding.entry.signature ∧
    artifact.programs[bound.binding.entry.implementation]? = some checked.receipt.input.implementation := by
  obtain ⟨actual,previous,a,b,c,d,decoded,verified,retained⟩ := checked.originalInput
  obtain ⟨signature,implementation,x,y,ident⟩ := input_original _ _ _ _ _ decoded
  obtain ⟨u,v,originalIdentity⟩ := bound.binding.identityRead
  have sameIdentity : actual.identity = bound.binding.identity :=
    (identity_value _ _ _ _ _ ident).trans (identity_value _ _ _ _ _ originalIdentity).symm
  rw [retained]
  exact ⟨sameIdentity,signature,implementation⟩

theorem Realized.sourceRow {artifact slots owner selector target}
    {bound : Bound artifact owner selector target} (checked : Realized artifact slots bound) :
    (bound.source.operation.resolution.moduleName,bound.source.operation.signature.original.source) ∈
      checked.receipt.input.identity.sources := by
  rw [checked.inputBinding.1]
  exact bound.binding.row


theorem subjectRoots_only (artifact : Artifact) {owner selector target}
    (arms : List (Bound artifact owner selector target)) (index : Nat)
    (member : index ∈ subjectRoots artifact arms) :
    index = artifact.root ∨ ∃ arm ∈ arms, index = arm.binding.entry.implementation ∨
      index = arm.programs.controlled ∨ index = artifact.programs.size+arm.programs.evidence := by
  simp only [subjectRoots,List.mem_eraseDups,List.mem_cons,List.mem_flatMap] at member
  rcases member with same | ⟨arm,present,found⟩
  · exact Or.inl same
  · exact Or.inr ⟨arm,present,by simpa using found⟩

theorem readRoots_value (artifact : Artifact) {owner selector target}
    (arms : List (Bound artifact owner selector target)) (roots : List Nat) (work left : Nat)
    (ok : (readRoots artifact arms).run work = (.ok roots,left)) : roots = subjectRoots artifact arms := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  exact (pure_success _ _ _ _ h).1


/-- Changing the resolved source function while retaining an evidence table
and index cannot preserve a successful binding. This holds for all original
source tables and all full target trees, independently of concrete examples. -/
theorem Bound.sameEvidence_name {artifact other owner otherOwner selector target otherSelector otherTarget}
    (first : Bound artifact owner selector target) (second : Bound other otherOwner otherSelector otherTarget)
    (table : artifact.entries = other.entries) (index : first.programs.evidence = second.programs.evidence) :
    canonical first.source = canonical second.source := by
  have found := first.binding.original
  rw [table,index] at found
  have same : first.binding.entry = second.binding.entry :=
    Option.some.inj (found.symm.trans second.binding.original)
  exact first.binding.named.symm.trans ((congrArg Entry.implementationName same).trans second.binding.named)

end QleisliKernel.Qirf.SourceArm
