import QleisliKernel.Qirf.SectorArm

/-! Informed #64/#195 original-arm collection study. One fresh nominal graph
supplies all dependencies; each original implementation and its separate
controlled implementation supplies exact code-space evidence. Canonical logical
ordinals do not depend on written order. This internal component still lacks
original source-site/operation identity and native/QDV binding; it issues no handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SectorArms
open Semantics.Exact Semantics.Finite Semantics.CarrierInterface Finite

structure BoundArm where
  reference : SectorArm.Reference
  checked : SectorArm.Checked

def readAt (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (references : List SectorArm.Reference) (ordinal : Nat) : WorkM BoundArm := do
  let reference ← lift (readOption (references.find? fun arm => arm.label == ordinal))
  let checked ← SectorArm.read artifact dependencies target bits inputCode outputCode reference
  return ⟨reference,checked⟩

def AtBinding (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (references : List SectorArm.Reference) (ordinal : Nat) (arm : BoundArm) : Prop :=
  arm.reference ∈ references ∧ arm.reference.label = ordinal ∧
    SectorArm.Postcondition artifact dependencies target bits inputCode outputCode arm.reference arm.checked

theorem readAt_bound (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (references : List SectorArm.Reference) (ordinal : Nat) (arm : BoundArm) (work left : Nat)
    (ok : (readAt artifact dependencies target bits inputCode outputCode references ordinal).run work = (.ok arm,left)) :
    AtBinding artifact dependencies target bits inputCode outputCode references ordinal arm := by
  obtain ⟨reference,w₁,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨checked,w₂,hc,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst arm
  have found : references.find? (fun arm => arm.label == ordinal) = some reference := by
    have read := (lift_success _ _ _ _ hf).1
    cases selected : references.find? (fun arm => arm.label == ordinal) <;> simp_all [readOption]
  have label : (reference.label == ordinal) = true :=
    List.find?_some (p := fun arm : SectorArm.Reference => arm.label == ordinal) found
  exact ⟨List.mem_of_find?_eq_some found,beq_iff_eq.mp label,
    SectorArm.read_bound _ _ _ _ _ _ _ _ _ _ hc⟩

def partition (count : Nat) (references : List SectorArm.Reference) : Bool :=
  references.length == count && references.all (fun arm => arm.label < count) &&
    (references.map (·.label)).eraseDups.length == references.length

def readAll (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (count : Nat) (references : List SectorArm.Reference) : WorkM (List BoundArm) := do
  guard (0 < count && count ≤ 64 && references.length ≤ 64) .limit
  exactWork (Exact.charge (16*(references.length+1)^2))
  guard (partition count references) .request
  (List.range count).mapM (readAt artifact dependencies target bits inputCode outputCode references)

theorem readAll_bound (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (count : Nat) (references : List SectorArm.Reference) (arms : List BoundArm) (work left : Nat)
    (ok : (readAll artifact dependencies target bits inputCode outputCode count references).run work = (.ok arms,left)) :
    (0 < count && count ≤ 64 && references.length ≤ 64) = true ∧ partition count references = true ∧
      QleisliKernel.Exact.ListRel
        (AtBinding artifact dependencies target bits inputCode outputCode references)
        (List.range count) arms := by
  obtain ⟨_,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hp,h⟩ := bind_success _ _ _ _ _ h
  exact ⟨(guard_success _ _ _ _ hl).1,(guard_success _ _ _ _ hp).1,
    FiniteRestriction.mapM_relation
      (readAt artifact dependencies target bits inputCode outputCode references)
      (AtBinding artifact dependencies target bits inputCode outputCode references)
      (readAt_bound artifact dependencies target bits inputCode outputCode references)
      (List.range count) arms w₃ left h⟩

/-- Roots are derived only from the actual main and arm/control subjects.
No transport-supplied root list or source-coverage flag can enter this path. -/
def subjectRoots (main : Nat) (references : List SectorArm.Reference) : List Nat :=
  (main :: references.flatMap (fun arm => [arm.implementation,arm.controlled])).eraseDups

def readRoots (main : Nat) (references : List SectorArm.Reference) : WorkM (List Nat) := do
  guard (references.length ≤ 64) .limit
  exactWork (Exact.charge (16*(2*references.length+1)^2))
  return subjectRoots main references

theorem subjectRoots_main (main : Nat) (references : List SectorArm.Reference) :
    main ∈ subjectRoots main references := by
  simp [subjectRoots]

theorem subjectRoots_arm (main : Nat) (references : List SectorArm.Reference)
    (reference : SectorArm.Reference) (member : reference ∈ references) :
    reference.implementation ∈ subjectRoots main references ∧
      reference.controlled ∈ subjectRoots main references := by
  constructor
  all_goals
    simp only [subjectRoots,List.mem_eraseDups]
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨reference,member,by simp⟩

theorem subjectRoots_only (main : Nat) (references : List SectorArm.Reference) (index : Nat)
    (member : index ∈ subjectRoots main references) :
    index = main ∨ ∃ reference ∈ references,
      index = reference.implementation ∨ index = reference.controlled := by
  simp only [subjectRoots,List.mem_eraseDups,List.mem_cons,List.mem_flatMap] at member
  rcases member with same | ⟨reference,present,found⟩
  · exact Or.inl same
  · exact Or.inr ⟨reference,present,by simpa using found⟩

theorem readRoots_value (main : Nat) (references : List SectorArm.Reference)
    (roots : List Nat) (work left : Nat)
    (ok : (readRoots main references).run work = (.ok roots,left)) :
    roots = subjectRoots main references := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  exact (pure_success _ _ _ _ h).1

structure Checked where
  roots : List Nat
  subject : NominalSector.Prepared
  arms : List BoundArm
  logical : List Matrix

/-- Complete original QIRF/Raw checking happens once before arm reconstruction.
No caller-supplied matrix is used for an arm's logical meaning or its controlled
capability. Each active main sector must match that actual original arm exactly. -/
def check (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (references : List SectorArm.Reference) : WorkM Checked := do
  let roots ← readRoots artifact.root references
  let subject ← NominalSector.prepareFromRoots artifact order attached required roots
  let arms ← readAll artifact subject.root.dependencies subject.ports.targetIn.basis
    subject.targetLayout.bits subject.targetInCode subject.targetOutCode subject.selectorLayout.labels.length references
  let logical ← NominalSector.checkLogicals subject.targetInCode subject.targetOutCode subject.restriction.sectors
    subject.selectorLayout.labels (arms.map (·.checked.logical))
  return ⟨roots,subject,arms,logical⟩

structure Postcondition (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (references : List SectorArm.Reference) (checked : Checked) : Prop where
  roots : checked.roots = subjectRoots artifact.root references
  subject : NominalSector.PreparedPostconditionFromRoots artifact order attached required checked.roots checked.subject
  partition : partition checked.subject.selectorLayout.labels.length references = true
  arms : QleisliKernel.Exact.ListRel
    (AtBinding artifact checked.subject.root.dependencies checked.subject.ports.targetIn.basis
      checked.subject.targetLayout.bits checked.subject.targetInCode checked.subject.targetOutCode references)
    (List.range checked.subject.selectorLayout.labels.length) checked.arms
  count : checked.arms.length = checked.subject.selectorLayout.labels.length
  logical : QleisliKernel.Exact.ListRel
    (NominalSector.LogicalBinding checked.subject.targetInCode checked.subject.targetOutCode checked.subject.restriction.sectors)
    (checked.subject.selectorLayout.labels.zip (checked.arms.map (·.checked.logical))) checked.logical

theorem check_bound (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (references : List SectorArm.Reference) (checked : Checked) (work left : Nat)
    (ok : (check artifact order attached required references).run work = (.ok checked,left)) :
    Postcondition artifact order attached required references checked := by
  obtain ⟨roots,rootWork,hroots,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨subject,w₁,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨arms,w₂,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨logical,w₃,hl,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have armFacts := readAll_bound artifact subject.root.dependencies subject.ports.targetIn.basis
    subject.targetLayout.bits subject.targetInCode subject.targetOutCode subject.selectorLayout.labels.length
    references arms w₁ w₂ ha
  have logicalFacts := NominalSector.checkLogicals_bound subject.targetInCode subject.targetOutCode
    subject.restriction.sectors subject.selectorLayout.labels (arms.map (·.checked.logical)) logical w₂ w₃ hl
  exact ⟨readRoots_value _ _ _ _ _ hroots,
    NominalSector.prepareFromRoots_bound artifact order attached required roots subject rootWork w₁ hs,
    armFacts.2.1,armFacts.2.2,
    by simpa only [List.length_map] using logicalFacts.1,logicalFacts.2⟩

end QleisliKernel.Qirf.SectorArms
