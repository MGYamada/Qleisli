import QleisliKernel.Qirf.NominalSector

/-! Informed #64/#195 bounded arm study. Actual original implementation and
control programs are reconstructed with the enclosing fresh graph's dependencies.
Logical projection keeps an exact code-space equation; unitarity alone never
supplies the separate controlled implementation. Original source-site/function
binding and native/QDV dispatch remain separate; no handle is issued here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SectorArm
open Semantics.Exact Semantics.Finite Finite

def projectLogical (inputCode outputCode physical : Matrix) : WorkM Matrix := do
  let actual ← exactWork (Exact.Matrix.composeWork physical inputCode)
  let adjoint ← exactWork (Exact.Matrix.adjointWork outputCode)
  let logical ← exactWork (Exact.Matrix.composeWork adjoint actual)
  wholeSpace logical
  let required ← exactWork (Exact.Matrix.composeWork outputCode logical)
  exactWork (Exact.charge actual.entries.length)
  guard (actual == required) .equation
  return logical

structure Projection (inputCode outputCode physical logical : Matrix) : Prop where
  projection : ∃ actual adjoint a b c d e f,
    Exact.Matrix.compose physical inputCode a = (.ok actual,b) ∧
    Exact.Matrix.adjoint outputCode c = (.ok adjoint,d) ∧
    Exact.Matrix.compose adjoint actual e = (.ok logical,f)
  unitary : ∃ a b, (wholeSpace logical).run a = (.ok (),b)
  equation : ∃ actual a b c d,
    Exact.Matrix.compose physical inputCode a = (.ok actual,b) ∧
    Exact.Matrix.compose outputCode logical c = (.ok actual,d)

theorem projectLogical_bound (inputCode outputCode physical logical : Matrix) (work left : Nat)
    (ok : (projectLogical inputCode outputCode physical).run work = (.ok logical,left)) :
    Projection inputCode outputCode physical logical := by
  obtain ⟨actual,w₁,ha,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨adjoint,w₂,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₃,hl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨required,w₅,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,he,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst logical
  have exactEq := beq_iff_eq.mp (guard_success _ _ _ _ he).1
  rw [← exactEq] at hr
  exact ⟨⟨actual,adjoint,work,w₁,w₁,w₂,w₂,w₃,exactWork_success _ _ _ _ ha,
      exactWork_success _ _ _ _ hd,exactWork_success _ _ _ _ hl⟩,
    ⟨w₃,w₄,hu⟩,⟨actual,work,w₁,w₄,w₅,exactWork_success _ _ _ _ ha,
      exactWork_success _ _ _ _ hr⟩⟩

structure Reference where
  label : Nat
  basis : Semantics.FiniteCarrier.Basis
  publicEffect : Semantics.Raw.Effect
  implementation : Nat
  controlled : Nat

structure Checked where
  original : Semantics.Observation.Program
  physical : Matrix
  logical : Matrix
  controlledOriginal : Semantics.Observation.Program
  controlledProgram : Semantics.Raw.Program
  restriction : QleisliKernel.Raw.Sector.Retained
  identity : Matrix
  controlMeanings : List Matrix

/-- Codes are the enclosing freshly checked target owner's codes. Dependency
matrices must come from that same original artifact's fresh root, not a packet.
This helper checks concrete subjects and confers no independent acceptance API. -/
def read (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (reference : Reference) : WorkM Checked := do
  let layout ← FiniteCarrier.read reference.basis
  guard (reference.basis == target && layout.bits == bits && reference.publicEffect == .unitary) .request
  let original ← lift (readOption artifact.programs[reference.implementation]?)
  guard (Raw.BranchFunction.preflight [.bits bits] original) .request
  let physical ← Raw.BranchFunction.reconstruct dependencies original
  wholeSpace physical
  let logical ← projectLogical inputCode outputCode physical
  let controlledOriginal ← lift (readOption artifact.programs[reference.controlled]?)
  exactWork (Exact.charge (controlledOriginal.operations.length + 1))
  let controlledProgram ← lift (readOption (Sector.project controlledOriginal))
  let restriction ← QleisliKernel.Raw.Sector.read dependencies [.bit] [.bits bits] controlledProgram
  exactWork (Exact.charge (logical.rows * logical.rows))
  let identity ← lift (arithmetic (Exact.Matrix.identity logical.rows))
  let controlMeanings ← NominalSector.checkLogicals inputCode outputCode restriction.sectors
    [0,1] [identity,logical]
  return ⟨original,physical,logical,controlledOriginal,controlledProgram,restriction,identity,controlMeanings⟩

structure Postcondition (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (reference : Reference) (checked : Checked) : Prop where
  target : reference.basis = target
  publicEffect : reference.publicEffect = .unitary
  layout : ∃ layout, Semantics.FiniteCarrier.layout reference.basis = some layout ∧ layout.bits = bits
  original : artifact.programs[reference.implementation]? = some checked.original
  preflight : Raw.BranchFunction.preflight [.bits bits] checked.original = true
  reconstruction : ∃ a b, (Raw.BranchFunction.reconstruct dependencies checked.original).run a =
    (.ok checked.physical,b)
  physicalUnitary : ∃ a b, (wholeSpace checked.physical).run a = (.ok (),b)
  logical : Projection inputCode outputCode checked.physical checked.logical
  controlledOriginal : artifact.programs[reference.controlled]? = some checked.controlledOriginal
  exactControl : checked.controlledOriginal = Semantics.Ownership.pureProgram checked.controlledProgram
  controlledEffect : checked.controlledProgram.effect = .unitary
  restriction : QleisliKernel.Raw.Sector.ReadBinding dependencies [.bit] [.bits bits]
    checked.controlledProgram checked.restriction
  identity : Exact.Matrix.identity checked.logical.rows = .ok checked.identity
  controlMeanings : QleisliKernel.Exact.ListRel
    (NominalSector.LogicalBinding inputCode outputCode checked.restriction.sectors)
    ([0,1].zip [checked.identity,checked.logical]) checked.controlMeanings

theorem read_bound (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (reference : Reference) (checked : Checked) (work left : Nat)
    (ok : (read artifact dependencies target bits inputCode outputCode reference).run work = (.ok checked,left)) :
    Postcondition artifact dependencies target bits inputCode outputCode reference checked := by
  obtain ⟨layout,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,ht,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨original,w₃,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨physical,w₅,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨logical,w₇,hlogical,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨control,w₈,hcontrol,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₉,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨program,w₁₀,hproject,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨restriction,w₁₁,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨identity,w₁₃,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨meanings,w₁₄,hmeanings,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have types := (guard_success _ _ _ _ ht).1
  simp only [Bool.and_eq_true,beq_iff_eq] at types
  have originalEq : artifact.programs[reference.implementation]? = some original := by
    have got := (lift_success _ _ _ _ ho).1
    cases found : artifact.programs[reference.implementation]? <;> simp_all [readOption]
  have controlEq : artifact.programs[reference.controlled]? = some control := by
    have got := (lift_success _ _ _ _ hcontrol).1
    cases found : artifact.programs[reference.controlled]? <;> simp_all [readOption]
  have projectEq : Sector.project control = some program := by
    have got := (lift_success _ _ _ _ hproject).1
    cases found : Sector.project control <;> simp_all [readOption]
  have pureControl := Sector.project_bound _ _ projectEq
  have identityEq := arithmetic_success _ _ (lift_success _ _ _ _ hi).1
  exact ⟨types.1.1,types.2,⟨layout,FiniteCarrier.read_reference _ _ _ _ hl,types.1.2⟩,
    originalEq,(guard_success _ _ _ _ hp).1,⟨w₄,w₅,hm⟩,⟨w₅,w₆,hu⟩,
    projectLogical_bound _ _ _ _ _ _ hlogical,controlEq,pureControl.1,pureControl.2,
    QleisliKernel.Raw.Sector.read_bound _ _ _ _ _ _ _ hr,identityEq,
    (NominalSector.checkLogicals_bound _ _ _ _ _ _ _ _ hmeanings).2⟩

end QleisliKernel.Qirf.SectorArm
