import QleisliKernel.Qirf.NominalSector
import QleisliKernel.Qirf.SectorForward

/-! Informed #64/#195 bounded arm study. Actual original implementation and
control programs are reconstructed with the enclosing fresh graph's dependencies.
Logical projection keeps an exact code-space equation; unitarity alone never
supplies the separate controlled implementation. Original source-site/function
binding and native/QDV dispatch remain separate; no handle is issued here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SectorArm
open Semantics.Exact Semantics.Finite Finite

structure AdjointCode (outputCode : Matrix) where
  matrix : Matrix
  computed : ∃ before after, Exact.Matrix.adjoint outputCode before = (.ok matrix,after)
  plan : Option (FiniteCarrier.CodePlan matrix) := none

private def readAdjoint (outputCode : Matrix) : WorkM (AdjointCode outputCode) := do
  let result ← SourceTypes.NaturalAffine.witness (exactWork (Exact.Matrix.adjointWork outputCode))
  return ⟨result.val,by
    obtain ⟨before,after,ran⟩ := result.property
    exact ⟨before,after,exactWork_success _ _ _ _ ran⟩,none⟩

structure Codes (inputCode outputCode : Matrix) where
  products : FiniteCarrier.CodePlans inputCode outputCode := {}
  adjoint : Option (AdjointCode outputCode) := none

/-- Prepare the literal target codes once for the arms of this selection.
The cached adjoint has the same original bounded arithmetic witness. -/
def prepareCodes (inputCode outputCode : Matrix) : WorkM (Codes inputCode outputCode) := do
  let products ← FiniteCarrier.prepareCodes inputCode outputCode
  let adjoint ← readAdjoint outputCode
  let plan ← FiniteCarrier.prepareCode adjoint.matrix
  return ⟨products,some { adjoint with plan := some plan }⟩

private def useAdjoint (outputCode : Matrix) : Option (AdjointCode outputCode) →
    WorkM (AdjointCode outputCode)
  | none => readAdjoint outputCode
  | some adjoint => pure adjoint

private def projectLogicalUsing (inputCode outputCode physical : Matrix)
    (codes : Codes inputCode outputCode) : WorkM Matrix := do
  let actual ← SourceTypes.NaturalAffine.witness
    (FiniteCarrier.codeProductUsing .right physical inputCode codes.products.inputPlan)
  let adjoint ← useAdjoint outputCode codes.adjoint
  let logical ← SourceTypes.NaturalAffine.witness
    (FiniteCarrier.codeProductWithAdmission .left adjoint.matrix actual.val adjoint.plan
      (.checked (FiniteCarrier.codeProduct_admitted _ _ _ _ _ .fresh actual.property)))
  FiniteRestriction.adaptiveWholeSpace logical.val
  let required ← FiniteCarrier.codeProductWithAdmission .left outputCode logical.val codes.products.outputPlan
    (.checked (FiniteCarrier.codeProduct_admitted _ _ _ _ _ _ logical.property))
  exactWork (Exact.charge actual.val.entries.length)
  guard (actual.val == required) .equation
  return logical.val

def projectLogical (inputCode outputCode physical : Matrix) : WorkM Matrix :=
  projectLogicalUsing inputCode outputCode physical {}

structure Projection (inputCode outputCode physical logical : Matrix) : Prop where
  projection : ∃ actual adjoint a b c d e f,
    Exact.Matrix.compose physical inputCode a = (.ok actual,b) ∧
    Exact.Matrix.adjoint outputCode c = (.ok adjoint,d) ∧
    Exact.Matrix.compose adjoint actual e = (.ok logical,f)
  unitary : ∃ a b, (wholeSpace logical).run a = (.ok (),b)
  equation : ∃ actual a b c d,
    Exact.Matrix.compose physical inputCode a = (.ok actual,b) ∧
    Exact.Matrix.compose outputCode logical c = (.ok actual,d)

private theorem projectLogicalUsing_bound (inputCode outputCode physical logical : Matrix)
    (codes : Codes inputCode outputCode) (work left : Nat)
    (ok : (projectLogicalUsing inputCode outputCode physical codes).run work = (.ok logical,left)) :
    Projection inputCode outputCode physical logical := by
  obtain ⟨actual,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨adjoint,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨required,w₅,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,he,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst logical
  have exactEq := beq_iff_eq.mp (guard_success _ _ _ _ he).1
  rw [← exactEq] at hr
  obtain ⟨before,after,actualRead⟩ := actual.property
  obtain ⟨a,b,actualDense⟩ := FiniteCarrier.codeProductUsing_dense _ _ _ _ _ before after actualRead
  obtain ⟨c,d,adjointDense⟩ := adjoint.computed
  obtain ⟨before,after,logicalRead⟩ := result.property
  obtain ⟨e,f,logicalDense⟩ := FiniteCarrier.codeProductWithAdmission_dense _ _ _ _ _ _ before after logicalRead
  obtain ⟨g,i,requiredDense⟩ := FiniteCarrier.codeProductWithAdmission_dense _ _ _ _ _ _ w₄ w₅ hr
  exact ⟨⟨actual.val,adjoint.matrix,a,b,c,d,e,f,actualDense,adjointDense,logicalDense⟩,
    FiniteRestriction.adaptiveWholeSpace_bound _ _ _ hu,
    ⟨actual.val,a,b,g,i,actualDense,requiredDense⟩⟩

theorem projectLogical_bound (inputCode outputCode physical logical : Matrix) (work left : Nat)
    (ok : (projectLogical inputCode outputCode physical).run work = (.ok logical,left)) :
    Projection inputCode outputCode physical logical :=
  projectLogicalUsing_bound inputCode outputCode physical logical {} work left ok

private theorem witnessedProjection (inputCode outputCode physical : Matrix)
    (codes : Codes inputCode outputCode)
    (result : {value : Matrix // ∃ work left,
      (projectLogicalUsing inputCode outputCode physical codes).run work = (.ok value,left)}) :
    Projection inputCode outputCode physical result.val := by
  obtain ⟨work,left,checked⟩ := result.property
  exact projectLogicalUsing_bound inputCode outputCode physical result.val codes work left checked

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
def readUsing (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (codes : Codes inputCode outputCode)
    (reference : Reference) : WorkM Checked := do
  let layout ← FiniteCarrier.read reference.basis
  guard (reference.basis == target && layout.bits == bits && reference.publicEffect == .unitary) .request
  let original ← lift (readOption artifact.programs[reference.implementation]?)
  guard (Raw.BranchFunction.preflight [.bits bits] original) .request
  let physical ← SectorForward.read dependencies bits original
  FiniteRestriction.adaptiveWholeSpace physical
  let projection ← SourceTypes.NaturalAffine.witness (projectLogicalUsing inputCode outputCode physical codes)
  let logical := projection.val
  let controlledOriginal ← lift (readOption artifact.programs[reference.controlled]?)
  exactWork (Exact.charge (controlledOriginal.operations.length + 1))
  let controlledProgram ← lift (readOption (Sector.project controlledOriginal))
  let restriction ← QleisliKernel.Raw.Sector.read dependencies [.bit] [.bits bits] controlledProgram
  exactWork (Exact.charge (logical.rows * logical.rows))
  let identity ← lift (arithmetic (Exact.Matrix.identity logical.rows))
  let inactive ← NominalSector.checkLogicalWithPlans inputCode outputCode restriction.sectors codes.products
    (0,identity)
  let active ← NominalSector.checkLogicalWithGramAndPlans inputCode outputCode restriction.sectors codes.products
    (1,logical) (witnessedProjection inputCode outputCode physical codes projection).unitary
  return ⟨original,physical,logical,controlledOriginal,controlledProgram,restriction,identity,[inactive,active]⟩

def read (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (reference : Reference) : WorkM Checked :=
  readUsing artifact dependencies target bits inputCode outputCode {} reference

structure Postcondition (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (reference : Reference) (checked : Checked) : Prop where
  target : reference.basis = target
  publicEffect : reference.publicEffect = .unitary
  layout : ∃ layout, Semantics.FiniteCarrier.layout reference.basis = some layout ∧ layout.bits = bits
  original : artifact.programs[reference.implementation]? = some checked.original
  preflight : Raw.BranchFunction.preflight [.bits bits] checked.original = true
  reconstruction : SectorForward.Binding dependencies bits checked.original checked.physical
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

theorem readUsing_bound (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (codes : Codes inputCode outputCode)
    (reference : Reference) (checked : Checked) (work left : Nat)
    (ok : (readUsing artifact dependencies target bits inputCode outputCode codes reference).run work =
      (.ok checked,left)) :
    Postcondition artifact dependencies target bits inputCode outputCode reference checked := by
  obtain ⟨layout,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,ht,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨original,w₃,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨physical,w₅,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨projection,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨control,w₈,hcontrol,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₉,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨program,w₁₀,hproject,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨restriction,w₁₁,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨identity,w₁₃,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨inactive,w₁₄,hinactive,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨active,w₁₅,hactive,h⟩ := bind_success _ _ _ _ _ h
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
    originalEq,(guard_success _ _ _ _ hp).1,SectorForward.read_bound _ _ _ _ _ _ hm,
    FiniteRestriction.adaptiveWholeSpace_bound _ _ _ hu,
    witnessedProjection _ _ _ codes projection,controlEq,pureControl.1,pureControl.2,
    QleisliKernel.Raw.Sector.read_bound _ _ _ _ _ _ _ hr,identityEq,
    ⟨NominalSector.checkLogicalWithPlans_bound _ _ _ _ _ inactive _ _ hinactive,
      NominalSector.checkLogicalWithGramAndPlans_bound _ _ _ _ _ _ active _ _ hactive,trivial⟩⟩

theorem read_bound (artifact : Artifact) (dependencies : List Dependency)
    (target : Semantics.FiniteCarrier.Basis) (bits : Nat) (inputCode outputCode : Matrix)
    (reference : Reference) (checked : Checked) (work left : Nat)
    (ok : (read artifact dependencies target bits inputCode outputCode reference).run work = (.ok checked,left)) :
    Postcondition artifact dependencies target bits inputCode outputCode reference checked :=
  readUsing_bound artifact dependencies target bits inputCode outputCode {} reference checked work left ok

end QleisliKernel.Qirf.SectorArm
