import QleisliKernel.Qirf.Carrier
import QleisliKernel.Qirf.Sector
import QleisliKernel.SourceTypes

/-! Informed #64 component study: connect original nominal source declarations,
two logical owner ports and fresh original QIRF/Raw sector reconstruction.
No native/source qmatch mode, arm capability, AST-preservation theorem or
accepted handle is enabled by this component.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.NominalSector
open Semantics.Exact Semantics.CarrierInterface Finite

structure Ports where
  selectorIn : Owner
  targetIn : Owner
  selectorOut : Owner
  targetOut : Owner

def ports (interface : Interface) : Option Ports :=
  match interface.inputs,interface.outputs with
  | [si,ti],[so,to] => some ⟨si,ti,so,to⟩
  | _,_ => none

def forests (attached required : Interface) : List Semantics.FiniteCarrier.Basis :=
  [attached.inputs,attached.outputs,required.inputs,required.outputs].flatMap fun owners =>
    owners.map (·.basis)

private def checkLogicalUsing (inputCode outputCode : Matrix) (physical : List Matrix)
    (plans : FiniteCarrier.CodePlans inputCode outputCode)
    (request : Nat × Matrix) (checkGram : WorkM Unit) : WorkM Matrix := do
  let logical ← SourceTypes.NaturalAffine.witness (matrixRead request.2)
  guard (logical.val.cols == inputCode.cols && logical.val.rows == outputCode.cols) .request
  checkGram
  let sector ← lift (readOption physical[request.1]?)
  let actual ← FiniteCarrier.codeProductUsing .right sector inputCode plans.inputPlan
  let required ← FiniteCarrier.codeProductWithAdmission .left outputCode logical.val plans.outputPlan
    (.checked (by
      obtain ⟨before,after,ran⟩ := logical.property
      exact matrixRead_admitted _ _ before after ran))
  exactWork (Exact.charge actual.entries.length)
  guard (actual == required) .equation
  return logical.val

/-- Exact code-space equation for one active physical selector label. The
physical list comes from complete original-body reconstruction, including
padding labels; these matrices are never supplied as dependency evidence. -/
def checkLogicalWithPlans (inputCode outputCode : Matrix) (physical : List Matrix)
    (plans : FiniteCarrier.CodePlans inputCode outputCode)
    (request : Nat × Matrix) : WorkM Matrix :=
  checkLogicalUsing inputCode outputCode physical plans request
    (FiniteRestriction.adaptiveWholeSpace request.2)

def checkLogical (inputCode outputCode : Matrix) (physical : List Matrix)
    (request : Nat × Matrix) : WorkM Matrix :=
  checkLogicalWithPlans inputCode outputCode physical {} request

/-- A native proof for this exact logical matrix allows the control equation
to reuse its Gram check. The matrix and the code-space equation are checked. -/
def checkLogicalWithGramAndPlans (inputCode outputCode : Matrix) (physical : List Matrix)
    (plans : FiniteCarrier.CodePlans inputCode outputCode)
    (request : Nat × Matrix) (_ : ∃ a b, (wholeSpace request.2).run a = (.ok (),b)) :
    WorkM Matrix :=
  checkLogicalUsing inputCode outputCode physical plans request (pure ())

def checkLogicalWithGram (inputCode outputCode : Matrix) (physical : List Matrix)
    (request : Nat × Matrix) (gram : ∃ a b, (wholeSpace request.2).run a = (.ok (),b)) :
    WorkM Matrix :=
  checkLogicalWithGramAndPlans inputCode outputCode physical {} request gram

def LogicalBinding (inputCode outputCode : Matrix) (physical : List Matrix)
    (request : Nat × Matrix) (logical : Matrix) : Prop :=
  logical = request.2 ∧ logical.cols = inputCode.cols ∧ logical.rows = outputCode.cols ∧
    (∃ before after, (wholeSpace logical).run before = (.ok (),after)) ∧
    ∃ sector actual a b c d,
      physical[request.1]? = some sector ∧
      Exact.Matrix.compose sector inputCode a = (.ok actual,b) ∧
      Exact.Matrix.compose outputCode logical c = (.ok actual,d)

private theorem checkLogicalUsing_bound (inputCode outputCode : Matrix) (physical : List Matrix)
    (plans : FiniteCarrier.CodePlans inputCode outputCode)
    (request : Nat × Matrix) (checkGram : WorkM Unit)
    (gram : ∀ a b, checkGram.run a = (.ok (),b) →
      ∃ c d, (wholeSpace request.2).run c = (.ok (),d))
    (logical : Matrix) (work left : Nat)
    (ok : (checkLogicalUsing inputCode outputCode physical plans request checkGram).run work =
      (.ok logical,left)) :
    LogicalBinding inputCode outputCode physical request logical := by
  obtain ⟨read,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hu,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨sector,w₄,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₅,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨required,w₆,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₈,he,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst logical
  have dims := (guard_success _ _ _ _ hd).1
  simp only [Bool.and_eq_true,beq_iff_eq] at dims
  have sectorEq : physical[request.1]? = some sector := by
    have found := (lift_success _ _ _ _ hs).1
    cases entry : physical[request.1]? <;> simp_all [readOption]
  have exactEq := beq_iff_eq.mp (guard_success _ _ _ _ he).1
  rw [← exactEq] at hr
  obtain ⟨a,b,actualDense⟩ := FiniteCarrier.codeProductUsing_dense _ _ _ _ _ _ _ ha
  obtain ⟨c,d,requiredDense⟩ := FiniteCarrier.codeProductWithAdmission_dense _ _ _ _ _ _ _ _ hr
  obtain ⟨before,after,ran⟩ := read.property
  have sameMatrix := (matrixRead_value _ _ before after ran).1
  exact ⟨sameMatrix,dims.1,dims.2,sameMatrix.symm ▸ gram _ _ hu,
    sector,actual,a,b,c,d,sectorEq,actualDense,requiredDense⟩

theorem checkLogicalWithPlans_bound (inputCode outputCode : Matrix) (physical : List Matrix)
    (plans : FiniteCarrier.CodePlans inputCode outputCode)
    (request : Nat × Matrix) (logical : Matrix) (work left : Nat)
    (ok : (checkLogicalWithPlans inputCode outputCode physical plans request).run work =
      (.ok logical,left)) :
    LogicalBinding inputCode outputCode physical request logical :=
  checkLogicalUsing_bound inputCode outputCode physical plans request _
    (FiniteRestriction.adaptiveWholeSpace_bound request.2) logical work left ok

theorem checkLogical_bound (inputCode outputCode : Matrix) (physical : List Matrix)
    (request : Nat × Matrix) (logical : Matrix) (work left : Nat)
    (ok : (checkLogical inputCode outputCode physical request).run work = (.ok logical,left)) :
    LogicalBinding inputCode outputCode physical request logical :=
  checkLogicalWithPlans_bound inputCode outputCode physical {} request logical work left ok

theorem checkLogicalWithGramAndPlans_bound (inputCode outputCode : Matrix) (physical : List Matrix)
    (plans : FiniteCarrier.CodePlans inputCode outputCode)
    (request : Nat × Matrix) (gram : ∃ a b, (wholeSpace request.2).run a = (.ok (),b))
    (logical : Matrix) (work left : Nat)
    (ok : (checkLogicalWithGramAndPlans inputCode outputCode physical plans request gram).run work =
      (.ok logical,left)) :
    LogicalBinding inputCode outputCode physical request logical :=
  checkLogicalUsing_bound inputCode outputCode physical plans request _ (fun _ _ _ => gram)
    logical work left ok

theorem checkLogicalWithGram_bound (inputCode outputCode : Matrix) (physical : List Matrix)
    (request : Nat × Matrix) (gram : ∃ a b, (wholeSpace request.2).run a = (.ok (),b))
    (logical : Matrix) (work left : Nat)
    (ok : (checkLogicalWithGram inputCode outputCode physical request gram).run work =
      (.ok logical,left)) :
    LogicalBinding inputCode outputCode physical request logical :=
  checkLogicalWithGramAndPlans_bound inputCode outputCode physical {} request gram logical work left ok

private def prepareLogicalCodes (inputCode outputCode : Matrix) (labels : List Nat) :
    WorkM (FiniteCarrier.CodePlans inputCode outputCode) :=
  match labels with
  | _::_::_ => FiniteCarrier.prepareCodes inputCode outputCode
  | _ => pure {}

def checkLogicals (inputCode outputCode : Matrix) (physical : List Matrix)
    (labels : List Nat) (required : List Matrix) : WorkM (List Matrix) := do
  guard (required.length == labels.length) .request
  let plans ← prepareLogicalCodes inputCode outputCode labels
  (labels.zip required).mapM (checkLogicalWithPlans inputCode outputCode physical plans)

theorem checkLogicals_bound (inputCode outputCode : Matrix) (physical : List Matrix)
    (labels : List Nat) (required actual : List Matrix) (work left : Nat)
    (ok : (checkLogicals inputCode outputCode physical labels required).run work = (.ok actual,left)) :
    required.length = labels.length ∧
      QleisliKernel.Exact.ListRel (LogicalBinding inputCode outputCode physical)
        (labels.zip required) actual := by
  obtain ⟨_,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨plans,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ hl).1,
    FiniteRestriction.mapM_relation (checkLogicalWithPlans inputCode outputCode physical plans)
      (LogicalBinding inputCode outputCode physical)
      (checkLogicalWithPlans_bound inputCode outputCode physical plans) (labels.zip required) actual w₂ left h⟩

structure Prepared where
  ports : Ports
  selectorLayout : Semantics.FiniteCarrier.Layout
  targetLayout : Semantics.FiniteCarrier.Layout
  selectorInCode : Matrix
  targetInCode : Matrix
  selectorOutCode : Matrix
  targetOutCode : Matrix
  root : Validity.Root
  program : Semantics.Raw.Program
  restriction : QleisliKernel.Raw.Sector.Retained

structure Checked where
  ports : Ports
  selectorLayout : Semantics.FiniteCarrier.Layout
  targetLayout : Semantics.FiniteCarrier.Layout
  selectorInCode : Matrix
  targetInCode : Matrix
  selectorOutCode : Matrix
  targetOutCode : Matrix
  root : Validity.Root
  program : Semantics.Raw.Program
  restriction : QleisliKernel.Raw.Sector.Retained
  logical : List Matrix

def Checked.subject (checked : Checked) : Prepared :=
  ⟨checked.ports,checked.selectorLayout,checked.targetLayout,checked.selectorInCode,
    checked.targetInCode,checked.selectorOutCode,checked.targetOutCode,checked.root,
    checked.program,checked.restriction⟩

def Prepared.finish (subject : Prepared) (logical : List Matrix) : Checked :=
  ⟨subject.ports,subject.selectorLayout,subject.targetLayout,subject.selectorInCode,
    subject.targetInCode,subject.selectorOutCode,subject.targetOutCode,subject.root,
    subject.program,subject.restriction,logical⟩

def shape (attached required : Interface) : Bool :=
  attached.inputs.length == 2 && attached.outputs.length == 2 &&
    required.inputs.length == 2 && required.outputs.length == 2

def sameTypes (required : Interface) (p : Ports) : Bool :=
  required.publicEffect == .unitary && p.selectorIn.basis == p.selectorOut.basis &&
    p.targetIn.basis == p.targetOut.basis

/-- Fresh typed original subject, reusable by arm checks without another graph pass. -/
def prepareWithRows (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (roots : List Nat) (originalRows : List (String × String)) : WorkM Prepared := do
  guard (shape attached required) .request
  SourceTypes.checkMany artifact.sources (forests attached required)
  let p ← lift (readOption (ports required))
  let si ← Carrier.ownerCode [p.selectorIn]
  let ti ← Carrier.ownerCode [p.targetIn]
  let so ← Carrier.ownerCode [p.selectorOut]
  let to ← Carrier.ownerCode [p.targetOut]
  let sl ← Carrier.readOwner p.selectorIn
  let tl ← Carrier.readOwner p.targetIn
  exactWork (Exact.charge (Carrier.sourceNodes attached required + 1))
  guard (attached == required) .request
  guard (sameTypes required p) .request
  let root ← Carrier.sourceRootWithRows artifact order attached required roots originalRows
  guard (root.program.inputs == attached.inputs.map (·.port) &&
    root.program.outputs == attached.outputs.map (·.port.token)) .request
  exactWork (Exact.charge (attached.outputs.length * root.checked.state.quantum.live.length + 1))
  guard (attached.outputs.all fun owner => root.checked.state.quantum.live.contains owner.port) .request
  exactWork (Exact.charge (root.program.operations.length + 1))
  let program ← lift (readOption (Sector.project root.program))
  let restriction ← QleisliKernel.Raw.Sector.read root.dependencies [.bits sl.bits] [.bits tl.bits] program
  return ⟨p,sl,tl,si,ti,so,to,root,program,restriction⟩

def prepareFromRoots (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (roots : List Nat) : WorkM Prepared :=
  prepareWithRows artifact order attached required roots []

def prepare (artifact : Artifact) (order : Array Nat) (attached required : Interface) : WorkM Prepared :=
  prepareFromRoots artifact order attached required [artifact.root]

def check (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (logical : List Matrix) : WorkM Checked := do
  let subject ← prepare artifact order attached required
  let actual ← checkLogicals subject.targetInCode subject.targetOutCode
    subject.restriction.sectors subject.selectorLayout.labels logical
  return subject.finish actual

structure PreparedPostconditionWithRows (artifact : Artifact) (order : Array Nat)
    (attached required : Interface) (roots : List Nat) (originalRows : List (String × String)) (checked : Prepared) : Prop where
  ownerCounts : shape attached required = true
  sourceTypes : ∃ a b, (SourceTypes.checkMany artifact.sources (forests attached required)).run a = (.ok (),b)
  ports : ports required = some checked.ports
  selectorInCode : ∃ a b, (Carrier.ownerCode [checked.ports.selectorIn]).run a = (.ok checked.selectorInCode,b)
  targetInCode : ∃ a b, (Carrier.ownerCode [checked.ports.targetIn]).run a = (.ok checked.targetInCode,b)
  selectorOutCode : ∃ a b, (Carrier.ownerCode [checked.ports.selectorOut]).run a = (.ok checked.selectorOutCode,b)
  targetOutCode : ∃ a b, (Carrier.ownerCode [checked.ports.targetOut]).run a = (.ok checked.targetOutCode,b)
  selectorLayout : Semantics.FiniteCarrier.layout checked.ports.selectorIn.basis = some checked.selectorLayout
  targetLayout : Semantics.FiniteCarrier.layout checked.ports.targetIn.basis = some checked.targetLayout
  interface : attached = required
  sameTypes : sameTypes required checked.ports = true
  root : ∃ work, Validity.SourceRootPostconditionFromRoots artifact order (Carrier.sourceRows attached required ++ originalRows) roots checked.root work
  inputs : checked.root.program.inputs = attached.inputs.map (·.port)
  outputs : checked.root.program.outputs = attached.outputs.map (·.port.token)
  live : attached.outputs.all (fun owner => checked.root.checked.state.quantum.live.contains owner.port) = true
  exactOriginal : checked.root.program = Semantics.Ownership.pureProgram checked.program
  pureEffect : checked.program.effect = .unitary
  restriction : QleisliKernel.Raw.Sector.ReadBinding checked.root.dependencies
    [.bits checked.selectorLayout.bits] [.bits checked.targetLayout.bits] checked.program checked.restriction


abbrev PreparedPostconditionFromRoots (artifact : Artifact) (order : Array Nat)
    (attached required : Interface) (roots : List Nat) (checked : Prepared) : Prop :=
  PreparedPostconditionWithRows artifact order attached required roots [] checked

abbrev PreparedPostcondition (artifact : Artifact) (order : Array Nat)
    (attached required : Interface) (checked : Prepared) : Prop :=
  PreparedPostconditionFromRoots artifact order attached required [artifact.root] checked

structure Postcondition (artifact : Artifact) (order : Array Nat)
    (attached required : Interface) (logical : List Matrix) (checked : Checked) : Prop
    extends PreparedPostcondition artifact order attached required checked.subject where
  logicalCount : logical.length = checked.selectorLayout.labels.length
  logical : QleisliKernel.Exact.ListRel
    (LogicalBinding checked.targetInCode checked.targetOutCode checked.restriction.sectors)
    (checked.selectorLayout.labels.zip logical) checked.logical

theorem prepareWithRows_bound (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (roots : List Nat) (originalRows : List (String × String)) (checked : Prepared) (work left : Nat)
    (ok : (prepareWithRows artifact order attached required roots originalRows).run work = (.ok checked,left)) :
    PreparedPostconditionWithRows artifact order attached required roots originalRows checked := by
  obtain ⟨_,w₁,hshape,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hsource,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨p,w₃,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨si,w₄,hsi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨ti,w₅,hti,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨so,w₆,hso,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨to,w₇,hto,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨sl,w₈,hsl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨tl,w₉,htl,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₀,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₁,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₂,htypes,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨root,w₁₃,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₄,hports,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₅,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₆,hlive,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₁₇,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨program,w₁₈,hprogram,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨restriction,w₁₉,hrestriction,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have selected : ports required = some p := by
    have found := (lift_success _ _ _ _ hp).1
    cases entry : ports required <;> simp_all [readOption]
  have projected : Sector.project root.program = some program := by
    have found := (lift_success _ _ _ _ hprogram).1
    cases entry : Sector.project root.program <;> simp_all [readOption]
  have rootCheck := Carrier.sourceRootWithRows_result artifact order attached required roots originalRows root w₁₂ w₁₃ hr
  obtain ⟨rootWork,rootCheck⟩ := rootCheck
  have portEq := (guard_success _ _ _ _ hports).1
  simp only [Bool.and_eq_true,beq_iff_eq] at portEq
  have original := Sector.project_bound _ _ projected
  exact ⟨(guard_success _ _ _ _ hshape).1,⟨w₁,w₂,hsource⟩,selected,
    ⟨w₃,w₄,hsi⟩,⟨w₄,w₅,hti⟩,⟨w₅,w₆,hso⟩,⟨w₆,w₇,hto⟩,
    (Carrier.readOwner_conditions _ _ _ _ hsl).1,(Carrier.readOwner_conditions _ _ _ _ htl).1,
    beq_iff_eq.mp (guard_success _ _ _ _ hi).1,(guard_success _ _ _ _ htypes).1,
    ⟨rootWork,Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ rootCheck⟩,
    portEq.1,portEq.2,(guard_success _ _ _ _ hlive).1,original.1,original.2,
    QleisliKernel.Raw.Sector.read_bound _ _ _ _ _ _ _ hrestriction⟩


theorem prepareFromRoots_bound (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (roots : List Nat) (checked : Prepared) (work left : Nat)
    (ok : (prepareFromRoots artifact order attached required roots).run work = (.ok checked,left)) :
    PreparedPostconditionFromRoots artifact order attached required roots checked := by
  exact prepareWithRows_bound artifact order attached required roots [] checked work left ok

theorem prepare_bound (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (checked : Prepared) (work left : Nat)
    (ok : (prepare artifact order attached required).run work = (.ok checked,left)) :
    PreparedPostcondition artifact order attached required checked := by
  exact prepareFromRoots_bound artifact order attached required [artifact.root] checked work left ok

theorem check_bound (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (logical : List Matrix) (checked : Checked) (work left : Nat)
    (ok : (check artifact order attached required logical).run work = (.ok checked,left)) :
    Postcondition artifact order attached required logical checked := by
  obtain ⟨subject,w₁,hsubject,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨actual,w₂,hlogical,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst checked
  have facts := checkLogicals_bound subject.targetInCode subject.targetOutCode
    subject.restriction.sectors subject.selectorLayout.labels logical actual w₁ w₂ hlogical
  exact ⟨prepare_bound artifact order attached required subject work w₁ hsubject,facts.1,facts.2⟩

end QleisliKernel.Qirf.NominalSector
