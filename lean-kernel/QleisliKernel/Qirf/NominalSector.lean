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

/-- Exact code-space equation for one active physical selector label. The
physical list comes from complete original-body reconstruction, including
padding labels; these matrices are never supplied as dependency evidence. -/
def checkLogical (inputCode outputCode : Matrix) (physical : List Matrix)
    (request : Nat × Matrix) : WorkM Matrix := do
  let logical ← matrixRead request.2
  guard (logical.cols == inputCode.cols && logical.rows == outputCode.cols) .request
  wholeSpace logical
  let sector ← lift (readOption physical[request.1]?)
  let actual ← exactWork (Exact.Matrix.composeWork sector inputCode)
  let required ← exactWork (Exact.Matrix.composeWork outputCode logical)
  exactWork (Exact.charge actual.entries.length)
  guard (actual == required) .equation
  return logical

def LogicalBinding (inputCode outputCode : Matrix) (physical : List Matrix)
    (request : Nat × Matrix) (logical : Matrix) : Prop :=
  logical = request.2 ∧ logical.cols = inputCode.cols ∧ logical.rows = outputCode.cols ∧
    (∃ before after, (wholeSpace logical).run before = (.ok (),after)) ∧
    ∃ sector actual a b c d,
      physical[request.1]? = some sector ∧
      Exact.Matrix.compose sector inputCode a = (.ok actual,b) ∧
      Exact.Matrix.compose outputCode logical c = (.ok actual,d)

theorem checkLogical_bound (inputCode outputCode : Matrix) (physical : List Matrix)
    (request : Nat × Matrix) (logical : Matrix) (work left : Nat)
    (ok : (checkLogical inputCode outputCode physical request).run work = (.ok logical,left)) :
    LogicalBinding inputCode outputCode physical request logical := by
  obtain ⟨read,w₁,hm,h⟩ := bind_success _ _ _ _ _ ok
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
  exact ⟨(matrixRead_value _ _ _ _ hm).1,dims.1,dims.2,⟨w₂,w₃,hu⟩,
    sector,actual,w₄,w₅,w₅,w₆,sectorEq,exactWork_success _ _ _ _ ha,
    exactWork_success _ _ _ _ hr⟩

def checkLogicals (inputCode outputCode : Matrix) (physical : List Matrix)
    (labels : List Nat) (required : List Matrix) : WorkM (List Matrix) := do
  guard (required.length == labels.length) .request
  (labels.zip required).mapM (checkLogical inputCode outputCode physical)

theorem checkLogicals_bound (inputCode outputCode : Matrix) (physical : List Matrix)
    (labels : List Nat) (required actual : List Matrix) (work left : Nat)
    (ok : (checkLogicals inputCode outputCode physical labels required).run work = (.ok actual,left)) :
    required.length = labels.length ∧
      QleisliKernel.Exact.ListRel (LogicalBinding inputCode outputCode physical)
        (labels.zip required) actual := by
  obtain ⟨_,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ hl).1,
    FiniteRestriction.mapM_relation (checkLogical inputCode outputCode physical)
      (LogicalBinding inputCode outputCode physical)
      (checkLogical_bound inputCode outputCode physical) (labels.zip required) actual w₁ left h⟩

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
def prepareFromRoots (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (roots : List Nat) : WorkM Prepared := do
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
  let root ← Carrier.sourceRootFromRoots artifact order attached required roots
  guard (root.program.inputs == attached.inputs.map (·.port) &&
    root.program.outputs == attached.outputs.map (·.port.token)) .request
  exactWork (Exact.charge (attached.outputs.length * root.checked.state.quantum.live.length + 1))
  guard (attached.outputs.all fun owner => root.checked.state.quantum.live.contains owner.port) .request
  exactWork (Exact.charge (root.program.operations.length + 1))
  let program ← lift (readOption (Sector.project root.program))
  let restriction ← QleisliKernel.Raw.Sector.read root.dependencies [.bits sl.bits] [.bits tl.bits] program
  return ⟨p,sl,tl,si,ti,so,to,root,program,restriction⟩

def prepare (artifact : Artifact) (order : Array Nat) (attached required : Interface) : WorkM Prepared :=
  prepareFromRoots artifact order attached required [artifact.root]

def check (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (logical : List Matrix) : WorkM Checked := do
  let subject ← prepare artifact order attached required
  let actual ← checkLogicals subject.targetInCode subject.targetOutCode
    subject.restriction.sectors subject.selectorLayout.labels logical
  return subject.finish actual

structure PreparedPostconditionFromRoots (artifact : Artifact) (order : Array Nat)
    (attached required : Interface) (roots : List Nat) (checked : Prepared) : Prop where
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
  root : ∃ work, Validity.SourceRootPostconditionFromRoots artifact order (Carrier.sourceRows attached required) roots checked.root work
  inputs : checked.root.program.inputs = attached.inputs.map (·.port)
  outputs : checked.root.program.outputs = attached.outputs.map (·.port.token)
  live : attached.outputs.all (fun owner => checked.root.checked.state.quantum.live.contains owner.port) = true
  exactOriginal : checked.root.program = Semantics.Ownership.pureProgram checked.program
  pureEffect : checked.program.effect = .unitary
  restriction : QleisliKernel.Raw.Sector.ReadBinding checked.root.dependencies
    [.bits checked.selectorLayout.bits] [.bits checked.targetLayout.bits] checked.program checked.restriction


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

theorem prepareFromRoots_bound (artifact : Artifact) (order : Array Nat) (attached required : Interface)
    (roots : List Nat) (checked : Prepared) (work left : Nat)
    (ok : (prepareFromRoots artifact order attached required roots).run work = (.ok checked,left)) :
    PreparedPostconditionFromRoots artifact order attached required roots checked := by
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
  have rootCheck := Carrier.sourceRootFromRoots_result artifact order attached required roots root w₁₂ w₁₃ hr
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
