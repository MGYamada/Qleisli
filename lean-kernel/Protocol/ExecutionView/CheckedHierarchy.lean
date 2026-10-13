import Protocol.ExecutionView.Gate
import Protocol.ExecutionView.Hierarchy

/-! Pure hierarchy inspection gate over one fresh structural result and its
exact finite leaves. Production modes and the protocol cutover remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.CheckedHierarchy
open Gate
abbrev Error := Gate.Error

structure Checked where
  artifact : Hierarchical.Artifact.Artifact
  order : Array Nat
  structural : Hierarchical.Conditional.Pending
  matrices : HierarchyView.Matrices

private def structureCheck (artifact : Hierarchical.Artifact.Artifact) (order : Array Nat) :
    Except Error Hierarchical.Conditional.Pending :=
  (Hierarchical.Conditional.checkAll artifact order).mapError
    (fun error => .hierarchy error.kind error.atNode)

/-- No intermediate checked record is supplied by the host. The exact leaves
returned here are the ones whose original bodies were checked in this call. -/
def checkInspect (bytes supplied : ByteArray) : CheckM Checked := do
  guard (framed supplied) .invalidView
  let (artifact,order) ← lift ((Protocol.Hierarchical.parse bytes).mapError fun _ => .packet)
  let structural ← lift (structureCheck artifact order)
  let matrices ← native (HierarchyView.reconstructLeaves structural.state.requests)
  let description ← native (HierarchyView.purePlan artifact matrices)
  let expected ← lift ((encode description).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return ⟨artifact,order,structural,matrices⟩

structure Binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat) where
  afterLeaves : Nat
  description : Value
  framedView : framed supplied = true
  packetBound : Protocol.Hierarchical.parse bytes = .ok (checked.artifact,checked.order)
  structuralBound : Hierarchical.Conditional.checkAll checked.artifact checked.order = .ok checked.structural
  leavesBound : (HierarchyView.reconstructLeaves checked.structural.state.requests).run work =
    (.ok checked.matrices,afterLeaves)
  viewBound : (HierarchyView.purePlan checked.artifact checked.matrices).run afterLeaves = (.ok description,left)
  compared : encode description = .ok supplied

theorem checkInspect_binding (bytes supplied : ByteArray) (checked : Checked) (work left : Nat)
    (ok : (checkInspect bytes supplied).run work = (.ok checked,left)) :
    Nonempty (Binding bytes supplied checked work left) := by
  unfold checkInspect at ok
  obtain ⟨_,w₀,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨input,w₁,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨structural,w₂,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨matrices,w₃,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨description,w₄,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,w₅,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₆,hs,h⟩ := bind_success _ _ _ _ _ h
  cases h
  have frame := guard_success _ _ _ _ hf
  have packet := lift_success _ _ _ _ hp
  have core := lift_success _ _ _ _ hc
  have encoded := lift_success _ _ _ _ he
  have same := guard_success _ _ _ _ hs
  have bound : Protocol.Hierarchical.parse bytes = .ok input := by
    cases h : Protocol.Hierarchical.parse bytes <;> simp_all [Except.mapError]
  have checkedCore : Hierarchical.Conditional.checkAll input.1 input.2 = .ok structural := by
    cases h : Hierarchical.Conditional.checkAll input.1 input.2 <;>
      simp_all [structureCheck,Except.mapError]
  have equalData : supplied.data = expected.data := beq_iff_eq.mp same.1
  have equal : supplied = expected := by
    cases supplied; cases expected; cases equalData; rfl
  have encoding : encode description = .ok supplied := by
    cases h : encode description <;> simp_all [Except.mapError]
  have start := frame.2
  have packetWork := packet.2
  have coreWork := core.2
  have encodingWork := encoded.2
  have compareWork := same.2
  subst w₀; subst w₁; subst w₂; subst w₅; subst left
  exact ⟨⟨w₃,description,frame.1,bound,checkedCore,
    native_success _ _ _ _ hm,native_success _ _ _ _ hv,encoding⟩⟩

end QleisliKernel.Protocol.ExecutionView.CheckedHierarchy

namespace QleisliKernel.Protocol.ExecutionView.CheckedHierarchy.Modes
open Gate
open QleisliKernel.Hierarchical

inductive Mode where
  | inspect | request | fourier | instrument | qpeInstrument
  deriving BEq, DecidableEq, Repr

/-- Each variant retains the original decoded packet and its fresh complete
structural result. No serialized receipt or host success flag is an input. -/
inductive Core where
  | inspect (artifact : Artifact.Artifact) (order : Array Nat) (checked : Conditional.Pending)
  | request (packet : Protocol.Hierarchical.RootPacket) (checked : Root.Checked)
  | fourier (packet : Protocol.Hierarchical.FourierPacket) (checked : FourierRoot.Checked)
  | instrument (packet : Protocol.Hierarchical.InstrumentPacket) (checked : Instrument.Pending)
  | qpeInstrument (packet : Protocol.Hierarchical.QpeInstrumentPacket) (checked : QpeInstrument.Pending)

def Core.requests : Core → Array Hierarchical.Finite.Request
  | .inspect _ _ c => c.state.requests
  | .request _ c | .fourier _ c => c.artifact.state.requests
  | .instrument _ c => c.circuit.artifact.state.requests
  | .qpeInstrument _ c => c.circuit.artifact.state.requests

def Core.visits : Core → Nat
  | .inspect _ _ c => c.state.visits
  | .request _ c | .fourier _ c => c.artifact.state.visits + c.binding.visits
  | .instrument _ c => c.visits
  | .qpeInstrument _ c => c.visits

def Core.pairs : Core → List Nat
  | .request _ c => c.binding.requests
  | .instrument _ c => c.circuit.binding.requests
  | .qpeInstrument _ c => c.circuit.provider.requests
  | _ => []

def Core.hadamards : Core → List Nat
  | .fourier _ c => c.binding.body.requests.map Hadamard.Request.leafIndex
  | .qpeInstrument p c =>
    ((p.packet.circuit.candidate.hadamards.toList.map (·.index)) ++
      c.circuit.schedule.inverse.fourier.body.requests.map (·.leafIndex)).eraseDups
  | _ => []

private def parsed {α : Type} (result : Except Protocol.Error α) : Except Gate.Error α :=
  result.mapError (fun error => match error with | .syntax => .packet | .limit => .native .limit)

private def structural {α : Type} (result : Except Artifact.Failure α) : Except Gate.Error α :=
  result.mapError (fun error => .hierarchy error.kind error.atNode)

/-- All modes use the existing whole-artifact checker exactly once. -/
def checkCore (mode : Mode) (bytes : ByteArray) : Except Gate.Error Core := do
  match mode with
  | .inspect =>
    let (artifact,order) ← parsed (Protocol.Hierarchical.parse bytes)
    let checked ← structural (Conditional.checkAll artifact order)
    return .inspect artifact order checked
  | .request =>
    let p ← parsed (Protocol.Hierarchical.parseRequest bytes)
    let checked ← structural (Root.checkAll p.artifact p.order p.request p.pairs p.pairOrder)
    return .request p checked
  | .fourier =>
    let p ← parsed (Protocol.Hierarchical.parseFourier bytes)
    let checked ← structural (FourierRoot.checkAll p.artifact p.order p.request p.wiringOrder)
    return .fourier p checked
  | .instrument =>
    let p ← parsed (Protocol.Hierarchical.parseInstrument bytes)
    let checked ← structural (Instrument.checkAll p.request p.packet)
    return .instrument p checked
  | .qpeInstrument =>
    let p ← parsed (Protocol.Hierarchical.parseQpeInstrument bytes)
    let checked ← structural (QpeInstrument.checkAll p.request p.packet)
    return .qpeInstrument p checked

/-- Independent pair and phase-fixed H checks keep their original obligations.
They share the same remaining budget as the actual-leaf reconstruction. -/
def Core.extra : Core → Finite.WorkM Unit
  | .request p c => HierarchicalFinite.checkPairs p.artifact p.request p.pairs c.binding.requests
  | .fourier p c => HierarchicalFinite.checkHadamards p.artifact
      (c.binding.body.requests.map Hadamard.Request.leafIndex)
  | .instrument p c => HierarchicalFinite.checkPairs p.packet.artifact
      p.request.circuit p.packet.pairs c.circuit.binding.requests
  | .qpeInstrument p c => do
    HierarchicalFinite.checkPairs p.packet.circuit.artifact
      p.request.circuit.provider p.packet.circuit.pairs c.circuit.provider.requests
    HierarchicalFinite.checkHadamards p.packet.circuit.artifact (Core.qpeInstrument p c).hadamards
  | .inspect _ _ _ => pure ()

/-- Read actual original coordinates, never the independent requested meaning.
QPE restores the original circuit root rather than executing its provider. -/
def Core.plan (core : Core) (matrices : HierarchyView.Matrices) : Finite.WorkM Value :=
  match core with
  | .inspect artifact _ _ => HierarchyView.purePlan artifact matrices
  | .request p _ => HierarchyView.purePlan p.artifact matrices
  | .fourier p _ => HierarchyView.purePlan p.artifact matrices
  | .instrument p _ => HierarchyView.instrumentPlan p.packet matrices
  | .qpeInstrument p _ => HierarchyView.instrumentPlan
      ⟨p.packet.preparation,p.packet.circuit.artifact,p.packet.circuit.order,
        p.packet.circuit.pairs,p.packet.circuit.pairOrder,p.packet.readout⟩ matrices

/-- Binding to the original mode, complete packet and actual structural call. -/
def CoreBound (mode : Mode) (bytes : ByteArray) : Core → Prop
  | .inspect a o c => mode = .inspect ∧ Protocol.Hierarchical.parse bytes = .ok (a,o) ∧
      Conditional.checkAll a o = .ok c
  | .request p c => mode = .request ∧ Protocol.Hierarchical.parseRequest bytes = .ok p ∧
      Root.checkAll p.artifact p.order p.request p.pairs p.pairOrder = .ok c
  | .fourier p c => mode = .fourier ∧ Protocol.Hierarchical.parseFourier bytes = .ok p ∧
      FourierRoot.checkAll p.artifact p.order p.request p.wiringOrder = .ok c
  | .instrument p c => mode = .instrument ∧ Protocol.Hierarchical.parseInstrument bytes = .ok p ∧
      Instrument.checkAll p.request p.packet = .ok c
  | .qpeInstrument p c => mode = .qpeInstrument ∧ Protocol.Hierarchical.parseQpeInstrument bytes = .ok p ∧
      QpeInstrument.checkAll p.request p.packet = .ok c

private theorem step_bound {α β γ : Type} (input : Except Protocol.Error α)
    (next : α → Except Artifact.Failure β) (finish : α → β → γ) (result : γ)
    (ok : (do let a ← parsed input; let b ← structural (next a); pure (finish a b)) = .ok result) :
    ∃ a b, input = .ok a ∧ next a = .ok b ∧ finish a b = result := by
  cases input with
  | error e =>
    change Except.error (match e with | .syntax => Gate.Error.packet | .limit => Gate.Error.native .limit) = .ok result at ok
    cases ok
  | ok a =>
    change (do let b ← structural (next a); pure (finish a b)) = .ok result at ok
    cases hc : next a with
    | error e =>
      rw [hc] at ok
      change Except.error (Gate.Error.hierarchy e.kind e.atNode) = .ok result at ok
      cases ok
    | ok b =>
      rw [hc] at ok
      change Except.ok (finish a b) = .ok result at ok
      exact ⟨a,b,rfl,hc,Except.ok.inj ok⟩

theorem checkCore_bound (mode : Mode) (bytes : ByteArray) (core : Core)
    (ok : checkCore mode bytes = .ok core) : CoreBound mode bytes core := by
  cases mode with
  | inspect =>
    obtain ⟨p,c,hp,hc,rfl⟩ := step_bound (Protocol.Hierarchical.parse bytes)
      (fun p => Conditional.checkAll p.1 p.2) (fun p c => Core.inspect p.1 p.2 c) core ok
    exact ⟨rfl,hp,hc⟩
  | request =>
    obtain ⟨p,c,hp,hc,rfl⟩ := step_bound (Protocol.Hierarchical.parseRequest bytes)
      (fun p => Root.checkAll p.artifact p.order p.request p.pairs p.pairOrder) Core.request core ok
    exact ⟨rfl,hp,hc⟩
  | fourier =>
    obtain ⟨p,c,hp,hc,rfl⟩ := step_bound (Protocol.Hierarchical.parseFourier bytes)
      (fun p => FourierRoot.checkAll p.artifact p.order p.request p.wiringOrder) Core.fourier core ok
    exact ⟨rfl,hp,hc⟩
  | instrument =>
    obtain ⟨p,c,hp,hc,rfl⟩ := step_bound (Protocol.Hierarchical.parseInstrument bytes)
      (fun p => Instrument.checkAll p.request p.packet) Core.instrument core ok
    exact ⟨rfl,hp,hc⟩
  | qpeInstrument =>
    obtain ⟨p,c,hp,hc,rfl⟩ := step_bound (Protocol.Hierarchical.parseQpeInstrument bytes)
      (fun p => QpeInstrument.checkAll p.request p.packet) Core.qpeInstrument core ok
    exact ⟨rfl,hp,hc⟩

structure Inspected where
  core : Core
  matrices : HierarchyView.Matrices

/-- Inspection remains available independently of execution capability. -/
def inspectMode (mode : Mode) (bytes : ByteArray) : CheckM Inspected := do
  let core ← lift (checkCore mode bytes)
  let matrices ← native (HierarchyView.reconstructLeaves core.requests)
  native core.extra
  return ⟨core,matrices⟩

structure InspectionBinding (mode : Mode) (bytes : ByteArray) (checked : Inspected) (work left : Nat) where
  afterLeaves : Nat
  original : CoreBound mode bytes checked.core
  coreBound : checkCore mode bytes = .ok checked.core
  leavesBound : (HierarchyView.reconstructLeaves checked.core.requests).run work =
    (.ok checked.matrices,afterLeaves)
  extraBound : checked.core.extra.run afterLeaves = (.ok (),left)

theorem inspectMode_binding (mode : Mode) (bytes : ByteArray) (checked : Inspected) (work left : Nat)
    (ok : (inspectMode mode bytes).run work = (.ok checked,left)) :
    Nonempty (InspectionBinding mode bytes checked work left) := by
  unfold inspectMode at ok
  obtain ⟨core,w₁,hc,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨matrices,w₂,hm,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨unitResult,w₃,hx,h⟩ := bind_success _ _ _ _ _ h
  cases unitResult
  cases h
  have original := lift_success _ _ _ _ hc
  have nativeExtra := native_success _ _ _ _ hx
  have coreWork := original.2
  subst w₁
  exact ⟨⟨w₂,checkCore_bound mode bytes core original.1,original.1,
    native_success _ _ _ _ hm,nativeExtra⟩⟩

/-- Compare a plan derived from this call's exact original checks. -/
def checkMode (mode : Mode) (bytes supplied : ByteArray) : CheckM Inspected := do
  guard (framed supplied) .invalidView
  let checked ← inspectMode mode bytes
  let description ← native (checked.core.plan checked.matrices)
  let expected ← lift ((encode description).mapError fun _ => .encoding)
  guard (supplied.data == expected.data) .decodedView
  return checked

structure ComparisonBinding (mode : Mode) (bytes supplied : ByteArray) (checked : Inspected)
    (work left : Nat) where
  afterInspection : Nat
  description : Value
  framedView : framed supplied = true
  inspection : InspectionBinding mode bytes checked work afterInspection
  viewBound : (checked.core.plan checked.matrices).run afterInspection = (.ok description,left)
  compared : encode description = .ok supplied

theorem checkMode_binding (mode : Mode) (bytes supplied : ByteArray) (checked : Inspected) (work left : Nat)
    (ok : (checkMode mode bytes supplied).run work = (.ok checked,left)) :
    Nonempty (ComparisonBinding mode bytes supplied checked work left) := by
  unfold checkMode at ok
  obtain ⟨_,w₀,hf,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨inspected,w₁,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨description,w₂,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨expected,w₃,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,hs,h⟩ := bind_success _ _ _ _ _ h
  cases h
  have frame := guard_success _ _ _ _ hf
  have encoded := lift_success _ _ _ _ he
  have same := guard_success _ _ _ _ hs
  have equalData : supplied.data = expected.data := beq_iff_eq.mp same.1
  have equal : supplied = expected := by
    cases supplied; cases expected; cases equalData; rfl
  have encoding : encode description = .ok supplied := by
    cases h : encode description <;> simp_all [Except.mapError]
  have frameWork := frame.2
  have encodingWork := encoded.2
  have comparisonWork := same.2
  subst w₀; subst w₃; subst left
  obtain ⟨inspection⟩ := inspectMode_binding mode bytes checked work w₁ hi
  exact ⟨⟨w₁,description,frame.1,inspection,native_success _ _ _ _ hv,encoding⟩⟩

end QleisliKernel.Protocol.ExecutionView.CheckedHierarchy.Modes
