import Qleisli.RuntimeComputedForest
import Qleisli.RawProtected
import Qleisli.RuntimeSemanticSelectionFibre
import Qleisli.StructuralComputedRestoration

/-! A checked original protected body acts diagonally on its logical owner's
digit. The independent Raw trace acts by the same phase on the complete
caller encoding, including padding and correlated reference columns.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeComputedCallerAction
open QleisliKernel QleisliKernel.Qirf
open Qirf.RuntimeComputedUse (Checked)
open RuntimeOwnerMap (Binding Map)
open RuntimeSemanticForest (Frame ownerLayout)
open RuntimeForestCode (embed forestAxes)
open Semantics.Finite (gather scatter)
open Qleisli.Semantics.Exact (scalar)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (decode)

def predicateChoice {sources caller event} (prepared : @RuntimeComputedUse.Prepared sources caller event)
    (physical : Nat) : Nat :=
  prepared.predicate.table[physical]?.getD 0

noncomputable def phaseAt {sources caller event} (prepared : @RuntimeComputedUse.Prepared sources caller event)
    (physical : Nat) : ℂ :=
  let choice := predicateChoice prepared physical
  scalar (prepared.action.matrix.entry choice choice)

noncomputable def sourceOperator {sources caller event} (prepared : @RuntimeComputedUse.Prepared sources caller event)
    (bindings : Map) (operand : Binding) {R : Type} (joint : Nat → R → ℂ) (logical : Nat) (reference : R) : ℂ :=
  let digit := decode bindings (sourceDimension bindings) logical operand
  let code := (ownerLayout operand).labels[digit]?.getD 0
  joint logical reference * phaseAt prepared code

theorem literal_phase {sources caller dependencies program block start count event prepared interval before}
    (checked : @Checked sources caller dependencies program block start count event prepared interval before)
    (ψ : Nat → ℂ) (row : Nat) :
    let port := checked.literal.input.port
    let frame := interval.before.quantum.frame
    let axes := port.wires.map frame.idxOf
    Qleisli.Semantics.RawAction.event dependencies
      (.protectedComputed frame.length axes port.bits 1 checked.literal.table checked.literal.uses) ψ row =
    ψ row * phaseAt prepared (gather row axes) := by
  intro port frame axes
  let operand : Binding := ⟨event.input,port⟩
  have member : operand ∈ checked.literal.frame.bindings :=
    checked.literal.sameFrame.symm ▸ RuntimeBasisOwnerGeometry.selected_binding checked.literal.input
  have live : port ∈ interval.before.quantum.live :=
    checked.literal.frame.complete.mem_iff.mp (List.mem_map.mpr ⟨operand,member,rfl⟩)
  have valid := Raw.Ownership.valid _ interval.history.1
  have axesUnique : axes.Nodup := by
    have allAxes := RuntimeNamedInputAction.axes_unique checked.literal.frame interval.history.1
    have perPort : (checked.literal.frame.bindings.flatMap (fun b => b.port.wires.map frame.idxOf)).Nodup := by
      simpa only [forestAxes,List.map_flatMap] using allAxes
    exact (List.nodup_flatMap.mp perPort).1 operand member
  have width : axes.length = port.bits := (List.length_map _).trans (valid.ports port live).1.symm
  let code := gather row axes
  have bounded : code < 2^port.bits := by
    rw [← width]
    exact RuntimeForestProduct.gather_bound row axes
  have geometry := RuntimeComputedGeometry.literal_geometry checked.literal
  have table := geometry.2.1
  simp only [Raw.tableValid,Bool.not_false,Bool.true_or,Bool.and_true,Bool.and_eq_true,beq_iff_eq,Nat.pow_one] at table
  have diagonal := Qleisli.Raw.uses_valid_diagonal _ _ _ _ geometry.2.2.1
  have index : code < checked.literal.table.length := table.1 ▸ bounded
  let choice := checked.literal.table[code]
  have found : checked.literal.table[code]? = some choice := List.getElem?_eq_getElem index
  have good : choice < 2 :=
    of_decide_eq_true (List.all_eq_true.mp table.2 choice (List.mem_of_getElem? found))
  have original : prepared.predicate.table[code]? = some choice := checked.literal.exactTable ▸ found
  have bit : choice = 0 ∨ choice = 1 := by omega
  let fibre : Qleisli.Semantics.Protected.Logical Unit := fun source target _ =>
    ψ (scatter row axes (source+target*2^port.bits))
  have applyPhase := Qleisli.RuntimeComputedProtectedAction.original_phase checked fibre code 0 () original bit
  change Qleisli.Semantics.Protected.compute (fun i => checked.literal.table[i]?.getD 0)
      (Qleisli.Semantics.Protected.run checked.literal.uses
        (Qleisli.Semantics.Protected.compute (fun i => checked.literal.table[i]?.getD 0)
          (Qleisli.Semantics.Protected.zero fibre)))
      (code % 2^port.bits) 0 (code / 2^port.bits) () = _
  rw [Qleisli.Semantics.Protected.clean_factorization _ _ diagonal fibre,
    Nat.mod_eq_of_lt bounded,Nat.div_eq_of_lt bounded]
  simp only [Qleisli.Semantics.Protected.zero,if_true]
  rw [applyPhase]
  simp only [fibre,Nat.zero_mul,Nat.add_zero,code,RuntimeScatterTransport.scatter_gather row axes axesUnique,
    phaseAt,predicateChoice,original,Option.getD_some]

theorem original_reference_action
    {sources caller dependencies program block start count event prepared interval before}
    (checked : @Checked sources caller dependencies program block start count event prepared interval before)
    (input : Frame before.bindings) :
    let operand : Binding := ⟨event.input,checked.literal.input.port⟩
    let frame := interval.before.quantum.frame
    let raw := Semantics.Raw.Event.protectedComputed frame.length
      (operand.port.wires.map frame.idxOf) operand.port.bits 1 checked.literal.table checked.literal.uses
    ∃ output : Frame checked.literal.after.bindings, ∀ {R : Type}
      (joint : Nat → R → ℂ) (physical : Nat) (reference : R),
      Qleisli.Semantics.RawAction.event dependencies raw
        (fun row => RuntimeSemanticForest.action input frame joint row reference) physical =
      RuntimeSemanticForest.action output interval.after.quantum.frame
        (sourceOperator prepared before.bindings operand joint) physical reference := by
  intro operand frame raw
  obtain ⟨output,rebound⟩ := RuntimeComputedForest.rebound_encoding checked.literal input
  refine ⟨output,?_⟩
  intro R joint physical reference
  rw [rebound,show Qleisli.Semantics.RawAction.event dependencies raw
      (fun row => RuntimeSemanticForest.action input frame joint row reference) physical =
      RuntimeSemanticForest.action input frame joint physical reference *
        phaseAt prepared (gather physical (operand.port.wires.map frame.idxOf)) from literal_phase checked _ _]
  have member : operand ∈ before.bindings := RuntimeBasisOwnerGeometry.selected_binding checked.literal.input
  have unique : before.bindings.Nodup := checked.literal.sameFrame ▸
    RuntimeSemanticSelectionFibre.unique_bindings checked.literal.frame
  unfold RuntimeSemanticForest.action
  rw [← List.sum_map_mul_right]
  apply Qleisli.Exact.sum_map_congr
  intro logical present
  by_cases zero : scalar (embed frame before.bindings input.code physical logical) = 0
  · simp only [frame,zero,zero_mul]
  · obtain ⟨_,code⟩ := RuntimeSemanticForest.owner_support input unique operand member frame physical logical
      (List.mem_range.mp present) zero
    simp only [sourceOperator,code,Option.getD_some,mul_assoc,frame]

noncomputable def structuralPhaseAt {sources caller compute inverse uses}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event}
    (checked : StructuralComputedUse.Checked original compute inverse uses) (physical : Nat) : ℂ :=
  let choice := StructuralComputedRestoration.selected original physical
  scalar (checked.action.matrix.entry choice choice)

noncomputable def structuralSourceOperator {sources caller compute inverse uses}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event}
    (checked : StructuralComputedUse.Checked original compute inverse uses)
    (bindings : Map) (operand : Binding) {R : Type} (joint : Nat → R → ℂ)
    (logical : Nat) (reference : R) : ℂ :=
  let digit := decode bindings (sourceDimension bindings) logical operand
  let code := (ownerLayout operand).labels[digit]?.getD 0
  joint logical reference * structuralPhaseAt checked code

theorem structural_literal_phase {sources caller dependencies program block start count before}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (checked : StructuralComputedRaw.IntervalChecked event interval before)
    (ψ : Nat → ℂ) (row : Nat) :
    let frame := interval.before.quantum.frame
    let axes := checked.checked.raw.input.wires.map frame.idxOf
    Qleisli.Semantics.RawAction.event dependencies
      (.structuralComputed frame.length axes checked.packet.forward checked.packet.inverse checked.packet.uses) ψ row =
    ψ row * structuralPhaseAt checked.checked.matched (gather row axes) := by
  intro frame axes
  let action := checked.checked
  let operand : Binding := ⟨event.input,action.owner.port⟩
  have member : operand ∈ action.frame.bindings :=
    action.sameFrame.symm ▸ RuntimeBasisOwnerGeometry.selected_binding action.owner
  have live : action.owner.port ∈ interval.before.quantum.live :=
    action.frame.complete.mem_iff.mp (List.mem_map.mpr ⟨operand,member,rfl⟩)
  have valid := Raw.Ownership.valid _ action.raw.inputValid
  have unique : axes.Nodup := by
    have allAxes := RuntimeNamedInputAction.axes_unique action.frame action.raw.inputValid
    have perPort : (action.frame.bindings.flatMap (fun b => b.port.wires.map frame.idxOf)).Nodup := by
      simpa only [forestAxes,List.map_flatMap] using allAxes
    have ownerAxes := (List.nodup_flatMap.mp perPort).1 operand member
    simpa only [operand,action.sameInput] using ownerAxes
  have width : axes.length = checked.original.width := by
    change (action.raw.input.wires.map frame.idxOf).length = _
    rw [← action.sameInput,List.length_map]
    exact ((valid.ports action.owner.port live).1.symm).trans (action.sameInput ▸ action.width)
  exact StructuralComputedRestoration.literal_event action.matched action.raw.diagonalUses dependencies
    frame.length axes width unique ψ row

private theorem structural_output_wires {sources caller packet before entry}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event}
    (checked : StructuralComputedRaw.SourceChecked original packet before entry) :
    checked.output.wires = checked.owner.port.wires := by
  obtain ⟨port,present,token,wires⟩ := checked.raw.returnedPort
  have valid := Raw.Ownership.valid _ checked.raw.outputValid
  have read := RuntimeNamedFrameAxes.tokenLookup checked.raw.after.live port valid.owners present
  rw [token] at read
  have given := checked.returned
  simp only [PureInterval.ports,PureInterval.portsOf,List.mapM_cons,List.mapM_nil,read,bind,
    Option.bind,pure,Option.some.injEq,List.cons.injEq,and_true] at given
  exact given.symm ▸ (wires.trans (congrArg (·.wires) checked.sameInput).symm)

/-- The source phase and the literal Raw event act equally on the actual
caller encoding, with every spectator owner and reference retained. -/
theorem structural_reference_action
    {sources caller dependencies program block start count before}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (checked : StructuralComputedRaw.IntervalChecked event interval before) (input : Frame before.bindings) :
    let action := checked.checked
    let operand : Binding := ⟨event.input,action.owner.port⟩
    let frame := interval.before.quantum.frame
    let axes := action.raw.input.wires.map frame.idxOf
    let raw := Semantics.Raw.Event.structuralComputed frame.length axes checked.packet.forward
      checked.packet.inverse checked.packet.uses
    ∃ output : Frame action.continuation.bindings, ∀ {R : Type}
      (joint : Nat → R → ℂ) (physical : Nat) (reference : R),
      Qleisli.Semantics.RawAction.event dependencies raw
        (fun row => RuntimeSemanticForest.action input frame joint row reference) physical =
      RuntimeSemanticForest.action output interval.after.quantum.frame
        (structuralSourceOperator action.matched before.bindings operand joint) physical reference := by
  intro action operand frame axes raw
  obtain ⟨output,rebound⟩ := RuntimeComputedForest.rebound_encoding_of_ports
    action.owner action.output action.frame action.continuation action.sameContinuation
    event.returned.dataType (structural_output_wires action) action.raw.sameFrame action.raw.outputValid input
  refine ⟨output,?_⟩
  intro R joint physical reference
  rw [← checked.afterQuantum, rebound, structural_literal_phase checked]
  have member : operand ∈ before.bindings := RuntimeBasisOwnerGeometry.selected_binding action.owner
  have unique : before.bindings.Nodup :=
    action.sameFrame ▸ RuntimeSemanticSelectionFibre.unique_bindings action.frame
  unfold RuntimeSemanticForest.action
  rw [← List.sum_map_mul_right]
  apply Qleisli.Exact.sum_map_congr
  intro logical present
  by_cases zero : scalar (embed frame before.bindings input.code physical logical) = 0
  · simp only [frame,zero,zero_mul]
  · obtain ⟨_,code⟩ := RuntimeSemanticForest.owner_support input unique operand member frame physical logical
      (List.mem_range.mp present) zero
    have sameAxes :
        checked.checked.raw.input.wires.map interval.before.quantum.frame.idxOf =
          operand.port.wires.map interval.before.quantum.frame.idxOf := by
      simp only [operand,action,checked.checked.sameInput]
    simp only [structuralSourceOperator,code,Option.getD_some,mul_assoc,frame,sameAxes,action]

#print axioms original_reference_action
#print axioms structural_reference_action
end Qleisli.RuntimeComputedCallerAction
