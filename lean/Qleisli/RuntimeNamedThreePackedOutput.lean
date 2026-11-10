import Qleisli.RuntimeNamedThreeFrameChain
import Qleisli.RuntimeBoundaryFrameEvidence
import Mathlib.Data.Fintype.Card

/-! Compose the actual original named call actions through the original final
Raw reorder into the exact packed result code.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedThreePackedOutput
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite (gather bit)
open RuntimeOwnerMap (Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.RuntimeForestProduct Qleisli.Semantics.Exact Qleisli.RuntimeNamedBlockEncoding

private theorem bit_above (row bits axis : Nat) (bounded : row < 2^bits)
    (above : bits ≤ axis) : bit row axis = 0 := by
  have power : 2^bits ≤ 2^axis := Nat.pow_le_pow_right (by decide) above
  simp [bit,Nat.div_eq_of_lt (Nat.lt_of_lt_of_le bounded power)]

/-- The exact original full return axes permute all finite physical rows. -/
theorem gather_bijective (bits : Nat) (axes : List Nat)
    (permutation : axes.Perm (List.range bits)) :
    ∃ projection : Fin (2^bits) → Fin (2^bits),
      Function.Bijective projection ∧ ∀ input,(projection input).val = gather input.val axes := by
  have width : axes.length = bits := permutation.length_eq.trans List.length_range
  let projection : Fin (2^bits) → Fin (2^bits) :=
    fun input => ⟨gather input.val axes, by simpa only [width] using gather_bound input.val axes⟩
  have injective : Function.Injective projection := by
    intro left right same
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro axis
    have equal : bit left.val axis = bit right.val axis := by
      by_cases inside : axis < bits
      · obtain ⟨index,bound,found⟩ := List.getElem_of_mem
          (permutation.mem_iff.mpr (List.mem_range.mpr inside))
        have gathered := congrArg (fun coordinate : Fin (2^bits) => bit coordinate.val index) same
        change bit (gather left.val axes) index = bit (gather right.val axes) index at gathered
        rwa [RuntimeScatterTransport.gather_at _ axes index bound,
          RuntimeScatterTransport.gather_at _ axes index bound,found] at gathered
      · rw [bit_above _ _ _ left.isLt (Nat.le_of_not_gt inside),
          bit_above _ _ _ right.isLt (Nat.le_of_not_gt inside)]
    simp only [bit] at equal
    rw [← Nat.toNat_testBit left.val axis,← Nat.toNat_testBit right.val axis] at equal
    cases leftBit : left.val.testBit axis <;> cases rightBit : right.val.testBit axis <;> simp_all
  exact ⟨projection,⟨injective,Finite.injective_iff_surjective.mp injective⟩,fun _ => rfl⟩

noncomputable def packedAction {roles state checked} (frame : @Frame roles state checked)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (ref : Reference) : ℂ :=
  ((List.range frame.code.dimension).map fun logical =>
    scalar (sparseEntry frame.code row logical) * joint logical ref).sum

/-- An original full-width Raw reorder selects one original physical row. -/
theorem reorder_gather (dependencies : List Semantics.Finite.Dependency)
    (bits : Nat) (axes : List Nat) (permutation : axes.Perm (List.range bits))
    (operator : Nat → ℂ) (row : Nat) (bounded : row < 2^bits) :
    ∃ original : Nat, original < 2^bits ∧ gather original axes = row ∧
      Qleisli.Semantics.RawAction.event dependencies (.reorder bits axes) operator row = operator original := by
  obtain ⟨projection,bijection,values⟩ := gather_bijective bits axes permutation
  obtain ⟨original,selected⟩ := bijection.2 ⟨row,bounded⟩
  have coordinate : gather original.val axes = row :=
    (values original).symm.trans (congrArg Fin.val selected)
  refine ⟨original.val,original.isLt,coordinate,?_⟩
  unfold Qleisli.Semantics.RawAction.event
  calc
    _ = ((List.range (2^bits)).map fun input =>
        if original.val = input then operator input else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro input present
      have bound : input < 2^bits := List.mem_range.mp present
      have only : gather input axes = row ↔ original.val = input := by
        constructor
        · intro result
          have same : projection original = projection ⟨input,bound⟩ := Fin.ext
            ((values original).trans (coordinate.trans (result.symm.trans (values ⟨input,bound⟩).symm)))
          exact congrArg Fin.val (bijection.1 same)
        · intro same
          rw [← same]
          exact coordinate
      change (if (gather input axes == row) = true then operator input else 0) = _
      simp only [beq_iff_eq,only]
    _ = operator original.val :=
      Qleisli.Exact.range_delta_sum _ _ _ original.isLt

/-- The complete return permutation expresses the existing sparse code in the
packed physical order of its original source owners. -/
theorem reorder_packed {roles state checked} (frame : @Frame roles state checked)
    (dependencies : List Semantics.Finite.Dependency)
    (permutation : (forestAxes state.quantum.frame checked.bindings).Perm
      (List.range state.quantum.frame.length))
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat)
    (bounded : row < 2^state.quantum.frame.length) (ref : Reference) :
    Qleisli.Semantics.RawAction.event dependencies
      (.reorder state.quantum.frame.length (forestAxes state.quantum.frame checked.bindings))
      (fun input => referenceAction frame joint input ref) row = packedAction frame joint row ref := by
  obtain ⟨original,_,coordinate,equation⟩ :=
    reorder_gather dependencies _ _ permutation (fun input => referenceAction frame joint input ref) row bounded
  rw [equation]
  unfold referenceAction packedAction
  apply Qleisli.Exact.sum_map_congr
  intro logical _
  change scalar (sparseEntry frame.code (gather original (forestAxes state.quantum.frame checked.bindings)) logical) *
      joint logical ref = scalar (sparseEntry frame.code row logical) * joint logical ref
  rw [coordinate]

theorem final_axes {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) :
    let tokens := checked.bindings.map (fun b => b.port.token)
    Semantics.RawTrace.axes state.quantum.reference
      (tokens.flatMap fun token => ((state.quantum.live.find? (fun p => p.token == token)).map (·.wires)).getD []) =
      forestAxes state.quantum.frame checked.bindings := by
  let wires := fun token : Nat => ((state.quantum.live.find? (fun p => p.token == token)).map (·.wires)).getD []
  change (List.flatMap wires (checked.bindings.map (fun b => b.port.token))).map state.quantum.frame.idxOf = _
  unfold forestAxes
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro binding member
  have live := checked.complete.mem_iff.mp (List.mem_map_of_mem member)
  have lookup := RuntimeNamedFrameAxes.tokenLookup state.quantum.live binding.port
    (Raw.Ownership.valid _ valid).owners live
  simp [wires,lookup]

theorem final_axes_permutation {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) :
    (forestAxes state.quantum.frame checked.bindings).Perm (List.range state.quantum.frame.length) := by
  have complete := checked.complete.flatMap_right (fun p => p.wires)
  simp only [List.flatMap_map] at complete
  have facts := Raw.Ownership.valid _ valid
  have size : (checked.bindings.flatMap (fun b => b.port.wires)).length = state.quantum.frame.length :=
    complete.length_eq.trans facts.count
  have wires : (checked.bindings.flatMap (fun b => b.port.wires)).Perm state.quantum.frame := by
    have subset : checked.bindings.flatMap (fun b => b.port.wires) ⊆ state.quantum.frame :=
      fun _ member => facts.covered _ (complete.mem_iff.mp member)
    obtain ⟨other,permuted,sublist⟩ := List.subperm_iff.mp ((complete.nodup_iff.mpr facts.exclusive).subperm subset)
    have same := sublist.eq_of_length (size.trans permuted.length_eq.symm)
    exact same ▸ permuted
  exact (wires.map state.quantum.frame.idxOf).trans
    (List.Perm.of_eq (RuntimeNamedCallerAction.self_indices _ facts.frame))

#print axioms reorder_packed
#print axioms final_axes
#print axioms final_axes_permutation

/-- The permutation appended by the original observing program reader. -/
def readerFinish (program : Semantics.Observation.Program) (state : Semantics.RawTrace.Interface) :
    Semantics.Raw.Event :=
  .reorder state.frame.length (Semantics.RawTrace.axes state (program.outputs.flatMap fun token =>
    ((state.live.find? (fun port => port.token == token)).map (·.wires)).getD []))

/-- The original checked result storage identifies the reader's final
permutation and its packed return encoding, for any original body trace. -/
theorem actual_root_finish {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) :
    let state := body.checked.native.whole.state
    let finish := Semantics.Raw.Event.reorder state.quantum.frame.length
      (forestAxes state.quantum.frame body.checked.owners.bindings)
    body.checked.native.whole.prepared.state = state.quantum.reference ∧
    readerFinish body.root.program body.checked.native.whole.prepared.state = finish ∧
    ∃ output : Frame body.checked.owners,
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row,
        row < 2^state.quantum.frame.length → ∀ ref,
          Qleisli.Semantics.RawAction.event body.root.dependencies finish
            (fun input => referenceAction output joint input ref) row = packedAction output joint row ref := by
  intro state finish
  obtain ⟨work,left,read⟩ := body.checked.native.verified
  have checked := Raw.Observation.verify_postcondition body.root.dependencies body.root.program
    body.checked.native.whole work left read
  have reference : body.checked.native.whole.prepared.state = state.quantum.reference := by
    have lives := checked.live
    have frames := checked.frame
    cases original : body.checked.native.whole.prepared.state with
    | mk live frame =>
      rw [original] at lives frames
      exact congrArg₂ Semantics.RawTrace.Interface.mk lives frames
  have outputs := body.checked.outputs.rawOutputs
  rw [body.checked.outputs.originalOwners] at outputs
  have tokens : body.root.program.outputs = body.checked.owners.bindings.map (fun binding => binding.port.token) := by
    simpa only [RuntimeSourceBoundary.returnedOwners,List.map_map] using outputs.symm
  obtain ⟨output⟩ := RuntimeBoundaryFrameEvidence.outputs_frame body.checked.outputs
  refine ⟨reference,?_,output,fun joint row bound ref =>
    reorder_packed output body.root.dependencies (final_axes_permutation _ checked.state) joint row bound ref⟩
  rw [reference,readerFinish,tokens]
  erw [final_axes body.checked.owners checked.state]
  rfl

/-- An original root consisting of the three calls ends with its packed return. -/
theorem actual_root_reorder {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    {pre center post : RuntimeAdjacentSlices.Span body.checked.native.block}
    {a b c : List Semantics.Raw.Event}
    (whole : RuntimeNamedThreeRoot.Whole body.checked.native pre center post a b c) :
    let state := body.checked.native.whole.state
    let axes := forestAxes state.quantum.frame body.checked.owners.bindings
    ∃ output : Frame body.checked.owners,
      body.checked.native.whole.prepared.events =
        (a++b++c).map Semantics.Observation.Event.pure ++
          [.pure (.reorder state.quantum.frame.length axes)] ∧
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row,
        row < 2^state.quantum.frame.length → ∀ ref,
          Qleisli.Semantics.RawAction.event body.root.dependencies
            (.reorder state.quantum.frame.length axes)
            (fun input => referenceAction output joint input ref) row = packedAction output joint row ref := by
  intro state axes
  obtain ⟨_reference,finish,output,action⟩ := actual_root_finish body
  have events := whole.finalEvents
  change body.checked.native.whole.prepared.events =
    (a++b++c).map Semantics.Observation.Event.pure ++
      [.pure (readerFinish body.root.program post.slice.interval.after.quantum.reference)] at events
  rw [← whole.finalState,finish] at events
  exact ⟨output,events,action⟩

#print axioms actual_root_finish
#print axioms actual_root_reorder

open RuntimeOwnerMap (Map)
open RuntimeOwnerCodeReindex
open Qleisli.RuntimeForestOrderedProduct

def PostReturnOrder {dependencies program block step}
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (returned : Map) : Prop :=
  match post with
  | .named (boundary := boundary) _ _ => returned.Perm boundary.afterFrame.bindings

theorem post_return_order {dependencies program block step roles}
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (last history : RuntimeStructuralAction.SourceState)
    (endState : RuntimeNamedSourceFlow.exitState step = some last)
    (returned : RuntimeNamedSourceFlow.Returned block roles last history)
    (ends : (RuntimeNamedOccurrenceAction.span post).start+(RuntimeNamedOccurrenceAction.span post).count =
      block.operations.length) : PostReturnOrder post history.bindings := by
  cases post with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary primitive original bound =>
    change some boundary.after = some last at endState
    have state := Option.some.inj endState
    subst last
    exact RuntimeNamedSelectionReturnOrder.returned_permutation scope.interval boundary.afterFrame returned
      boundary.sameAfter.symm ends

/-- The actual post return and the original checked result storage identify
the entire root output owner permutation, including every empty-wire owner. -/
theorem actual_root_return_order {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (ends : (RuntimeNamedOccurrenceAction.span view.postPrimitive).start+
      (RuntimeNamedOccurrenceAction.span view.postPrimitive).count = body.checked.native.block.operations.length) :
    PostReturnOrder view.postPrimitive body.checked.owners.bindings := by
  obtain ⟨_initial,_read,_entry,_first,_second,last,exit,returned⟩ :=
    RuntimeNamedSourceFlow.original_three body view
  rw [RuntimeBoundaryOwnerEvidence.check_bindings body.checked.owners body.checked.ownersRead]
  exact post_return_order view.postPrimitive last body.checked.result.history exit returned ends

/-- The exact source return permutation expresses the same complete encoded
caller output using the original written output order. -/
theorem recode_return {leftRoles leftState leftChecked rightRoles rightState rightChecked}
    (left : @Frame leftRoles leftState leftChecked) (right : @Frame rightRoles rightState rightChecked)
    (order : rightChecked.bindings.Perm leftChecked.bindings)
    (physicalFrame : rightState.quantum.frame = leftState.quantum.frame)
    {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (ref : Reference) :
    referenceAction left joint physical ref =
      referenceAction right (fun logical reference =>
        joint (Qleisli.MixedRadix.recode rightChecked.bindings leftChecked.bindings
          (dimensionAt left.owners) logical) reference) physical ref := by
  obtain ⟨reordered,kept⟩ := reindex_exists left.owners rightChecked.bindings order.subset
  rw [RuntimeNamedOutputOrder.regroup_dense_action left _ ⟨reordered,kept⟩ order]
  have same := RuntimeNamedCallerGeometry.codes_same rfl reordered right.owners _ _ physicalFrame
  have layout := frame_product_agrees right
  have dimension := layout.dimension.trans (product_agrees right.owners).dimension.symm
  unfold referenceAction
  rw [dimension,← same.1]
  apply Qleisli.Exact.sum_map_congr
  intro logical member
  have bounded : logical < (sparseProduct right.owners).dimension := same.1 ▸ List.mem_range.mp member
  have product := product_coefficient rightState.quantum.frame right.owners physical logical bounded
  change _ = scalar (sparseEntry right.code
    (gather physical (forestAxes rightState.quantum.frame rightChecked.bindings)) logical) * _
  have sparse : sparseEntry right.code
      (gather physical (forestAxes rightState.quantum.frame rightChecked.bindings)) logical =
      sparseEntry (.ofLayout (layoutProduct right.owners))
        (gather physical (forestAxes rightState.quantum.frame rightChecked.bindings)) logical := by
    unfold sparseEntry
    rw [layout.labels logical]
    rfl
  rw [sparse,product,same.2]

#print axioms actual_root_return_order
#print axioms recode_return

open Qleisli.RuntimeNamedThreeFrameChain (PostFrame encodePost)

noncomputable def packedCallerReturn {dependencies program block step roles state checked}
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (output : @Frame roles state checked) (caller : PostFrame post)
    {Reference : Type} (joint : Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  match step,post,caller with
  | _,.named (boundary := boundary) _ _,caller =>
    packedAction output (fun logical reference =>
      joint (Qleisli.MixedRadix.recode checked.bindings boundary.afterFrame.bindings
        (dimensionAt caller.owners) logical) reference)

def FinishCaller {dependencies program block step roles state checked}
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (output : @Frame roles state checked) (finish : Semantics.Raw.Event) : Prop :=
  ∀ caller : PostFrame post, ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row,
    row < 2^state.quantum.frame.length → ∀ ref,
      Qleisli.Semantics.RawAction.event dependencies finish
        (fun input => encodePost post caller joint input ref) row =
      packedCallerReturn post output caller joint row ref

theorem finish_caller {dependencies program block step roles state checked}
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (output : @Frame roles state checked) (finish : Semantics.Raw.Event)
    (order : PostReturnOrder post checked.bindings)
    (physicalFrame : state.quantum.frame =
      (RuntimeNamedOccurrenceAction.span post).slice.interval.after.quantum.frame)
    (reorder : ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row,
      row < 2^state.quantum.frame.length → ∀ ref,
        Qleisli.Semantics.RawAction.event dependencies finish
          (fun input => referenceAction output joint input ref) row =
        packedAction output joint row ref) :
    FinishCaller post output finish := by
  cases post with
  | @named start count inputs sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary primitive original bound =>
    dsimp only [FinishCaller,PostFrame,encodePost,packedCallerReturn]
    intro caller Reference joint row bounded ref
    have encoding : (fun input => referenceAction caller joint input ref) =
        fun input => referenceAction output (fun logical reference =>
          joint (Qleisli.MixedRadix.recode checked.bindings boundary.afterFrame.bindings
            (dimensionAt caller.owners) logical) reference) input ref := by
      funext input
      exact recode_return caller output order physicalFrame joint input ref
    rw [encoding]
    exact reorder _ row bounded ref

/-- Identify the packed result of the actual final event on any exact logical
family in the original post caller frame. The written source return supplies
the only owner recode between that frame and result storage. -/
theorem original_post_finish {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_body_middle body view))
    {a b c : List Semantics.Raw.Event}
    (whole : RuntimeNamedThreeRoot.Whole body.checked.native
      (RuntimeNamedOccurrenceAction.span view.prePrimitive)
      (RuntimeNamedSelectionOn.middle view.centerSelection
        (RuntimeNamedThreeOccurrence.actual_body_middle body view) coverage)
      (RuntimeNamedOccurrenceAction.span view.postPrimitive) a b c)
    (ends : (RuntimeNamedOccurrenceAction.span view.postPrimitive).start+
      (RuntimeNamedOccurrenceAction.span view.postPrimitive).count = body.checked.native.block.operations.length) :
    let state := body.checked.native.whole.state
    let finish := Semantics.Raw.Event.reorder state.quantum.frame.length
      (forestAxes state.quantum.frame body.checked.owners.bindings)
    ∃ output : Frame body.checked.owners,
      body.checked.native.whole.prepared.events =
        (a++b++c).map Semantics.Observation.Event.pure ++ [.pure finish] ∧
      FinishCaller view.postPrimitive output finish := by
  intro state finish
  obtain ⟨output,events,reorder⟩ := actual_root_reorder body whole
  have returned := actual_root_return_order body view ends
  obtain ⟨work,left,read⟩ := body.checked.native.verified
  have checked := Raw.Observation.verify_postcondition body.root.dependencies body.root.program
    body.checked.native.whole work left read
  have physicalFrame := checked.frame.symm.trans (congrArg Semantics.RawTrace.Interface.frame whole.finalState)
  exact ⟨output,events,finish_caller view.postPrimitive output finish returned physicalFrame reorder⟩

#print axioms original_post_finish

/-- The terminal post call in a longer observing traversal has the same
source return order and physical frame as the original packed result. -/
theorem original_adjacent_post_finish {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Adjacent body.checked.result.steps)
    (terminal : view.later = [])
    (ends : (RuntimeNamedOccurrenceAction.span view.postPrimitive).start+
      (RuntimeNamedOccurrenceAction.span view.postPrimitive).count = body.checked.native.block.operations.length)
    (finalState : body.checked.native.whole.prepared.state =
      (RuntimeNamedOccurrenceAction.span view.postPrimitive).slice.interval.after.quantum.reference) :
    let state := body.checked.native.whole.state
    let finish := Semantics.Raw.Event.reorder state.quantum.frame.length
      (forestAxes state.quantum.frame body.checked.owners.bindings)
    readerFinish body.root.program body.checked.native.whole.prepared.state = finish ∧
    state.quantum.frame = (RuntimeNamedOccurrenceAction.span view.postPrimitive).slice.interval.after.quantum.frame ∧
    ∃ output : Frame body.checked.owners, FinishCaller view.postPrimitive output finish := by
  intro state finish
  obtain ⟨last,exit,returned⟩ := RuntimeNamedSourceFlow.original_adjacent_return body view terminal
  have order : PostReturnOrder view.postPrimitive body.checked.owners.bindings := by
    rw [RuntimeBoundaryOwnerEvidence.check_bindings body.checked.owners body.checked.ownersRead]
    exact post_return_order view.postPrimitive last body.checked.result.history exit returned ends
  obtain ⟨reference,actual,output,reorder⟩ := actual_root_finish body
  have physicalFrame := congrArg Semantics.RawTrace.Interface.frame (reference.symm.trans finalState)
  exact ⟨actual,physicalFrame,output,finish_caller view.postPrimitive output finish order physicalFrame reorder⟩

#print axioms original_adjacent_post_finish

open Qleisli.RuntimeNamedThreeFrameChain (checkedAt frameAt Composed ComposedAt originalBindings PointwiseAction EntryFrame)
open Qleisli.RuntimeNamedSelectionWholeOutput (callerUpdate)
open Qleisli.RuntimeNamedCallerAction (updatedJoint)
open Qleisli.RuntimeForestOrderedProduct

/-- The packed logical output uses the same three original source actions and
the owner order of the original source return. -/
def PackedComposition {dependencies program block preStep centerStep postStep rootItem rootCount
    inputRoles outputRoles state checked}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block preStep)
    (center : @RuntimeNamedThreeOccurrence.Middle dependencies program block centerStep)
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block postStep)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness center)
    (initial : RuntimeOwnerMap.Checked inputRoles block.entry)
    (result : @Frame outputRoles state checked)
    (a b c : List Semantics.Raw.Event) (finish : Semantics.Raw.Event) : Prop :=
  match preStep,centerStep,postStep,pre,center,post,held with
  | _,_,_,.named (before := before) (scope := preScope) (boundary := preBoundary) (action := preOp) _ preBound,
    .named (childHistory := child) (scope := centerScope) (boundary := centerBoundary) _ _,
    .named (scope := postScope) (boundary := postBoundary) (action := postOp) _ postBound,held =>
    match held.literal with
    | .selection (frame := frame) (inputCode := inCode) (outputCode := outCode)
        (retained := retained) (labels := labels) (expected := expected)
        (codes := codes) (layouts := layouts) literal _ =>
        ∃ same : block.entry = preScope.interval.before,
        ∃ input : Frame (checkedAt same initial),
        (checkedAt same initial).bindings = before.bindings ∧
        ∃ firstState : preScope.interval.after = centerScope.interval.before,
        ∃ secondState : centerScope.interval.after = postScope.interval.before,
        ∃ first : Frame preBoundary.afterFrame,
        ∃ second : Frame centerBoundary.afterFrame,
        ∃ output : Frame postBoundary.afterFrame,
        ∃ preReturned postReturned : Binding,
          preBoundary.mapped = [preReturned] ∧ postBoundary.mapped = [postReturned] ∧
          let centerInput := frameAt firstState first
          let postInput := frameAt secondState second
          let selected := centerBoundary.input.ordered
          let spectators := RuntimeSelectionPartition.complement
            (checkedAt firstState preBoundary.afterFrame).bindings selected
          ∃ selectedCodes : OwnerCodes selected, ∃ beforeCodes : OwnerCodes spectators,
            reindex centerInput.owners (selected++spectators) = some (append selectedCodes beforeCodes) ∧
            ∃ mappedCodes : OwnerCodes centerBoundary.mapped, ∃ afterCodes : OwnerCodes spectators,
              reindex second.owners (centerBoundary.mapped++spectators) = some (append mappedCodes afterCodes) ∧
              ∃ table : Qleisli.RuntimeMultiwayGram.OrdinalTable inCode outCode retained.sectors labels expected,
              ∀ {Reference : Type} (joint : Nat → Reference → ℂ) row,
                row < 2^state.quantum.frame.length → ∀ ref,
                  Qleisli.Semantics.RawAction.events dependencies (a++b++c++[finish])
                    (fun physical => referenceAction input joint physical ref) row =
                  packedAction result (fun logical reference =>
                    updatedJoint postInput output postBound.binding postReturned postOp.expected
                  (callerUpdate centerInput literal.outputCode second (selected++spectators)
                    child.bindings (centerBoundary.mapped++spectators)
                    (sparseProduct selectedCodes).dimension (sparseProduct mappedCodes).dimension
                    (Qleisli.RuntimeMultiwayGram.sourceAction frame codes layouts literal table)
                    (updatedJoint input first preBound.binding preReturned preOp.expected joint))
                    (Qleisli.MixedRadix.recode checked.bindings postBoundary.afterFrame.bindings
                      (dimensionAt output.owners) logical) reference) row ref


theorem packed_composition {dependencies program block preStep centerStep postStep rootItem rootCount
    inputRoles outputRoles state checked}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (pre : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block preStep)
    (center : @RuntimeNamedThreeOccurrence.Middle dependencies program block centerStep)
    (post : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block postStep)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness center)
    (initial : RuntimeOwnerMap.Checked inputRoles block.entry)
    (result : @Frame outputRoles state checked)
    (a b c : List Semantics.Raw.Event) (finish : Semantics.Raw.Event)
    (entry : EntryFrame pre initial)
    (chain : Composed pre center post held a b c)
    (reorder : FinishCaller post result finish) :
    PackedComposition pre center post held initial result a b c finish := by
  cases pre
  cases center
  cases post
  dsimp only [EntryFrame,Composed,ComposedAt,originalBindings,PointwiseAction,encodePost,FinishCaller,packedCallerReturn,PackedComposition] at *
  cases stored : held.literal
  case selection =>
    rw [stored] at chain
    obtain ⟨same,input,bindings⟩ := entry
    obtain ⟨firstState,secondState,first,second,output,preReturned,postReturned,
      preMapped,postMapped,selectedCodes,beforeCodes,inputRead,mappedCodes,afterCodes,outputRead,table,action⟩ :=
      chain _ input bindings
    refine ⟨same,input,bindings,firstState,secondState,first,second,output,preReturned,postReturned,
      preMapped,postMapped,selectedCodes,beforeCodes,inputRead,mappedCodes,afterCodes,outputRead,table,?_⟩
    intro Reference joint row bounded ref
    have composed := funext fun physical => action joint physical ref
    simp only [Qleisli.Semantics.RawAction.events,List.foldl_append,List.foldl_cons,List.foldl_nil] at composed ⊢
    erw [composed]
    exact reorder output _ row bounded ref

/-- The original input storage, actual complete three-call event list and
original return storage satisfy one exact finite-row equation. -/
theorem original_three_packed {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_body_middle body view)) :
    let held := RuntimeNamedThreeOccurrence.actual_body_middle body view
    let pre := RuntimeNamedOccurrenceAction.span view.prePrimitive
    let center := RuntimeNamedSelectionOn.middle view.centerSelection held coverage
    let post := RuntimeNamedOccurrenceAction.span view.postPrimitive
    let source := QleisliKernel.SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let initial := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    let state := body.checked.native.whole.state
    let finish := Semantics.Raw.Event.reorder state.quantum.frame.length
      (forestAxes state.quantum.frame body.checked.owners.bindings)
    pre.start = 0 → center.start = pre.start+pre.count → post.start = center.start+center.count →
    pre.count+center.count+post.count = body.root.program.operations.length →
    ∃ a b c, body.checked.native.whole.prepared.events =
        (a++b++c++[finish]).map Semantics.Observation.Event.pure ∧
      ∃ checked : RuntimeOwnerMap.Checked source.initialRoles body.checked.native.block.entry,
        RuntimeInterval.Computed
          (RuntimePureBody.reordered source.initialRoles body.checked.native.block.entry initial.bindings) checked ∧
        ∃ result : Frame body.checked.owners,
          PackedComposition view.prePrimitive view.centerSelection view.postPrimitive held checked result a b c finish := by
  intro held pre center post source initial state finish starts next last covers
  obtain ⟨a,b,c,whole,chain,checked,read,entry⟩ :=
    RuntimeNamedThreeFrameChain.original_three_composed body view coverage starts next last covers
  have ends : post.start+post.count = body.checked.native.block.operations.length := by
    change post.start+post.count = body.root.program.operations.length
    omega
  obtain ⟨result,events,reorder⟩ := original_post_finish body view coverage whole ends
  refine ⟨a,b,c,?_,checked,read,result,packed_composition _ _ _ held checked result a b c finish entry chain reorder⟩
  simpa only [List.map_append,List.map_cons,List.map_nil] using events

#print axioms original_three_packed

end Qleisli.RuntimeNamedThreePackedOutput
