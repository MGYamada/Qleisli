import Qleisli.RuntimeSparseSelectionAction
import Qleisli.RuntimeNamedSelectionWholeOutput

/-! Reassemble the actual original selection in the full sparse caller output.
The returned child coordinates and the unchanged spectator fibres use their
real owner order, including zero-width owners and arbitrary reference columns.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSparseSelectionOutput
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite (gather scatter)
open QleisliKernel.Semantics.Exact (Matrix)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (carrierOwners forestAxes embed)
open Qleisli.RuntimeSemanticForest (Available Frame action product product_agrees frame_exists ofNative ofNative_action regroup_action)
open Qleisli.RuntimeSparseBlockEncoding (coefficient available_carriers product_carriers blockJoint block_result coefficient_scatter)
open Qleisli.RuntimeForestOrderedProduct (agrees_entry)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.RuntimeNamedSelectionOutputCodes (gather_scatter_wires)
open Qleisli.RuntimeNamedCarrierEncoding (carrier_wires)
open Qleisli.RuntimeNamedSelectionReturnOrder (caller_after_order)
open Qleisli.RuntimeNamedBlockEncoding (original_named_partition_geometry)
open Qleisli.RuntimeNamedSelectionWholeOutput (onFinite onFinite_reference ordinal_fibre)
open Qleisli.RuntimeNamedHeadCoefficients (fibre)
open Qleisli.RuntimeMultiwayGram (OrdinalTable sourceAction)
open Qleisli.MixedRadix (recode)

private theorem bindings_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    checked.bindings.Nodup :=
  List.Pairwise.of_map (fun b : Binding => b.port.token)
    (fun _ _ different same => different (congrArg (fun b : Binding => b.port.token) same))
    checked.tokensDistinct

/-- The actual selected output in caller coordinates is the returned child
code. Its ordered source aliases retain exact carrier layouts and wires. -/
theorem regrouped_output {childBindings returned mapped spectators : Map}
    (child : Frame childBindings) (childReturned : Frame returned) (output : Frame (mapped++spectators))
    (childOrder : childBindings.Perm returned) (childDistinct : childBindings.Nodup)
    (same : carrierOwners mapped = carrierOwners returned)
    (childFrame parentFrame axes : List Nat)
    (coordinates : childFrame.map parentFrame.idxOf = axes) (unique : axes.Nodup)
    (inside : returned.flatMap (·.port.wires) ⊆ childFrame)
    {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (base physical : Nat) (reference : Reference) :
    action output parentFrame (blockJoint (product mapped).labels.length
      (fun digit high ref => joint (recode returned childBindings (sourceDimension childBindings) digit) high ref))
      (scatter base axes physical) reference =
    action child childFrame (fun digit ref =>
      ((List.range (product spectators).labels.length).map fun high =>
        coefficient spectators parentFrame (scatter base axes physical) high * joint digit high ref).sum)
      physical reference := by
  have mappedAvailable : Available mapped := fun b member => output.available b (List.mem_append_left _ member)
  have sameLayout := product_carriers same childReturned.available mappedAvailable
  rw [block_result output,regroup_action child childReturned childOrder childDistinct]
  unfold action
  rw [(product_agrees childReturned).dimension,sameLayout]
  apply Qleisli.Exact.sum_map_congr
  intro digit _
  unfold coefficient embed
  rw [agrees_entry (product_agrees childReturned),sameLayout]
  unfold forestAxes
  rw [carrier_wires same,gather_scatter_wires childFrame parentFrame _ axes coordinates unique inside]

/-- Independently apply the child source table at each spectator coordinate
and interpret the result in the original caller's returned owner order. -/
noncomputable def callerUpdate {Reference : Type} {childRoles childState childChecked}
    (child : @RuntimeForestCode.Frame childRoles childState childChecked)
    (incoming inputOrder childReturn output outputOrder : Map) (inputLow outputLow : Nat)
    (run : (Nat → Reference → ℂ) → Fin child.code.dimension → Reference → ℂ)
    (joint : Nat → Reference → ℂ) (logical : Nat) (reference : Reference) : ℂ :=
  blockJoint outputLow (fun digit high ref =>
    onFinite (run (fun localDigit localRef =>
      joint (recode inputOrder incoming (sourceDimension incoming) (localDigit+inputLow*high)) localRef))
      (recode childReturn childChecked.bindings (sourceDimension childChecked.bindings) digit) ref)
    (recode output outputOrder (sourceDimension outputOrder) logical) reference

open Qleisli.RuntimeNamedSelectionReturnOrder (actual_occurrence_return_order OccurrenceReturnOrder)
open Qleisli.RuntimeForestProduct (referenceAction)

def CallWholeOutput
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {first size localInputs outputs selector target}
    (frame : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval localInputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (_equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels expected) logical)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (events : List Semantics.Raw.Event)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked.bindings) : Prop :=
  logical = expected ∧
  let selected := boundary.input.ordered
  let spectators := RuntimeSelectionPartition.complement checked.bindings selected
  ∃ output : Frame boundary.afterFrame.bindings,
  ∃ table : OrdinalTable inputCode outputCode retained.sectors labels expected,
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) physical reference,
      Qleisli.Semantics.RawAction.events dependencies events
        (fun row => action parent scope.interval.before.quantum.frame joint row reference) physical =
      action output scope.interval.after.quantum.frame
        (callerUpdate literal.outputCode checked.bindings (selected++spectators) child.bindings
          boundary.afterFrame.bindings (boundary.mapped++spectators) (product selected).labels.length
          (product boundary.mapped).labels.length (sourceAction frame codes layouts literal table) joint)
        physical reference

theorem call_whole_output
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {first size localInputs outputs selector target}
    (frame : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval localInputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels expected) logical)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (events : List Semantics.Raw.Event)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked.bindings)
    (sameBindings : checked.bindings = before.bindings)
    (starts : first = 0) (covers : size = ((block.operations.drop callStart).take callCount).length)
    (returned : child.bindings.Perm codes.owners.transport.after.bindings)
    (inputLaw : Qleisli.RuntimeSparseSelectionAction.CallSourceAction scope boundary frame codes layouts equations literal events checked parent) :
    CallWholeOutput scope boundary frame codes layouts equations literal events checked parent := by
  let chosen := boundary.input.ordered
  let spectators := RuntimeSelectionPartition.complement checked.bindings chosen
  let childFrame := ofNative literal.outputCode
  have childAvailable : Available child.bindings :=
    fun binding member => childFrame.available binding (returned.subset member)
  obtain ⟨childReturned⟩ := frame_exists childAvailable
  have carriers := RuntimeNamedCodeTransport.returned_carriers boundary
  have mappedAvailable := available_carriers carriers childAvailable
  have inputOrder := original_named_partition_geometry scope boundary checked sameBindings
  have outputOrder := (caller_after_order scope boundary checked sameBindings).2
  have spectatorsAvailable : Available spectators := fun b member =>
    parent.available b (inputOrder.subset (List.mem_append_right _ member))
  have available : Available (boundary.mapped++spectators) := by
    intro b member
    rcases List.mem_append.mp member with selected | other
    · exact mappedAvailable b selected
    · exact spectatorsAvailable b other
  obtain ⟨orderedOutput⟩ := frame_exists available
  obtain ⟨output⟩ := frame_exists (fun b member => available b (outputOrder.symm.subset member))
  obtain ⟨sameLogical,table,actionLaw⟩ := inputLaw
  obtain ⟨_events,_trace,_action,geometry⟩ := RuntimeNamedSelectionParent.parent_action scope frame starts covers literal
  let axes := RuntimeNamedFrameAxes.mixedAxes scope
  have disjoint : (forestAxes scope.interval.before.quantum.frame spectators).Disjoint axes := by
    change (forestAxes scope.interval.before.quantum.frame spectators).Disjoint (RuntimeNamedFrameAxes.mixedAxes scope)
    rw [(RuntimeNamedFrameAxes.mixed_bound_axes scope boundary).2.2]
    exact RuntimeNamedBlockSpectators.partition_axes_disjoint checked scope.interval.history.1
      chosen spectators inputOrder
  have unique := (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1
  have inside : child.bindings.flatMap (·.port.wires) ⊆ frame.interval.after.quantum.frame := by
    intro wire member
    obtain ⟨b,returnedMember,wireMember⟩ := List.mem_flatMap.mp member
    have live := codes.owners.transport.after.complete.mem_iff.mp (List.mem_map_of_mem (returned.subset returnedMember))
    exact (Raw.Ownership.valid _ frame.interval.history.2.2.1).covered wire
      (List.mem_flatMap.mpr ⟨b.port,live,wireMember⟩)
  refine ⟨sameLogical,output,table,?_⟩
  intro Reference joint physical reference
  let localRow := gather physical axes
  let low := (product chosen).labels.length
  let high := (product spectators).labels.length
  let canonical : Nat → Reference → ℂ := fun index ref =>
    joint (recode (chosen++spectators) checked.bindings (sourceDimension checked.bindings) index) ref
  let coeff := coefficient spectators scope.interval.before.quantum.frame physical
  let run := @sourceAction _ _ _ _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ codes layouts literal table Reference
  have point := actionLaw joint physical localRow reference
  have restored := RuntimeScatterTransport.scatter_gather physical axes unique
  rw [restored] at point
  have sourceFibre :
      RuntimeNamedSelectionAction.sourceSlice axes physical
        (fun digit environment ref =>
          fibre low high (coefficient spectators scope.interval.before.quantum.frame environment)
            canonical digit ref) =
      fibre low high coeff canonical := by
    funext digit ref
    unfold RuntimeNamedSelectionAction.sourceSlice fibre
    simp only [coefficient_scatter spectators _ _ disjoint]
    rfl
  change _ = RuntimeMultiwayAction.finiteReferenceAction literal.outputCode (run _) localRow reference at point
  rw [sourceFibre,onFinite_reference] at point
  have transported := regrouped_output childFrame childReturned orderedOutput returned.symm
    (bindings_unique codes.owners.transport.after) carriers frame.interval.after.quantum.frame
    scope.interval.after.quantum.frame axes geometry.2.2 unique inside
    (fun digit high ref => onFinite (run (fun input ref => canonical (input+low*high) ref)) digit ref)
    physical localRow reference
  rw [restored,ofNative_action] at transported
  have outputPoint := regroup_action orderedOutput output outputOrder
    (outputOrder.symm.nodup (bindings_unique boundary.afterFrame)) scope.interval.after.quantum.frame
    (blockJoint (product boundary.mapped).labels.length
      (fun digit high ref => onFinite (run (fun input ref => canonical (input+low*high) ref))
        (recode child.bindings codes.owners.transport.after.bindings
          (sourceDimension codes.owners.transport.after.bindings) digit) ref))
    physical reference
  refine point.trans ?_
  refine Eq.trans ?_ (transported.symm.trans outputPoint)
  apply congrArg (fun family => referenceAction literal.outputCode family localRow reference)
  funext digit ref
  rw [geometry.1]
  unfold run sourceAction
  exact ordinal_fibre _ _ _ _ _ _ canonical low high coeff digit ref

private def SelectionWholeOutput
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) (events : List Semantics.Raw.Event) : Prop :=
  match stored with
  | .selection (frame := frame) (codes := codes) (layouts := layouts) (equations := equations) literal _ =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked.bindings),
      checked.bindings = before.bindings →
      CallWholeOutput scope boundary frame codes layouts equations literal events checked parent

def OccurrenceWholeOutput {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (occurrence : @RuntimeNamedThreeOccurrence.Middle dependencies program block step)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness occurrence)
    (events : List Semantics.Raw.Event) : Prop :=
  match occurrence,held with
  | .named (scope := scope) (boundary := boundary) _ _,held =>
    SelectionWholeOutput scope boundary held.literal events

/-- Reassemble the actual named selection at its original caller output.
The child run fixes the source input and return order, while the indexed
Literal fixes the selected action, owner codes and the event slice. -/
theorem actual_occurrence_whole_output {artifact root execution fuel program block step rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness root.dependencies rootItem rootCount}
    (occurrence : @RuntimeNamedThreeOccurrence.Middle root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness occurrence)
    (coverage : RuntimeNamedSelectionOn.Coverage occurrence held)
    (events : List Semantics.Raw.Event) (on : RuntimeNamedSelectionOn.On events occurrence held) :
    OccurrenceWholeOutput occurrence held events := by
  have input := Qleisli.RuntimeSparseSelectionAction.actual_occurrence_source_action occurrence call held coverage events on
  have order := actual_occurrence_return_order occurrence call held coverage
  cases occurrence with
  | @named start count inputs sources caller before childHistory childRetired ordinary event scope body read boundary finalOrdinary node selected =>
    change SelectionWholeOutput scope boundary held.literal events
    dsimp only [RuntimeNamedSelectionOn.Coverage] at coverage
    dsimp only [Qleisli.RuntimeSparseSelectionAction.OccurrenceAction] at input
    dsimp only [OccurrenceReturnOrder] at order
    cases stored : held.literal with
    | @selection first size localInputs outputs selector target frame selectorBits targetBits retained restricted
        inputCode outputCode labels expected logical equations codes layouts literal nativeRead =>
      have bounds : first = 0 ∧ size = ((block.operations.drop start).take count).length := by
        simpa only [stored] using coverage
      rw [stored] at input order
      intro roles checked parent sameBindings
      exact call_whole_output scope boundary frame codes layouts equations literal events checked parent
        sameBindings bounds.1 bounds.2 order.1 (input checked parent sameBindings)

#print axioms regrouped_output
#print axioms call_whole_output
#print axioms actual_occurrence_whole_output
end Qleisli.RuntimeSparseSelectionOutput
