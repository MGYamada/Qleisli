import Qleisli.RuntimeNamedSelectionOutputCodes

/-! Compose the retained selection action with the full caller output encoding.
The source arm acts on each spectator coordinate with arbitrary reference
correlations, and the original owner maps determine both coordinate orders.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSelectionWholeOutput
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (gather scatter)
open RuntimeOwnerMap (Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.RuntimeForestOrderedProduct Qleisli.RuntimeForestRegroup
open Qleisli.RuntimeNamedBlockEncoding Qleisli.RuntimeNamedHeadCoefficients
open Qleisli.RuntimeMultiwayGram Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct

noncomputable def onFinite {Reference : Type} {size : Nat}
    (joint : Fin size → Reference → ℂ) (logical : Nat) (ref : Reference) : ℂ :=
  if bound : logical < size then joint ⟨logical,bound⟩ ref else 0

/-- The arm and the target coordinate are fixed by the actual output index.
Only the joint input is summed over the original spectator coordinates. -/
theorem ordinal_fibre {roles state checked labels arms inputCode outputCode sectors}
    (code : @Frame roles state checked) (selector target : RuntimeOwnerMap.Binding)
    (member : selector ∈ checked.bindings)
    (table : OrdinalTable inputCode outputCode sectors labels arms)
    (card : dimensionAt code.owners selector = labels.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) (low high : Nat)
    (coefficient : Nat → ℂ) (logical : Nat) (reference : Reference) :
    onFinite (ordinalAction code selector target member table card
      (fibre low high coefficient joint)) logical reference =
    ((List.range high).map fun spectator =>
      coefficient spectator * onFinite (ordinalAction code selector target member table card
        (fun digit ref => joint (digit+low*spectator) ref)) logical reference).sum := by
  unfold onFinite
  split
  next bound =>
    simp only [ordinalAction,action,fibre]
    let arm := table.arm (selectorIndex code selector member card ⟨logical,bound⟩)
    let row := Qleisli.MixedRadix.decode checked.bindings (dimensionAt code.owners) logical target
    let input := RuntimeTargetDigit.update code target logical
    change ((List.range arm.cols).map fun col =>
      entry arm row col * ((List.range high).map fun spectator =>
        coefficient spectator * joint (input col+low*spectator) reference).sum).sum =
      ((List.range high).map fun spectator => coefficient spectator *
        ((List.range arm.cols).map fun col =>
          entry arm row col * joint (input col+low*spectator) reference).sum).sum
    symm
    calc
      _ = ((List.range high).map fun spectator =>
        ((List.range arm.cols).map fun col =>
          coefficient spectator * (entry arm row col * joint (input col+low*spectator) reference)).sum).sum := by
        apply Qleisli.Exact.sum_map_congr
        intro spectator _
        rw [List.sum_map_mul_left]
      _ = ((List.range arm.cols).map fun col =>
        ((List.range high).map fun spectator =>
          coefficient spectator * (entry arm row col * joint (input col+low*spectator) reference)).sum).sum :=
        Qleisli.Exact.sum_swap _ _ _
      _ = _ := by
        simp only [mul_left_comm (coefficient _) (entry arm _ _),List.sum_map_mul_left]
  next _ => simp

theorem onFinite_reference {roles state checked} (frame : @Frame roles state checked)
    {Reference : Type} (joint : Fin frame.code.dimension → Reference → ℂ)
    (physical : Nat) (reference : Reference) :
    RuntimeMultiwayAction.finiteReferenceAction frame joint physical reference =
      referenceAction frame (onFinite joint) physical reference := by
  rw [← RuntimeMultiwayAction.finiteReferenceAction_of_nat]
  congr 1
  funext index ref
  simp only [onFinite,dif_pos index.isLt,Fin.eta]

noncomputable def blockJoint {roles state checked} (frame : @Frame roles state checked)
    (order : Map) (low : Nat) {Reference : Type} (joint : Nat → Nat → Reference → ℂ)
    (logical : Nat) (reference : Reference) : ℂ :=
  let index := regroupIndex frame order logical
  joint (index%low) (index/low) reference

theorem blockJoint_recode {roles state checked} (frame : @Frame roles state checked)
    (selected spectators : Map) (left : OwnerCodes selected) (right : OwnerCodes spectators)
    (kept : reindex frame.owners (selected++spectators) = some (append left right))
    (order : (selected++spectators).Perm checked.bindings)
    {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (digit high : Nat)
    (digitBound : digit < (sparseProduct left).dimension)
    (highBound : high < (sparseProduct right).dimension) (reference : Reference) :
    blockJoint frame (selected++spectators) (sparseProduct left).dimension joint
      (Qleisli.MixedRadix.recode (selected++spectators) checked.bindings (dimensionAt frame.owners)
        (digit+(sparseProduct left).dimension*high)) reference = joint digit high reference := by
  let low := (sparseProduct left).dimension
  have positive : 0 < low := dimension_positive left
  have bound : digit+low*high < (sparseProduct (append left right)).dimension := by
    rw [dimension_append]
    calc
      digit+low*high < low+low*high := Nat.add_lt_add_right digitBound _
      _ = low*(high+1) := by rw [Nat.mul_succ,Nat.add_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ highBound
  unfold blockJoint
  rw [regroup_reverse frame _ ⟨append left right,kept⟩ order _ bound]
  change joint ((digit+low*high)%low) ((digit+low*high)/low) reference = _
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt digitBound,
    Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt digitBound,Nat.zero_add]

/-- Output owner reindexing acts on the finite child output, including every
spectator coefficient in the actual caller output frame. -/
theorem regrouped_block_action {childRoles childState childChecked roles state checked}
    (child : @Frame childRoles childState childChecked) (frame : @Frame roles state checked)
    (returned selected spectators : Map)
    (returnedCodes : OwnerCodes returned) (left : OwnerCodes selected) (right : OwnerCodes spectators)
    (childKept : reindex child.owners returned = some returnedCodes)
    (kept : reindex frame.owners (selected++spectators) = some (append left right))
    (childOrder : returned.Perm childChecked.bindings)
    (order : (selected++spectators).Perm checked.bindings)
    (dimension : (sparseProduct left).dimension = (sparseProduct returnedCodes).dimension)
    {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (physical localPhysical : Nat)
    (same : ∀ digit < (sparseProduct returnedCodes).dimension,
      coefficients state.quantum.frame left physical digit =
        coefficients childState.quantum.frame returnedCodes localPhysical digit)
    (reference : Reference) :
    referenceAction frame
      (blockJoint frame (selected++spectators) (sparseProduct left).dimension
        (fun digit high ref => joint
          (Qleisli.MixedRadix.recode returned childChecked.bindings (dimensionAt child.owners) digit)
          high ref)) physical reference =
    referenceAction child
      (fun digit ref => ((List.range (sparseProduct right).dimension).map fun high =>
        coefficients state.quantum.frame right physical high * joint digit high ref).sum)
      localPhysical reference := by
  rw [frame_block_encoding frame selected spectators left right kept order,
    RuntimeNamedOutputOrder.regroup_dense_action child returned ⟨returnedCodes,childKept⟩ childOrder]
  change ((List.range (sparseProduct left).dimension).map _).sum =
    ((List.range (sparseProduct returnedCodes).dimension).map _).sum
  conv_rhs => rw [← dimension]
  apply Qleisli.Exact.sum_map_congr
  intro digit present
  have digitBound := List.mem_range.mp present
  rw [same digit (dimension ▸ digitBound)]
  congr 1
  unfold fibre
  apply Qleisli.Exact.sum_map_congr
  intro high presentHigh
  exact congrArg (coefficients state.quantum.frame right physical high * ·)
    (blockJoint_recode frame selected spectators left right kept order
      (fun digit high ref => joint
        (Qleisli.MixedRadix.recode returned childChecked.bindings (dimensionAt child.owners) digit)
        high ref) digit high digitBound (List.mem_range.mp presentHigh) reference)

#print axioms ordinal_fibre
#print axioms blockJoint_recode
#print axioms regrouped_block_action

/-- Apply the original child source action separately to each caller spectator
coordinate, then assemble the original returned owners in caller order. -/
noncomputable def callerUpdate {inputRoles inputState inputChecked childRoles childState childChecked
    outputRoles outputState outputChecked}
    (input : @Frame inputRoles inputState inputChecked)
    (child : @Frame childRoles childState childChecked)
    (output : @Frame outputRoles outputState outputChecked)
    (inputOrder returnOrder outputOrder : Map) (inputLow outputLow : Nat)
    {Reference : Type}
    (run : (Nat → Reference → ℂ) → Fin child.code.dimension → Reference → ℂ)
    (joint : Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  blockJoint output outputOrder outputLow (fun digit high ref =>
    onFinite (run (fun localDigit localRef => joint
      (Qleisli.MixedRadix.recode inputOrder inputChecked.bindings (dimensionAt input.owners)
        (localDigit+inputLow*high)) localRef))
      (Qleisli.MixedRadix.recode returnOrder childChecked.bindings (dimensionAt child.owners) digit) ref)

open RuntimeNamedSelectionInputEncoding
open RuntimeNamedSelectionOutputCodes
open RuntimeNamedSelectionReturnOrder

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
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked)
    (output : Frame boundary.afterFrame) : Prop :=
  logical = expected ∧
  let selected := boundary.input.ordered
  let spectators := RuntimeSelectionPartition.complement checked.bindings selected
  ∃ inputCodes : OwnerCodes selected, ∃ beforeCodes : OwnerCodes spectators,
    reindex parent.owners (selected++spectators) = some (append inputCodes beforeCodes) ∧
    ∃ mappedCodes : OwnerCodes boundary.mapped, ∃ afterCodes : OwnerCodes spectators,
      reindex output.owners (boundary.mapped++spectators) = some (append mappedCodes afterCodes) ∧
      ∃ table : OrdinalTable inputCode outputCode retained.sectors labels expected,
        ∀ {Reference : Type} (joint : Nat → Reference → ℂ) physical reference,
          Qleisli.Semantics.RawAction.events dependencies events
              (fun row => referenceAction parent joint row reference) physical =
            referenceAction output
              (callerUpdate parent literal.outputCode output (selected++spectators) child.bindings
                (boundary.mapped++spectators) (sparseProduct inputCodes).dimension
                (sparseProduct mappedCodes).dimension (sourceAction frame codes layouts literal table) joint)
              physical reference

/-- Identify the whole caller output on every row using the same source table
and authentic output codes. The spectator and reference coordinates remain
independent of the output owner permutation. -/
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
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked)
    (output : Frame boundary.afterFrame) (sameBindings : checked.bindings = before.bindings)
    (starts : first = 0) (covers : size = ((block.operations.drop callStart).take callCount).length)
    (returned : child.bindings.Perm codes.owners.transport.after.bindings)
    (inputLaw : CallSourceAction scope boundary frame codes layouts equations literal events checked parent) :
    CallWholeOutput scope boundary frame codes layouts equations literal events checked parent output := by
  let chosen := boundary.input.ordered
  let spectators := RuntimeSelectionPartition.complement checked.bindings chosen
  have afterOrder := (caller_after_order scope boundary checked sameBindings).2
  obtain ⟨returnedCodes,returnedRead,mappedCodes,afterCodes,outputRead,dimension,outputCoefficient⟩ :=
    call_output_codes scope boundary frame starts covers literal returned output spectators afterOrder
  obtain ⟨sameLogical,inputCodes,beforeCodes,inputRead,table,actionLaw⟩ := inputLaw
  obtain ⟨_input,_spectator,_read,permutation⟩ :=
    original_named_partition scope boundary checked parent sameBindings
  obtain ⟨_events,_trace,_action,geometry⟩ := RuntimeNamedSelectionParent.parent_action scope frame starts covers literal
  have spectra := RuntimeNamedCallerGeometry.codes_same rfl beforeCodes afterCodes _ _ geometry.1
  let axes := RuntimeNamedFrameAxes.mixedAxes scope
  have disjoint : (forestAxes scope.interval.before.quantum.frame spectators).Disjoint axes := by
    change (forestAxes scope.interval.before.quantum.frame spectators).Disjoint (RuntimeNamedFrameAxes.mixedAxes scope)
    rw [(RuntimeNamedFrameAxes.mixed_bound_axes scope boundary).2.2]
    exact RuntimeNamedBlockSpectators.partition_axes_disjoint checked scope.interval.history.1
      chosen spectators permutation
  have unique := (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1
  refine ⟨sameLogical,inputCodes,beforeCodes,inputRead,mappedCodes,afterCodes,outputRead,table,?_⟩
  intro Reference joint physical reference
  let localRow := gather physical axes
  let canonical : Nat → Reference → ℂ := fun index ref =>
    joint (Qleisli.MixedRadix.recode (chosen++spectators) checked.bindings (dimensionAt parent.owners) index) ref
  let coeff := fun high => coefficients scope.interval.before.quantum.frame beforeCodes physical high
  let run := @sourceAction _ _ _ _ _ _ _ _ _ frame _ _ _ _ _ _ _ _ codes layouts literal table Reference
  have point := actionLaw joint physical localRow reference
  rw [RuntimeScatterTransport.scatter_gather physical axes unique] at point
  have sourceFibre :
      RuntimeNamedSelectionAction.sourceSlice axes physical
        (fun digit environment ref =>
          fibre (sparseProduct inputCodes).dimension (sparseProduct beforeCodes).dimension
            (fun high => coefficients scope.interval.before.quantum.frame beforeCodes environment high)
            canonical digit ref) =
      fibre (sparseProduct inputCodes).dimension (sparseProduct beforeCodes).dimension coeff canonical := by
    funext digit ref
    unfold RuntimeNamedSelectionAction.sourceSlice fibre
    apply Qleisli.Exact.sum_map_congr
    intro high _
    exact congrArg (fun c => c * canonical (digit+(sparseProduct inputCodes).dimension*high) ref)
      (RuntimeNamedBlockSpectators.coefficients_scatter _ beforeCodes _ disjoint physical 0 high)
  change _ = RuntimeMultiwayAction.finiteReferenceAction literal.outputCode (run _) localRow reference at point
  rw [sourceFibre,onFinite_reference] at point
  have outputPoint := regrouped_block_action literal.outputCode output child.bindings boundary.mapped
    spectators returnedCodes mappedCodes afterCodes returnedRead outputRead returned afterOrder dimension
    (fun digit high ref =>
      onFinite (run (fun input ref => canonical (input+(sparseProduct inputCodes).dimension*high) ref)) digit ref)
    physical localRow
    (fun digit bound => by
      have coefficient := outputCoefficient physical localRow digit bound
      rw [RuntimeScatterTransport.scatter_gather physical axes unique] at coefficient
      exact coefficient) reference
  refine point.trans ?_
  refine Eq.trans ?_ outputPoint.symm
  apply congrArg (fun family => referenceAction literal.outputCode family localRow reference)
  funext digit ref
  rw [← spectra.1]
  simp only [← spectra.2 physical]
  unfold run sourceAction
  exact ordinal_fibre _ _ _ _ _ _ canonical _ _ coeff digit ref

#print axioms call_whole_output

private def SelectionWholeOutput
    {dependencies program block callStart callCount inputs ordinary effect sources caller before child retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired value)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) (events : List Semantics.Raw.Event) : Prop :=
  match stored with
  | .selection (frame := frame) (codes := codes) (layouts := layouts) (equations := equations) literal _ =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked),
      checked.bindings = before.bindings →
      ∀ output : Frame boundary.afterFrame,
        CallWholeOutput scope boundary frame codes layouts equations literal events checked parent output

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
  have input := actual_occurrence_source_action occurrence call held coverage events on
  have order := actual_occurrence_return_order occurrence call held coverage
  cases occurrence with
  | @named start count inputs sources caller before childHistory childRetired ordinary event scope body read boundary finalOrdinary node selected =>
    change SelectionWholeOutput scope boundary held.literal events
    dsimp only [RuntimeNamedSelectionOn.Coverage] at coverage
    dsimp only [OccurrenceAction] at input
    dsimp only [OccurrenceReturnOrder] at order
    cases stored : held.literal with
    | @selection first size localInputs outputs selector target frame selectorBits targetBits retained restricted
        inputCode outputCode labels expected logical equations codes layouts literal nativeRead =>
      have bounds : first = 0 ∧ size = ((block.operations.drop start).take count).length := by
        simpa only [stored] using coverage
      rw [stored] at input order
      intro roles checked parent sameBindings output
      exact call_whole_output scope boundary frame codes layouts equations literal events checked parent
        output sameBindings bounds.1 bounds.2 order.1 (input checked parent sameBindings)

#print axioms actual_occurrence_whole_output
end Qleisli.RuntimeNamedSelectionWholeOutput
