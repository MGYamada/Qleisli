import Qleisli.RuntimeNamedBlockEncoding
import Qleisli.RuntimeNamedCarrierEncoding
import Qleisli.RuntimeNamedBlockSpectators

/-! Connect the actual named selection to its complete caller input encoding.
The same original child, indexed Literal and parent Raw events carry arbitrary
correlated spectators/references. Output caller encoding and whole-body/instrument
composition remain separate obligations. No acceptance or work limit changes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSelectionInputEncoding
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (gather)
open RuntimeOwnerMap (Map Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.RuntimeForestOrderedProduct
open Qleisli.RuntimeNamedHeadCoefficients Qleisli.RuntimeNamedBlockEncoding
open Qleisli.RuntimeNamedCarrierEncoding

/-- This actual named selection's full caller input equals its child code
applied to the complete correlated spectator/reference fibre. All source
carriers, ordered axes and the one original parent map remain attached. -/
theorem original_call_input_encoding
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {first size localInputs outputs selector target}
    (selected : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    (source : RuntimeOwnerTransition.Selection selected.interval localInputs outputs [selector,target])
    (starts : first = 0)
    (same : carrierOwners source.before.bindings = carrierOwners boundary.input.ordered)
    (child : Frame source.before)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked)
    (sameBindings : checked.bindings = before.bindings) :
    let chosen := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings chosen
    ∃ selectedCodes : OwnerCodes chosen, ∃ spectatorCodes : OwnerCodes spectators,
      reindex parent.owners (chosen++spectators) = some (append selectedCodes spectatorCodes) ∧
      ∀ {Reference : Type} (joint : Nat → Reference → Complex) physical reference,
        referenceAction parent joint physical reference =
          referenceAction child
            (fibre (sparseProduct selectedCodes).dimension (sparseProduct spectatorCodes).dimension
              (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes physical high)
              (fun logical ref => joint (Qleisli.MixedRadix.recode (chosen++spectators)
                checked.bindings (dimensionAt parent.owners) logical) ref))
            (gather physical (RuntimeNamedFrameAxes.mixedAxes scope)) reference := by
  intro chosen spectators
  obtain ⟨selectedCodes,spectatorCodes,kept,permutation⟩ :=
    original_named_partition scope boundary checked parent sameBindings
  refine ⟨selectedCodes,spectatorCodes,kept,?_⟩
  intro Reference joint physical reference
  have whole := frame_block_encoding parent chosen spectators selectedCodes spectatorCodes
    kept permutation joint physical reference
  have childAction := original_selection_input_action scope boundary selected source starts same child selectedCodes
    (fibre (sparseProduct selectedCodes).dimension (sparseProduct spectatorCodes).dimension
      (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes physical high)
      (fun logical ref => joint (Qleisli.MixedRadix.recode (chosen++spectators)
        checked.bindings (dimensionAt parent.owners) logical) ref)) physical reference
  exact whole.trans childAction.symm

#print axioms original_call_input_encoding
def CallInputEncoding
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {childRoles childState childChecked} (child : @Frame childRoles childState childChecked) : Prop :=
  ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked),
    checked.bindings = before.bindings →
    let chosen := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings chosen
    ∃ selectedCodes : OwnerCodes chosen, ∃ spectatorCodes : OwnerCodes spectators,
      reindex parent.owners (chosen++spectators) = some (append selectedCodes spectatorCodes) ∧
      ∀ {Reference : Type} (joint : Nat → Reference → Complex) physical reference,
        referenceAction parent joint physical reference =
          referenceAction child
            (fibre (sparseProduct selectedCodes).dimension (sparseProduct spectatorCodes).dimension
              (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes physical high)
              (fun logical ref => joint (Qleisli.MixedRadix.recode (chosen++spectators)
                checked.bindings (dimensionAt parent.owners) logical) ref))
            (gather physical (RuntimeNamedFrameAxes.mixedAxes scope)) reference

private def SelectionEncoding
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) : Prop :=
  match stored with
  | .selection literal _ => CallInputEncoding scope boundary literal.inputCode

def OccurrenceEncoding {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (occurrence : @RuntimeNamedThreeOccurrence.Middle dependencies program block step)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness occurrence) : Prop :=
  match occurrence,held with
  | .named (scope := scope) (boundary := boundary) _ _,held =>
    SelectionEncoding scope boundary held.literal

/-- The same actual middle occurrence supplies the source carrier equality;
its retained indexed Literal fixes the child code and all native selection
fields. No caller-supplied carrier/code/matrix equality remains in this consumer. -/
theorem actual_occurrence_input_encoding {artifact root execution fuel program block step rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness root.dependencies rootItem rootCount}
    (occurrence : @RuntimeNamedThreeOccurrence.Middle root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness occurrence)
    (coverage : RuntimeNamedSelectionOn.Coverage occurrence held) :
    OccurrenceEncoding occurrence held := by
  have input := RuntimeNamedSelectionInputs.actual_occurrence_source occurrence call
  cases occurrence with
  | @named start count inputs sources caller before childHistory childRetired ordinary event scope body read boundary finalOrdinary node selected =>
    change SelectionEncoding scope boundary held.literal
    dsimp only [RuntimeNamedSelectionOn.Coverage] at coverage
    cases stored : held.literal with
    | @selection first size localInputs outputs selector target frame selectorBits targetBits retained restricted
        inputCode outputCode labels expected logical equations codes layouts literal nativeRead =>
      have bounds : first = 0 ∧ size = ((block.operations.drop start).take count).length := by
        simpa only [stored] using coverage
      intro roles checked parent sameBindings
      exact original_call_input_encoding scope boundary frame codes.owners bounds.1 input.1
        literal.inputCode checked parent sameBindings

#print axioms actual_occurrence_input_encoding

/-- The authentic original body traversal supplies the exact child run and
indexed Literal for this pre/choose/post middle call. Whole-body logical
composition and public capability coverage remain separate obligations. -/
theorem original_middle_input_encoding {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_body_middle body view)) :
    OccurrenceEncoding view.centerSelection (RuntimeNamedThreeOccurrence.actual_body_middle body view) :=
  actual_occurrence_input_encoding view.centerSelection
    (RuntimeNamedSourceFlow.original_child_runs body view).2.1
    (RuntimeNamedThreeOccurrence.actual_body_middle body view) coverage

#print axioms original_middle_input_encoding

/-- Express the actual whole caller input in exactly the encodedParent
form consumed by the original parent-event selection law. Clearing the selected
axes changes no spectator coefficient, including any reference correlations. -/
theorem original_call_encoded_parent
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {first size localInputs outputs selector target}
    (selected : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    (source : RuntimeOwnerTransition.Selection selected.interval localInputs outputs [selector,target])
    (starts : first = 0)
    (same : carrierOwners source.before.bindings = carrierOwners boundary.input.ordered)
    (child : Frame source.before)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked)
    (sameBindings : checked.bindings = before.bindings) :
    let chosen := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings chosen
    ∃ selectedCodes : OwnerCodes chosen, ∃ spectatorCodes : OwnerCodes spectators,
      reindex parent.owners (chosen++spectators) = some (append selectedCodes spectatorCodes) ∧
      ∀ {Reference : Type} (joint : Nat → Reference → Complex) physical reference,
        referenceAction parent joint physical reference =
          RuntimeNamedSelectionAction.encodedParent child (RuntimeNamedFrameAxes.mixedAxes scope)
            (fun digit environment ref =>
              fibre (sparseProduct selectedCodes).dimension (sparseProduct spectatorCodes).dimension
                (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes environment high)
                (fun logical ref => joint (Qleisli.MixedRadix.recode (chosen++spectators)
                  checked.bindings (dimensionAt parent.owners) logical) ref) digit ref) physical reference := by
  intro chosen spectators
  obtain ⟨selectedCodes,spectatorCodes,kept,law⟩ := original_call_input_encoding
    scope boundary selected source starts same child checked parent sameBindings
  obtain ⟨_chosen,_spectators,_kept,permutation⟩ :=
    original_named_partition scope boundary checked parent sameBindings
  have disjoint : (forestAxes scope.interval.before.quantum.frame spectators).Disjoint
      (RuntimeNamedFrameAxes.mixedAxes scope) := by
    rw [(RuntimeNamedFrameAxes.mixed_bound_axes scope boundary).2.2]
    exact RuntimeNamedBlockSpectators.partition_axes_disjoint checked scope.interval.history.1
      chosen spectators permutation
  refine ⟨selectedCodes,spectatorCodes,kept,?_⟩
  intro Reference joint physical reference
  have unchanged :
      (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes
        (QleisliKernel.Semantics.Finite.scatter physical (RuntimeNamedFrameAxes.mixedAxes scope) 0) high) =
      (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes physical high) := by
    funext high
    exact RuntimeNamedBlockSpectators.coefficients_scatter _ spectatorCodes _ disjoint physical 0 high
  simpa only [RuntimeNamedSelectionAction.encodedParent,referenceAction,unchanged] using law joint physical reference

#print axioms original_call_encoded_parent

/-- Apply the authentic parent-event source law to the complete caller
input, with the actual correlated spectator/reference fibre. The output is
still in the same retained child output code; caller-output reindexing and
whole-source/instrument composition are separate obligations. -/
theorem original_call_source_action
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {first size localInputs outputs selector target}
    (selected : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment selected.selected selected.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes selected.interval localInputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels expected) logical)
    (literal : RuntimeLocalEvents.Literal selected selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (starts : first = 0)
    (same : carrierOwners codes.owners.before.bindings = carrierOwners boundary.input.ordered)
    (events : List Semantics.Raw.Event)
    (on : RuntimeNamedSelectionOn.SourceOn scope selected codes layouts equations literal events)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked)
    (sameBindings : checked.bindings = before.bindings) :
    logical = expected ∧
    let chosen := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings chosen
    ∃ selectedCodes : OwnerCodes chosen, ∃ spectatorCodes : OwnerCodes spectators,
      reindex parent.owners (chosen++spectators) = some (append selectedCodes spectatorCodes) ∧
      ∃ table : Qleisli.RuntimeMultiwayGram.OrdinalTable inputCode outputCode retained.sectors labels expected,
        ∀ {Reference : Type} (joint : Nat → Reference → Complex) base physical reference,
          Qleisli.Semantics.RawAction.events dependencies events
            (fun value => referenceAction parent joint value reference)
            (QleisliKernel.Semantics.Finite.scatter base (RuntimeNamedFrameAxes.mixedAxes scope) physical) =
          Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
            (Qleisli.RuntimeMultiwayGram.sourceAction selected codes layouts literal table
              (RuntimeNamedSelectionAction.sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base
                (fun digit environment ref =>
                  fibre (sparseProduct selectedCodes).dimension (sparseProduct spectatorCodes).dimension
                    (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes environment high)
                    (fun logical ref => joint (Qleisli.MixedRadix.recode (chosen++spectators)
                      checked.bindings (dimensionAt parent.owners) logical) ref) digit ref))) physical reference := by
  obtain ⟨sameLogical,table,nativeAction⟩ := on
  refine ⟨sameLogical,?_⟩
  intro chosen spectators
  obtain ⟨selectedCodes,spectatorCodes,kept,parentLaw⟩ := original_call_encoded_parent
    scope boundary selected codes.owners starts same literal.inputCode checked parent sameBindings
  refine ⟨selectedCodes,spectatorCodes,kept,table,?_⟩
  intro Reference joint base physical reference
  let family : Nat → Nat → Reference → Complex := fun digit environment ref =>
    fibre (sparseProduct selectedCodes).dimension (sparseProduct spectatorCodes).dimension
      (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes environment high)
      (fun logical ref => joint (Qleisli.MixedRadix.recode (chosen++spectators)
        checked.bindings (dimensionAt parent.owners) logical) ref) digit ref
  have inputsEqual : (fun value => referenceAction parent joint value reference) =
      (fun value => RuntimeNamedSelectionAction.encodedParent literal.inputCode
        (RuntimeNamedFrameAxes.mixedAxes scope) family value reference) := by
    funext value
    exact parentLaw joint value reference
  rw [inputsEqual]
  exact nativeAction family base physical reference

#print axioms original_call_source_action

def CallSourceAction
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {first size localInputs outputs selector target}
    (selected : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment selected.selected selected.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes selected.interval localInputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (_equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels expected) logical)
    (literal : RuntimeLocalEvents.Literal selected selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (events : List Semantics.Raw.Event)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked) : Prop :=
    logical = expected ∧
    let chosen := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings chosen
    ∃ selectedCodes : OwnerCodes chosen, ∃ spectatorCodes : OwnerCodes spectators,
      reindex parent.owners (chosen++spectators) = some (append selectedCodes spectatorCodes) ∧
      ∃ table : Qleisli.RuntimeMultiwayGram.OrdinalTable inputCode outputCode retained.sectors labels expected,
        ∀ {Reference : Type} (joint : Nat → Reference → Complex) base physical reference,
          Qleisli.Semantics.RawAction.events dependencies events
            (fun value => referenceAction parent joint value reference)
            (QleisliKernel.Semantics.Finite.scatter base (RuntimeNamedFrameAxes.mixedAxes scope) physical) =
          Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
            (Qleisli.RuntimeMultiwayGram.sourceAction selected codes layouts literal table
              (RuntimeNamedSelectionAction.sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base
                (fun digit environment ref =>
                  fibre (sparseProduct selectedCodes).dimension (sparseProduct spectatorCodes).dimension
                    (fun high => coefficients scope.interval.before.quantum.frame spectatorCodes environment high)
                    (fun logical ref => joint (Qleisli.MixedRadix.recode (chosen++spectators)
                      checked.bindings (dimensionAt parent.owners) logical) ref) digit ref))) physical reference

private def SelectionAction
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) (events : List Semantics.Raw.Event) : Prop :=
  match stored with
  | .selection (frame := frame) (codes := codes) (layouts := layouts) (equations := equations) literal _ =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked),
      checked.bindings = before.bindings →
        CallSourceAction scope boundary frame codes layouts equations literal events checked parent

def OccurrenceAction {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (occurrence : @RuntimeNamedThreeOccurrence.Middle dependencies program block step)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness occurrence) (events : List Semantics.Raw.Event) : Prop :=
  match occurrence,held with
  | .named (scope := scope) (boundary := boundary) _ _,held =>
    SelectionAction scope boundary held.literal events

/-- The same real child, original indexed Literal and actual parent events
supply the complete-input source action. No source carrier, code or matrix
equality is a caller premise. The child output code remains explicit. -/
theorem actual_occurrence_source_action {artifact root execution fuel program block step rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness root.dependencies rootItem rootCount}
    (occurrence : @RuntimeNamedThreeOccurrence.Middle root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (held : RuntimeNamedThreeOccurrence.RetainedData witness occurrence)
    (coverage : RuntimeNamedSelectionOn.Coverage occurrence held)
    (events : List Semantics.Raw.Event) (on : RuntimeNamedSelectionOn.On events occurrence held) :
    OccurrenceAction occurrence held events := by
  have input := RuntimeNamedSelectionInputs.actual_occurrence_source occurrence call
  cases occurrence with
  | @named start count inputs sources caller before childHistory childRetired ordinary event scope body read boundary finalOrdinary node selected =>
    change SelectionAction scope boundary held.literal events
    dsimp only [RuntimeNamedSelectionOn.Coverage] at coverage
    dsimp only [RuntimeNamedSelectionOn.On] at on
    cases stored : held.literal with
    | @selection first size localInputs outputs selector target frame selectorBits targetBits retained restricted
        inputCode outputCode labels expected logical equations codes layouts literal nativeRead =>
      have bounds : first = 0 ∧ size = ((block.operations.drop start).take count).length := by
        simpa only [stored] using coverage
      have native : RuntimeNamedSelectionOn.SourceOn scope frame codes layouts equations literal events := by
        simpa only [stored] using on
      intro roles checked parent sameBindings
      exact original_call_source_action scope boundary frame codes layouts equations literal bounds.1
        input.1 events native checked parent sameBindings

/-- All three actual source calls now have their full-input action laws on
exactly the original root events. The center result remains in its authentic
child output code; matching caller output coefficients and whole-body/general
instrument composition is not asserted by this three-call checkpoint. -/
theorem original_three_input_actions {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_body_middle body view)) :
    let held := RuntimeNamedThreeOccurrence.actual_body_middle body view
    let pre := RuntimeNamedOccurrenceAction.span view.prePrimitive
    let center := RuntimeNamedSelectionOn.middle view.centerSelection held coverage
    let post := RuntimeNamedOccurrenceAction.span view.postPrimitive
    pre.start = 0 → center.start = pre.start+pre.count → post.start = center.start+center.count →
    pre.count+center.count+post.count = body.root.program.operations.length →
    ∃ a b c, RuntimeNamedThreeRoot.Whole body.checked.native pre center post a b c ∧
      RuntimeNamedCallerAction.WholeCallerAction view.prePrimitive a ∧
      OccurrenceAction view.centerSelection held b ∧
      RuntimeNamedCallerAction.WholeCallerAction view.postPrimitive c := by
  intro held pre center post starts next last covers
  obtain ⟨a,b,c,whole,preLaw,on,postLaw⟩ :=
    RuntimeNamedCallerAction.original_pre_post_actions body view coverage starts next last covers
  have calls := RuntimeNamedSourceFlow.original_child_runs body view
  exact ⟨a,b,c,whole,preLaw,
    actual_occurrence_source_action view.centerSelection calls.2.1 held coverage b on,postLaw⟩

#print axioms actual_occurrence_source_action
#print axioms original_three_input_actions

end Qleisli.RuntimeNamedSelectionInputEncoding
