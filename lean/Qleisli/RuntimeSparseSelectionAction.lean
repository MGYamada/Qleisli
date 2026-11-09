import Qleisli.RuntimeSparseBlockEncoding
import Qleisli.RuntimeNamedSelectionInputEncoding

/-! The literal named qmatch acts on the complete independent sparse caller
input. Its original checked child output code and exact selector table are
retained on each arbitrary correlated spectator/reference fibre.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSparseSelectionAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact (Matrix)
open RuntimeForestCode (carrierOwners)
open Qleisli.RuntimeSemanticForest (Frame action product)
open Qleisli.RuntimeSparseBlockEncoding (coefficient caller_input)
open Qleisli.RuntimeNamedBlockEncoding (original_named_partition_geometry)
open Qleisli.RuntimeNamedCarrierEncoding (original_selection_input_geometry)
open Qleisli.RuntimeNamedHeadCoefficients (fibre)
open Qleisli.RuntimeForestRegroup (sourceDimension)

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
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked.bindings) : Prop :=
    logical = expected ∧
    let chosen := boundary.input.ordered
    let spectators := RuntimeSelectionPartition.complement checked.bindings chosen
    ∃ table : Qleisli.RuntimeMultiwayGram.OrdinalTable inputCode outputCode retained.sectors labels expected,
        ∀ {Reference : Type} (joint : Nat → Reference → Complex) base physical reference,
          Qleisli.Semantics.RawAction.events dependencies events
            (fun value => action parent scope.interval.before.quantum.frame joint value reference)
            (QleisliKernel.Semantics.Finite.scatter base (RuntimeNamedFrameAxes.mixedAxes scope) physical) =
          Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
            (Qleisli.RuntimeMultiwayGram.sourceAction selected codes layouts literal table
              (RuntimeNamedSelectionAction.sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base
                (fun digit environment ref =>
                  fibre (product chosen).labels.length (product spectators).labels.length
                    (fun high => coefficient spectators scope.interval.before.quantum.frame environment high)
                    (fun logical ref => joint (Qleisli.MixedRadix.recode (chosen++spectators)
                      checked.bindings (sourceDimension checked.bindings) logical) ref) digit ref))) physical reference

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
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked.bindings)
    (sameBindings : checked.bindings = before.bindings) :
    CallSourceAction scope boundary selected codes layouts equations literal events checked parent := by
  obtain ⟨sameLogical,table,nativeAction⟩ := on
  refine ⟨sameLogical,table,?_⟩
  obtain ⟨axes,localFrame,unique⟩ := original_selection_input_geometry scope boundary selected starts
  have partition := original_named_partition_geometry scope boundary checked sameBindings
  intro Reference joint base physical reference
  have inputLaw := caller_input checked parent scope.interval.history.1 partition literal.inputCode same localFrame unique joint
  rw [axes] at inputLaw
  have sameInputs := funext (fun value => inputLaw value reference)
  rw [sameInputs]
  exact nativeAction _ base physical reference

private def SelectionAction
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) (events : List Semantics.Raw.Event) : Prop :=
  match stored with
  | .selection (frame := frame) (codes := codes) (layouts := layouts) (equations := equations) literal _ =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (parent : Frame checked.bindings),
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

#print axioms original_call_source_action
#print axioms actual_occurrence_source_action
end Qleisli.RuntimeSparseSelectionAction
