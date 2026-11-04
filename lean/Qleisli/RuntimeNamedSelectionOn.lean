import Qleisli.RuntimeNamedSelectionAction
import Qleisli.RuntimeAdjacentAction
import QleisliKernel.Qirf.RuntimeNamedThreeOccurrence

/-! The original named selection acts on the event list returned by its
enclosing parent fold. Its source table and code maps belong to the same
literal that the original body traversal retained.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedSelectionOn
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open RuntimeNamedThreeOccurrence (Middle RetainedData)
open RuntimeAdjacentSlices (Span Fold)
open RuntimeForestCode Qleisli.RuntimeForestProduct Qleisli.RuntimeMultiwayGram

abbrev Event := Semantics.Raw.Event

private def SelectionCoverage {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) : Prop :=
  match stored with
  | .selection (start := first) (count := size) _ _ =>
    first = 0 ∧ size = ((block.operations.drop start).take count).length

/-- Only whole-local-slice start/length data is required. The selected source
node, scope, codes and literal are already the retained actual values. -/
def Coverage {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (occurrence : @Middle dependencies program block step) (held : RetainedData witness occurrence) : Prop :=
  match occurrence,held with
  | .named (scope := scope) _ _,held => SelectionCoverage scope held.literal

private def selectionOps {dependencies program block node}
    (stored : @RuntimeSelectionWitness.Checked dependencies program block node) : List Semantics.Raw.Op :=
  match stored with
  | .selection (frame := frame) _ _ => frame.operations

private theorem selection_literal {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) (coverage : SelectionCoverage scope stored) :
    (block.operations.drop start).take count = (selectionOps stored).map Semantics.Observation.Op.pure := by
  cases stored with
  | @selection first size _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    calc
      _ = (((block.operations.drop start).take count).drop first).take size := by
        rw [coverage.1,List.drop_zero,coverage.2,List.take_length]
      _ = _ := frame.literal

private def selectionSpan {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) (coverage : SelectionCoverage scope stored) : Span block :=
  ⟨start,count,scope.interval,selectionOps stored,selection_literal scope stored coverage⟩

/-- Read the full parent slice of the retained selection. -/
def middle {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (occurrence : @Middle dependencies program block step) (held : RetainedData witness occurrence)
    (coverage : Coverage occurrence held) : Span block :=
  match occurrence,held with
  | .named (scope := scope) _ _,held => selectionSpan scope held.literal coverage

/-- Exactly the source law of the actual retained local selection, evaluated
on the specified parent events with all spectator/reference correlations. -/
def SourceOn {dependencies program block callStart callCount callInputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount callInputs ordinary effect)
    {start count inputs outputs selector target}
    (frame : RuntimePureInterval.Checked scope.prepared.block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (_equations : RuntimeInterval.Computed (NominalSector.checkLogicals
      inputCode outputCode retained.sectors labels expected) logical)
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after) (parentEvents : List Event) : Prop :=
  logical = expected ∧ ∃ table : OrdinalTable inputCode outputCode retained.sectors labels expected,
    ∀ {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (base physical : Nat) (reference : Reference),
      Qleisli.Semantics.RawAction.events dependencies parentEvents
        (fun input => RuntimeNamedSelectionAction.encodedParent literal.inputCode
          (RuntimeNamedFrameAxes.mixedAxes scope) joint input reference)
        (scatter base (RuntimeNamedFrameAxes.mixedAxes scope) physical) =
      Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
        (sourceAction frame codes layouts literal table
          (RuntimeNamedSelectionAction.sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base joint)) physical reference

private def SelectionOn {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) (events : List Event) : Prop :=
  match stored with
  | .selection (frame := frame) (codes := codes) (layouts := layouts) (equations := equations) literal _ =>
    SourceOn scope frame codes layouts equations literal events

def On {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (events : List Event) (occurrence : @Middle dependencies program block step)
    (held : RetainedData witness occurrence) : Prop :=
  match occurrence,held with
  | .named (scope := scope) _ _,held => SelectionOn scope held.literal events

private theorem selection_on_trace {dependencies program block callStart callCount callInputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount callInputs ordinary effect)
    {node : RuntimePureBody.Node dependencies scope.program scope.prepared.block}
    (stored : RuntimeSelectionWitness.Checked node) (coverage : SelectionCoverage scope stored) (events : List Event)
    (trace : RuntimeLocalEvents.trace scope.interval.before.quantum.reference (selectionOps stored) =
      some ⟨scope.interval.after.quantum.reference,events,scope.interval.before.quantum.frame.length⟩) :
    SelectionOn scope stored events := by
  cases stored with
  | @selection first size _inputs _outputs _selector _target frame _selectorBits _targetBits
      _retained _restricted _inputCode _outputCode _labels _expected _logical equations codes layouts literal sourceRead =>
    simp only [selectionOps] at trace
    obtain ⟨actual,actualTrace,law⟩ := RuntimeNamedSelectionAction.selection_reference_action
      scope frame codes layouts equations literal sourceRead coverage.1 coverage.2
    have same : actual = events := congrArg Semantics.RawTrace.Prepared.events
      (Option.some.inj (actualTrace.symm.trans trace))
    simpa only [SelectionOn,SourceOn,same] using law

/-- The original parent's trace fixes the event list in the source equation. -/
theorem on_middle {dependencies rootItem rootCount program block step}
    {witness : @RuntimeSelectionSteps.Witness dependencies rootItem rootCount}
    (occurrence : @Middle dependencies program block step) (held : RetainedData witness occurrence)
    (coverage : Coverage occurrence held) (events : List Event)
    (trace : RuntimeLocalEvents.trace (middle occurrence held coverage).slice.interval.before.quantum.reference
      (middle occurrence held coverage).slice.ops = some ⟨(middle occurrence held coverage).slice.interval.after.quantum.reference,
        events,(middle occurrence held coverage).slice.interval.before.quantum.frame.length⟩) :
    On events occurrence held := by
  cases occurrence with
  | @named _ _ _ _ _ _ _ _ _ _ scope _ _ _ _ _ _ =>
    exact selection_on_trace scope held.literal coverage events trace

#print axioms on_middle
end Qleisli.RuntimeNamedSelectionOn
