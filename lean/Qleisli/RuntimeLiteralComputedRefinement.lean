import Qleisli.RuntimeLiteralBasisRefinement
import Qleisli.RuntimeComputedCallerAction
import Qleisli.RuntimeCertifiedComputedAction
import Qleisli.RawFiniteRows
import Qleisli.RuntimeIntervalRawFold

/-! The original protected scope contributes its logical phase to the same
literal history. It preserves the ordinary SSA table and hidden outcomes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Step)
open RuntimeOwnerMap (Binding)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.RuntimeNamedChildRuns (OrdinaryAligned)
open Qleisli.Semantics.ObservingAction (History run)
open Semantics.Observation (readOps)
open Qleisli.RuntimeLiteralHistory (pure_history_with_inherited)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)

private noncomputable def computedResult {sources caller dependencies program block start count event prepared interval before}
    (checked : @RuntimeComputedUse.Checked sources caller dependencies program block start count event prepared interval before)
    (source : SourceHistory) : List SourceHistory :=
  let operand : Binding := ⟨event.input,checked.literal.input.port⟩
  [{source with
    owners := RuntimeComputedPredicate.continued event before checked.literal.output
    operator := RuntimeComputedCallerAction.sourceOperator prepared before.bindings operand source.operator}]


private noncomputable def certifiedResult {sources caller dependencies program block start count event prepared interval before}
    (checked : @RuntimeCertifiedComputed.Checked sources caller dependencies program block start count event prepared interval before)
    (source : SourceHistory) : List SourceHistory :=
  let operand : Binding := ⟨event.input,checked.literal.input.port⟩
  [{source with
    owners := RuntimeComputedPredicate.continued event before checked.literal.output
    operator := RuntimeLiteralHistory.applySourceOwner before.bindings before.bindings operand operand
      prepared.logical.matrix source.operator}]

private noncomputable def structuralResult {sources caller dependencies program block start count event interval before}
    (checked : @StructuralComputedRaw.IntervalChecked sources caller dependencies program block start count event interval before)
    (source : SourceHistory) : List SourceHistory :=
  let operand : Binding := ⟨event.input,checked.checked.owner.port⟩
  [{source with
    owners := RuntimeComputedPredicate.continued event before checked.checked.output
    operator := RuntimeComputedCallerAction.structuralSourceOperator checked.checked.matched
      before.bindings operand source.operator}]

noncomputable def withComputed {dependencies program block}
    (other : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.computed _ _ _ checked) => some (computedResult checked source)
  | .pure (.certifiedComputed _ _ _ checked) => some (certifiedResult checked source)
  | .pure (.structuralComputed _ _ checked) => some (structuralResult checked source)
  | _ => other prior step source

def NeedsNonComputed {dependencies program block} : Step dependencies program block → Prop
  | .pure (.computed ..) | .pure (.certifiedComputed ..) | .pure (.structuralComputed ..) => False
  | _ => True

private theorem computed_refines {sources caller dependencies program block start count event children prepared before}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (location : RuntimeSourceEvent.Location (.computed event children) start count)
    (checked : @RuntimeComputedUse.Checked sources caller dependencies program block start count event prepared interval before)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.pure (.computed interval location prepared checked)))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.pure (.computed interval location prepared checked)))
    {chunk source history outputs}
    (read : readOps block.fuel interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (interval.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs interval.before ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs interval.after ownerAfter ordinaryAfter)
      (computedResult checked source) outputs := by
  have beforeAligned : ownerBefore = before := owners.1
  have afterAligned : ownerAfter = RuntimeComputedPredicate.continued event before checked.literal.output := owners.2
  subst ownerBefore
  subst ownerAfter
  cases ordinary
  obtain ⟨_,hidden,bits,values,_,frame,bindings,input,represented⟩ := agrees
  let operand : Binding := ⟨event.input,checked.literal.input.port⟩
  let rawEvent := Semantics.Raw.Event.protectedComputed interval.before.quantum.frame.length
    (operand.port.wires.map interval.before.quantum.frame.idxOf) operand.port.bits 1 checked.literal.table checked.literal.uses
  obtain ⟨operations,events,literal,trace,results,kept⟩ := pure_history_with_inherited
    (.computed interval location prepared checked) inherited inputs ordinaryBefore history values read executed
  have operationsMatch : operations = [checked.literal.operation] :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp (literal.symm.trans checked.literal.literal)
  subst operations
  have geometry := RuntimeComputedGeometry.literal_geometry checked.literal
  have sameEvents : events = [rawEvent] := congrArg Semantics.RawTrace.Prepared.events
    (Option.some.inj (trace.symm.trans geometry.2.2.2))
  subst events
  subst outputs
  obtain ⟨output,action⟩ := RuntimeComputedCallerAction.original_reference_action checked input
  let operator := RuntimeComputedCallerAction.sourceOperator prepared before.bindings operand source.operator
  have representedAfter : Qleisli.RuntimeStructuralHistory.Represents output interval.after
      (pureHistory dependencies [rawEvent] history) operator := by
    intro column physical bounded
    rw [geometry.1] at bounded
    have correspondence := action source.operator physical column
    change Qleisli.Semantics.RawAction.event dependencies rawEvent (fun row => history.operator row column) physical = _
    rw [RuntimeComputedCallerAction.literal_phase checked]
    rw [represented column physical bounded]
    exact (RuntimeComputedCallerAction.literal_phase checked _ _).symm.trans correspondence
  exact .cons ⟨rfl,hidden,bits,kept,_,checked.literal.after,checked.literal.afterBindings,
    checked.literal.afterBindings ▸ output,cast_represents checked.literal.afterBindings output representedAfter⟩ .nil

private theorem certified_refines {sources caller dependencies program block start count event children prepared before}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (location : RuntimeSourceEvent.Location (.computed event children) start count)
    (checked : @RuntimeCertifiedComputed.Checked sources caller dependencies program block start count event prepared interval before)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.pure (.certifiedComputed interval location prepared checked)))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.pure (.certifiedComputed interval location prepared checked)))
    {chunk source history outputs}
    (read : readOps block.fuel interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (interval.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs interval.before ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs interval.after ownerAfter ordinaryAfter)
      (certifiedResult checked source) outputs := by
  have beforeAligned : ownerBefore = before := owners.1
  have afterAligned : ownerAfter = RuntimeComputedPredicate.continued event before checked.literal.output := owners.2
  subst ownerBefore
  subst ownerAfter
  cases ordinary
  obtain ⟨_,hidden,bits,values,_,frame,bindings,input,represented⟩ := agrees
  let operand : Binding := ⟨event.input,checked.literal.input.port⟩
  let rawEvent := Semantics.Raw.Event.computed interval.before.quantum.frame.length
    (operand.port.wires.map interval.before.quantum.frame.idxOf) operand.port.bits 1 checked.literal.table
    checked.literal.useSteps checked.literal.logicalSteps
  obtain ⟨operations,events,literal,trace,results,kept⟩ := pure_history_with_inherited
    (.certifiedComputed interval location prepared checked) inherited inputs ordinaryBefore history values read executed
  have operationsMatch : operations = [checked.literal.operation] :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp (literal.symm.trans checked.literal.original)
  subst operations
  have geometry := RuntimeComputedGeometry.certified_geometry checked.literal
  have sameEvents : events = [rawEvent] := congrArg Semantics.RawTrace.Prepared.events
    (Option.some.inj (trace.symm.trans geometry.2))
  subst events
  subst outputs
  obtain ⟨output,action⟩ := RuntimeCertifiedComputedAction.original_reference_action checked input
  let operator := RuntimeLiteralHistory.applySourceOwner before.bindings before.bindings operand operand
    prepared.logical.matrix source.operator
  have representedAfter : Qleisli.RuntimeStructuralHistory.Represents output interval.after
      (pureHistory dependencies [rawEvent] history) operator := by
    intro column physical bounded
    rw [geometry.1] at bounded
    have correspondence := action source.operator physical column
    change Qleisli.Semantics.RawAction.event dependencies rawEvent (fun row => history.operator row column) physical = _
    have held : operand ∈ checked.literal.frame.bindings :=
      checked.literal.sameFrame.symm ▸ RuntimeBasisOwnerGeometry.selected_binding checked.literal.input
    have live := checked.literal.frame.complete.mem_iff.mp (List.mem_map.mpr ⟨operand,held,rfl⟩)
    have valid := Raw.Ownership.valid _ interval.history.1
    have axesBound : ∀ axis ∈ operand.port.wires.map interval.before.quantum.frame.idxOf,
        axis < interval.before.quantum.frame.length := by
      intro axis member
      obtain ⟨wire,wireMember,rfl⟩ := List.mem_map.mp member
      exact List.idxOf_lt_length_iff.mpr (valid.covered wire (List.mem_flatMap.mpr ⟨_,live,wireMember⟩))
    have localEvent : Qleisli.RawFiniteRows.BoundedEvent interval.before.quantum.frame.length rawEvent
        interval.before.quantum.frame.length :=
      .computed _ _ _ _ _ _ _ axesBound
    exact (localEvent.congr dependencies _ _ (represented column) physical bounded).trans correspondence
  exact .cons ⟨rfl,hidden,bits,kept,_,checked.literal.after,checked.literal.afterBindings,
    checked.literal.afterBindings ▸ output,cast_represents checked.literal.afterBindings output representedAfter⟩ .nil

private theorem structural_exit {sources caller dependencies program block start count event before}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (checked : @StructuralComputedRaw.IntervalChecked sources caller dependencies program block start count event interval before) :
    {interval.before with quantum := checked.checked.raw.after} = interval.after := by
  obtain ⟨work,left,ran⟩ := interval.intervalRead
  rw [checked.literal] at ran
  cases fuel : block.fuel with
  | zero => rw [fuel] at ran; cases ran
  | succ fuel =>
    rw [fuel] at ran
    unfold Raw.Observation.checkOps at ran
    obtain ⟨result,remaining,folded,ran⟩ := Finite.bind_success _ _ _ _ _ ran
    obtain ⟨_,_,_,ran⟩ := Finite.bind_success _ _ _ _ _ ran
    have final := (Finite.pure_success _ _ _ _ ran).1
    subst result
    simp only [List.foldlM_cons,List.foldlM_nil] at folded
    obtain ⟨next,work',localStep,rest⟩ := Finite.bind_success _ _ _ _ _ folded
    have same := (Finite.pure_success _ _ _ _ rest).1
    subst next
    obtain ⟨transition,_,actual,_,_⟩ := Qleisli.RuntimeIntervalRawFold.checkStep_pure_raw
      dependencies _ interval.before interval.after checked.packet.operation work work' localStep
    have sameQuantum : interval.after.quantum = transition.state :=
      congrArg Raw.Observation.State.quantum actual
    rw [checked.afterQuantum,sameQuantum]
    exact actual.symm

private theorem structural_refines {sources caller dependencies program block start count event children before}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (location : RuntimeSourceEvent.Location (.computed event children) start count)
    (checked : @StructuralComputedRaw.IntervalChecked sources caller dependencies program block start count event interval before)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.pure (.structuralComputed interval location checked)))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.pure (.structuralComputed interval location checked)))
    {chunk source history outputs}
    (read : readOps block.fuel interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (interval.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs interval.before ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs interval.after ownerAfter ordinaryAfter)
      (structuralResult checked source) outputs := by
  have beforeAligned : ownerBefore = before := owners.1
  have afterAligned : ownerAfter = RuntimeComputedPredicate.continued event before checked.checked.output := owners.2
  subst ownerBefore
  subst ownerAfter
  cases ordinary
  obtain ⟨_,hidden,bits,values,_,frame,bindings,input,represented⟩ := agrees
  let action := checked.checked
  let rawEvent := Semantics.Raw.Event.structuralComputed interval.before.quantum.frame.length
    (action.raw.input.wires.map interval.before.quantum.frame.idxOf) checked.packet.forward
    checked.packet.inverse checked.packet.uses
  obtain ⟨operations,events,literal,trace,results,kept⟩ := pure_history_with_inherited
    (.structuralComputed interval location checked) inherited inputs ordinaryBefore history values read executed
  have operationsMatch : operations = [checked.packet.operation] :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp (literal.symm.trans checked.literal)
  subst operations
  have geometry := StructuralComputedRestoration.interval_trace checked
  have sameEvents : events = [rawEvent] := congrArg Semantics.RawTrace.Prepared.events
    (Option.some.inj (trace.symm.trans geometry.2))
  subst events
  subst outputs
  obtain ⟨output,corresponds⟩ := RuntimeComputedCallerAction.structural_reference_action checked input
  let operand : Binding := ⟨event.input,action.owner.port⟩
  let operator := RuntimeComputedCallerAction.structuralSourceOperator action.matched before.bindings operand source.operator
  have representedAfter : Qleisli.RuntimeStructuralHistory.Represents output interval.after
      (pureHistory dependencies [rawEvent] history) operator := by
    intro column physical bounded
    rw [geometry.1] at bounded
    have correspondence := corresponds source.operator physical column
    change Qleisli.Semantics.RawAction.event dependencies rawEvent (fun row => history.operator row column) physical = _
    rw [RuntimeComputedCallerAction.structural_literal_phase checked]
    rw [represented column physical bounded]
    exact (RuntimeComputedCallerAction.structural_literal_phase checked _ _).symm.trans correspondence
  let next := (RuntimeComputedPredicate.continued event before action.output).bindings
  have exitMap (state : Raw.Observation.State)
      (same : ({interval.before with quantum := action.raw.after} : Raw.Observation.State) = state) :
      ∃ mapped : RuntimeOwnerMap.Checked (next.map (·.owner)) state, mapped.bindings = next := by
    subst state
    exact ⟨action.continuation,action.sameContinuation⟩
  obtain ⟨afterFrame,sameBindings⟩ := exitMap interval.after (structural_exit checked)
  exact .cons ⟨rfl,hidden,bits,kept,_,afterFrame,sameBindings,action.sameContinuation ▸ output,
    cast_represents action.sameContinuation output representedAfter⟩ .nil

theorem sourceStep_with_computed {dependencies program block}
    (steps : List (Step dependencies program block)) (inputs : List Nat) (inherited : Option (Nat → Prop))
    (certifies : Step dependencies program block → Prop)
    (other : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsNonComputed step)
      other (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement steps certifies (withComputed other) (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  refine WithChunkWriteBound.of_trace ?_
  intro writes source history outputs agrees executed
  cases first
  case pure node =>
    cases node
    case computed =>
      exact ⟨_,rfl,computed_refines _ _ inputs inherited owners ordinary read agrees executed⟩
    case certifiedComputed =>
      exact ⟨_,rfl,certified_refines _ _ inputs inherited owners ordinary read agrees executed⟩
    case structuralComputed =>
      exact ⟨_,rfl,structural_refines _ _ inputs inherited owners ordinary read agrees executed⟩
    all_goals
      exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed

#print axioms sourceStep_with_computed
end Qleisli.RuntimeLiteralBody
