import Qleisli.RuntimeLiteralBasisRefinement
import Qleisli.RuntimeComputedCallerAction

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

noncomputable def withComputed {dependencies program block}
    (other : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.computed _ _ _ checked) => some (computedResult checked source)
  | _ => other prior step source

def NeedsNonComputed {dependencies program block} : Step dependencies program block → Prop
  | .pure (.computed ..) => False
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
    all_goals
      exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed

#print axioms sourceStep_with_computed
end Qleisli.RuntimeLiteralBody
