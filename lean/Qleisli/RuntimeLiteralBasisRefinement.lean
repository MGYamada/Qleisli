import Qleisli.RuntimeLiteralStructuralRefinement
import Qleisli.RuntimeBasisReference

/-! A coherent source basis expression contributes its exact operator to the
original body history. Its literal interval preserves ordinary SSA and hidden
outcomes while changing the owner encoding according to the same table.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Step)
open RuntimeOwnerMap (Binding)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.RuntimeNamedChildRuns (OrdinaryAligned)
open Qleisli.Semantics.ObservingAction (History run)
open Semantics.Observation (readOps)
open Qleisli.RuntimeBasisReference (sourceOperator original_reference_action)
open Qleisli.RuntimeLiteralHistory (pure_history_with_inherited)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)

/-- Every retained valuation has the same encoded action by
`original_reference_action`. A first row represents this common action. -/
private noncomputable def basisResult {sources caller dependencies program block start count event before}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (checked : @RuntimeBasisAction.Checked sources caller dependencies program block start count event interval before)
    (source : SourceHistory) : Option (List SourceHistory) :=
  event.function.rows.head?.map fun row =>
    let operand : Binding := ⟨event.input,checked.input.port⟩
    let returned : Binding := ⟨event.output,checked.output⟩
    [{source with
      owners := RuntimeBasisAction.continued event before checked.output
      operator := sourceOperator before.bindings checked.after.bindings operand returned row source.operator}]

noncomputable def withBasis {dependencies program block}
    (other : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.basis _ _ _ checked) => basisResult checked source
  | _ => other prior step source

def NeedsNonBasis {dependencies program block} : Step dependencies program block → Prop
  | .pure (.basis ..) => False
  | _ => True

private theorem basis_refines {sources caller dependencies program block start count event before}
    {interval : @RuntimeInterval.Checked dependencies program block start count}
    (location : RuntimeSourceEvent.Location (.basis event) start count)
    (sourceBody : RuntimeBasisAction.Source (sources := sources) (caller := caller) event)
    (checked : RuntimeBasisAction.Checked event interval before)
    (inputs : List Nat) (inherited : Option (Nat → Prop)) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.pure (.basis interval location sourceBody checked)))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.pure (.basis interval location sourceBody checked)))
    {chunk source history outputs}
    (read : readOps block.fuel interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (interval.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs interval.before ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    ∃ expected, basisResult checked source = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs interval.after ownerAfter ordinaryAfter) expected outputs := by
  have beforeAligned : ownerBefore = before := owners.1
  have afterAligned : ownerAfter = RuntimeBasisAction.continued event before checked.output := owners.2
  subst ownerBefore
  subst ownerAfter
  cases ordinary
  obtain ⟨_,hidden,bits,values,_,frame,bindings,input,represented⟩ := agrees
  let operand : Binding := ⟨event.input,checked.input.port⟩
  let returned : Binding := ⟨event.output,checked.output⟩
  let operation := Semantics.Raw.Op.liftBasis operand.port.token returned.port.token returned.port.wires checked.table
  let rawEvent := Semantics.Raw.Event.liftBasis interval.before.quantum.frame.length interval.after.quantum.frame.length
    (operand.port.wires.map interval.before.quantum.frame.idxOf)
    (returned.port.wires.map interval.after.quantum.frame.idxOf) checked.table
  obtain ⟨operations,events,literal,trace,results,kept⟩ := pure_history_with_inherited
    (.basis interval location sourceBody checked) inherited inputs ordinaryBefore history values read executed
  have ops : operations = [operation] :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp (literal.symm.trans checked.literal)
  subst operations
  have traced := (Qleisli.RuntimeBasisOwnerGeometry.literal_geometry checked frame bindings).2.2.2
  have sameEvents : events = [rawEvent] := congrArg Semantics.RawTrace.Prepared.events
    (Option.some.inj (trace.symm.trans traced))
  subst events
  subst outputs
  cases selected : event.function.rows.head? with
  | none =>
    have present := (Bool.and_eq_true_iff.mp checked.codes.agreement).1
    have empty := List.head?_eq_none_iff.mp selected
    rw [empty] at present
    contradiction
  | some row =>
    obtain ⟨output,action⟩ := original_reference_action checked frame bindings input (List.mem_of_head? selected)
    let operator := sourceOperator before.bindings checked.after.bindings operand returned row source.operator
    have representedAfter : Qleisli.RuntimeStructuralHistory.Represents output interval.after
        (pureHistory dependencies [rawEvent] history) operator := by
      intro column physical bounded
      have correspondence := action source.operator physical column bounded
      refine Eq.trans ?_ correspondence
      simp only [pureHistory,Qleisli.Semantics.RawAction.events,List.foldl_cons,List.foldl_nil,rawEvent,
        Qleisli.Semantics.RawAction.event]
      apply Qleisli.Exact.sum_map_congr
      intro index present
      rw [represented column index (List.mem_range.mp present)]
    refine ⟨[{source with owners := RuntimeBasisAction.continued event before checked.output, operator}],?_,
      .cons ⟨rfl,hidden,bits,kept,_,checked.after,checked.afterBindings,checked.afterBindings ▸ output,
        cast_represents checked.afterBindings output representedAfter⟩ .nil⟩
    simp only [basisResult,selected,Option.map_some]
    rfl

theorem sourceStep_with_basis {dependencies program block}
    (steps : List (Step dependencies program block)) (inputs : List Nat) (inherited : Option (Nat → Prop))
    (certifies : Step dependencies program block → Prop)
    (other : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsNonBasis step)
      other (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement steps certifies (withBasis other) (fun _ => SemanticHistoryAgreesWithInherited inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read
  refine WithChunkWriteBound.of_trace ?_
  intro writes source history outputs agrees executed
  cases first
  case pure node =>
    cases node
    case basis =>
      exact basis_refines _ _ _ inputs inherited owners ordinary read agrees executed
    all_goals
      exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed
  all_goals
    exact ((remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read).apply writes) agrees executed

#print axioms sourceStep_with_basis
end Qleisli.RuntimeLiteralBody
