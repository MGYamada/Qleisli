import Qleisli.RuntimeSparseOperationAction
import Qleisli.RuntimeSourceOrdinalAction
import Qleisli.RuntimeFiniteTargetAction

/-! Apply the original direct coherent selection to the shared sparse history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run)
open RuntimePureBody (Node Step)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.RuntimeNamedChildRuns (OrdinaryAligned)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory_operator_congr)
open Qleisli.RuntimeMultiwayGram (ordinal_table selector_card sourceAction)
open Qleisli.RuntimeForestProduct (referenceAction)

noncomputable def sourceDirectSelection {dependencies program block}
    (node : Node dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  match node with
  | .selection _ _ _ _ _ _ _ _ expected _ _ codes _ =>
    some [{source with
      owners := {source.owners with bindings := codes.owners.transport.after.bindings}
      operator := Qleisli.RuntimeSourceOrdinalAction.sourceAction codes.owners.transport.after.bindings
        codes.owners.returned.first codes.owners.returned.second expected source.operator}]
  | _ => none

/-- The same ordered singleton history carries the selection's original
finite action and the inherited SSA and observation state. -/
theorem direct_selection_refines {dependencies program}
    {block : RuntimeInterval.Block dependencies program} {node : Node dependencies program block}
    (witness : RuntimeSelectionWitness.Checked node)
    (inputs : List Nat) (inherited : Option (Nat → Prop))
    {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.pure node))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.pure node))
    {chunk source history outputs}
    (read : readOps block.fuel (nodeSpan node).checked.before.quantum.reference (nodeSpan node).operations =
      some ((nodeSpan node).checked.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs (nodeSpan node).checked.before
      ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    ∃ expected, sourceDirectSelection node source = some expected ∧
      List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs (nodeSpan node).checked.after
        ownerAfter ordinaryAfter) expected outputs := by
  cases witness with
  | @selection start count initialTokens finalTokens selector target frame selectorBits targetBits retained
      restricted inputCode outputCode labels expected logical equations codes layouts literal original =>
    let node := Node.selection frame selectorBits targetBits retained restricted inputCode outputCode
      labels expected logical equations codes layouts
    change ownerBefore.bindings = codes.owners.before.bindings ∧
      ownerAfter = {ownerBefore with bindings := codes.owners.transport.after.bindings} at owners
    rcases owners with ⟨beforeMap,rfl⟩
    change ordinaryAfter = ordinaryBefore at ordinary
    cases ordinary
    obtain ⟨_,_,_,input,represented⟩ := agrees.2.2.2.2
    let operator := Qleisli.RuntimeSourceOrdinalAction.sourceAction codes.owners.transport.after.bindings
      codes.owners.returned.first codes.owners.returned.second expected source.operator
    let after := {ownerBefore with bindings := codes.owners.transport.after.bindings}
    refine ⟨[{source with owners := after, operator}],?_,?_⟩
    · have ownerState := agrees.1
      simp only [sourceDirectSelection,ownerState,after,operator]
    apply Qleisli.RuntimeSparseOperationAction.pure_step_history_lift node inputs inherited
      codes.owners.transport.after rfl source history operator agrees read executed
    intro ops events opsRead traced
    have sameOps : ops = frame.operations :=
      (List.map_inj_right (f := Semantics.Observation.Op.pure)
        (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp
        (opsRead.symm.trans frame.literal)
    subst ops
    have sameEvents : literal.traceResult.events = events :=
      congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (literal.executed.symm.trans traced))
    have bounded := RawFiniteRows.checked_slice ⟨frame.interval,frame.operations,frame.literal⟩ events traced
    let incoming : RuntimeSemanticForest.Frame codes.owners.before.bindings := beforeMap ▸ input
    have sourceInput := cast_represents beforeMap input
      (state := frame.interval.before) (history := history) (operator := source.operator) represented
    have sameCode : incoming.code = literal.inputCode.code :=
      Option.some.inj (incoming.original.symm.trans literal.inputCode.original)
    have referenceInput : ∀ column, RawFiniteRows.OnRows frame.interval.before.quantum.frame.length
        (fun row => history.operator row column) (fun row => referenceAction literal.inputCode source.operator row column) := by
      intro column row bound
      refine (sourceInput column row bound).trans ?_
      change RuntimeSemanticForest.action incoming _ _ _ _ =
        referenceAction literal.inputCode source.operator row column
      rw [← RuntimeSemanticForest.ofNative_action literal.inputCode source.operator row column]
      unfold RuntimeSemanticForest.action
      rw [sameCode]
      rfl
    obtain ⟨_,table⟩ := ordinal_table equations
    refine ⟨RuntimeSemanticForest.ofNative literal.outputCode,?_⟩
    intro column row bound
    have native := pureHistory_operator_congr bounded dependencies history _ referenceInput column row bound
    have action := Qleisli.RuntimeFiniteTargetAction.caller_action frame codes layouts literal table
      source.operator row column
    rw [sameEvents] at action
    have coordinates := Qleisli.RuntimeSourceOrdinalAction.onFinite_ordinalAction literal.outputCode
      codes.owners.returned.first codes.owners.returned.second
      ((RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered).1 (by simp))
      table (selector_card frame codes layouts literal) source.operator
    rw [RuntimeNamedSelectionWholeOutput.onFinite_reference] at action
    change RuntimeNamedSelectionWholeOutput.onFinite
      (sourceAction frame codes layouts literal table source.operator) = operator at coordinates
    rw [coordinates] at action
    exact native.trans (action.trans (RuntimeSemanticForest.ofNative_action literal.outputCode _ _ _).symm)

#print axioms direct_selection_refines
end Qleisli.RuntimeLiteralBody
