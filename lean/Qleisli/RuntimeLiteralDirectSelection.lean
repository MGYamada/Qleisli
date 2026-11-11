import Qleisli.RuntimeSparseOperationAction
import Qleisli.RuntimeSemanticSelectionSource

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
open Qleisli.RuntimeMultiwayGram (ordinal_table)

noncomputable def sourceDirectSelection {dependencies program block}
    (node : Node dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  match node with
  | .selection _ _ _ _ _ _ _ _ expected _ _ codes _ =>
    some [{source with
      owners := {source.owners with bindings := codes.owners.transport.after.bindings}
      operator := Qleisli.RuntimeSourceOrdinalAction.sourceAction codes.owners.transport.after.bindings
        codes.owners.returned.first codes.owners.returned.second expected source.operator}]
  | _ => none

/-- The exact source node supplies the original logical action. Its ordered
singleton history carries the same visible SSA and inherited observations
with no additional bounded complete-forest witness. -/
theorem semantic_direct_selection_refines
    {dependencies program block start count initialTokens finalTokens selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count initialTokens finalTokens [selector,target])
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations finalTokens)) retained)
    {inputCode outputCode labels expected logical}
    (equations : RuntimeInterval.Computed
      (NominalSector.checkLogicals inputCode outputCode retained.sectors labels expected) logical)
    (codes : RuntimePureBody.SelectionCodes frame.interval initialTokens finalTokens selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels) :
    let node := Node.selection frame selectorBits targetBits retained restricted inputCode outputCode
      labels expected logical equations codes layouts
    ∀ (inputs : List Nat) (inherited : Option (Nat → Prop))
      {ownerBefore ownerAfter ordinaryBefore ordinaryAfter},
      Aligned ownerBefore ownerAfter (.pure node) →
      OrdinaryAligned ordinaryBefore ordinaryAfter (.pure node) →
      ∀ {chunk source history outputs},
      readOps block.fuel (nodeSpan node).checked.before.quantum.reference (nodeSpan node).operations =
        some ((nodeSpan node).checked.after.quantum.reference,chunk) →
      SemanticHistoryAgreesWithInherited inherited inputs (nodeSpan node).checked.before
        ownerBefore ordinaryBefore source history →
      run dependencies block.fuel chunk history = some outputs →
      ∃ expected, sourceDirectSelection node source = some expected ∧
        List.Forall₂ (SemanticHistoryAgreesWithInherited inherited inputs (nodeSpan node).checked.after
          ownerAfter ordinaryAfter) expected outputs := by
  intro node inputs inherited ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary
    chunk source history outputs read agrees executed
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
    simp only [node,sourceDirectSelection,ownerState,after,operator]
  apply Qleisli.RuntimeSparseOperationAction.pure_step_history_lift node inputs inherited
    codes.owners.transport.after rfl source history operator agrees read executed
  intro ops events opsRead traced
  have sameOps : ops = frame.operations :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp
      (opsRead.symm.trans frame.literal)
  subst ops
  have bounded := RawFiniteRows.checked_slice ⟨frame.interval,frame.operations,frame.literal⟩ events traced
  let incoming : RuntimeSemanticForest.Frame codes.owners.before.bindings := beforeMap ▸ input
  have sourceInput := cast_represents beforeMap input
    (state := frame.interval.before) (history := history) (operator := source.operator) represented
  obtain ⟨_,table⟩ := ordinal_table equations
  obtain ⟨trace,output,action⟩ := RuntimeSemanticSelectionSource.direct_selection_action
    frame restricted codes layouts table incoming
  have sameEvents : trace.traceResult.events = events :=
    congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (trace.executed.symm.trans traced))
  rw [sameEvents] at action
  refine ⟨output,?_⟩
  intro column row bound
  have native := pureHistory_operator_congr bounded dependencies history _ sourceInput column row bound
  exact native.trans (action source.operator row column)

/-- Compatibility for callers that still traverse retained selection witnesses. -/
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
  | @selection _ _ _ _ _ _ frame _ _ _ restricted _ _ _ _ _ equations codes layouts _ _ =>
    exact semantic_direct_selection_refines frame restricted equations codes layouts
      inputs inherited owners ordinary read agrees executed

#print axioms semantic_direct_selection_refines
#print axioms direct_selection_refines
end Qleisli.RuntimeLiteralBody
