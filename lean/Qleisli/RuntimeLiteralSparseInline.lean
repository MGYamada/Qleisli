import Qleisli.RuntimeSparseHeadAction
import Qleisli.RuntimeLiteralStructuralRefinement

/-! The actual original direct gate or tape preserves the complete sparse
arm history using the checked singleton action and caller ownership.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeNamedGateLift (Form)
open Qleisli.RuntimeLiteralInlinePrimitive (literalForm inline_reference_action inline_caller_geometry)
open Qleisli.RuntimeLiteralHistory (Agrees applySourceOwner sourcePrimitive sourceInlinePrimitive pure_history lookup_owner)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory pureHistory_operator_congr)
open Qleisli.RuntimeSemanticForest (Frame action)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.RuntimeNamedChildRuns (OrdinaryAligned)
open RuntimePureBody (Step)

private theorem sparse_inline_history {dependencies program block start count input output role kind roles}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (original : RuntimePrimitiveSource.Checked primitive)
    (form : Form) (literal : primitive.interval.operations = [form.operation input output])
    (checked : RuntimeOwnerMap.Checked roles primitive.interval.interval.before)
    (bindings : checked.bindings = original.frame.bindings)
    (frame : Frame checked.bindings)
    (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State) (history : History) (joint : Nat → Nat → ℂ)
    (agrees : Agrees inputs primitive.interval.interval.before ordinary history)
    (represented : Represents frame primitive.interval.interval.before history joint) {events results}
    (read : readOps block.fuel primitive.interval.interval.before.quantum.reference
      ((block.operations.drop start).take count) = some (primitive.interval.interval.after.quantum.reference,events))
    (executed : run dependencies block.fuel events history = some results) :
    ∃ resultFrame : Frame original.after.bindings, ∃ expected result,
      sourceInlinePrimitive original checked.bindings joint = some expected ∧ results = [result] ∧
      result.values = history.values ∧ result.hidden = history.hidden ∧
      Agrees inputs primitive.interval.interval.after ordinary result ∧
      Represents resultFrame primitive.interval.interval.after result expected := by
  obtain ⟨localEntry,rawEvents,localEvents,lifted,_,operand,localLaw⟩ :=
    inline_reference_action primitive original form literal
  obtain ⟨target,present,owner,port⟩ := RuntimeNamedPrimitiveOutputs.port_binding original.inputPort
  have member : target ∈ checked.bindings := bindings.symm ▸ present
  have interface := port.symm ▸ lifted.parentInterface
  obtain ⟨returned,returnedMember,returnedOwner,spectators,frames,wires,inputRead,outputRead⟩ :=
    inline_caller_geometry primitive original checked bindings target member owner port interface
  have inputShape := primitive.action.logicalShape.1
  have outputShape := primitive.action.logicalShape.2
  rw [primitive.equation] at inputShape outputShape
  obtain ⟨resultFrame,whole⟩ := Qleisli.RuntimeSparseHeadAction.whole_action checked original.owners.after frame
    primitive.interval.interval.history.1 target returned member returnedMember spectators frames wires
    primitive.inputCode primitive.outputCode primitive.expected inputRead outputRead inputShape outputShape rawEvents
    (by
      intro Reference amplitudes base row reference bound
      rw [port]
      exact localLaw amplitudes base row reference (by rwa [primitive.action.physicalShape.2]))
  obtain ⟨operations,performed,operationsLiteral,performedTrace,resultsEq,agreesAfter⟩ :=
    pure_history (.primitive primitive original) inputs ordinary history agrees read executed
  have operationsEq : operations = primitive.interval.operations :=
    (List.map_inj_right (f := Semantics.Observation.Op.pure)
      (fun _ _ equal => Semantics.Observation.Op.pure.inj equal)).mp
      (operationsLiteral.symm.trans primitive.interval.literal)
  subst operations
  have sameTrace : performed = rawEvents := congrArg Semantics.RawTrace.Prepared.events
    (Option.some.inj (performedTrace.symm.trans lifted.parentTrace))
  subst performed
  let slice : RuntimeAdjacentSlices.Slice block start count :=
    ⟨primitive.interval.interval,primitive.interval.operations,primitive.interval.literal⟩
  have bounded := RawFiniteRows.checked_slice slice rawEvents lifted.parentTrace
  let expected := applySourceOwner checked.bindings original.after.bindings target returned primitive.expected joint
  have targetRead : RuntimeOwnerMap.byOwner checked.bindings role = some target :=
    owner ▸ lookup_owner checked target member
  have returnedRead : RuntimeOwnerMap.byOwner original.after.bindings role = some returned :=
    returnedOwner ▸ lookup_owner original.owners.after returned returnedMember
  refine ⟨resultFrame,expected,pureHistory dependencies rawEvents history,?_,resultsEq,rfl,rfl,agreesAfter,?_⟩
  · simp [sourceInlinePrimitive,targetRead,returnedRead,sourcePrimitive,operand,expected]
  · intro column row bound
    have actual := pureHistory_operator_congr bounded dependencies history
      (fun row col => action frame primitive.interval.interval.before.quantum.frame joint row col)
      represented column row bound
    have result := whole joint row column
    have frameEq : original.interval.after.quantum.frame = primitive.interval.interval.after.quantum.frame :=
      congrArg (fun state : Raw.Observation.State => state.quantum.frame)
        (RuntimeIntervalStates.same_after original.interval primitive.interval.interval)
    rw [frameEq] at result
    exact actual.trans result

theorem sparse_inline_refines {dependencies program block start count input output role kind}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (original : RuntimePrimitiveSource.Checked primitive)
    (form : Form) (literal : primitive.interval.operations = [form.operation input output])
    (inputs : List Nat) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter (.pure (.primitive primitive original)))
    (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter (.pure (.primitive primitive original)))
    {chunk source history outputs}
    (read : readOps block.fuel primitive.interval.interval.before.quantum.reference
      ((block.operations.drop start).take count) = some (primitive.interval.interval.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgrees inputs primitive.interval.interval.before ownerBefore ordinaryBefore source history)
    (executed : run dependencies block.fuel chunk history = some outputs) :
    ∃ expected, sourceInlineHistory original source = some expected ∧
      List.Forall₂ (SemanticHistoryAgrees inputs primitive.interval.interval.after ownerAfter ordinaryAfter) expected outputs := by
  rcases owners with ⟨rfl,rfl⟩
  cases ordinary
  obtain ⟨ownerState,hidden,bits,values,_,checked,bindings,frame,represented⟩ := agrees
  obtain ⟨resultFrame,operator,result,sourceRead,rfl,sameValues,sameHidden,agreesAfter,resultRepresents⟩ :=
    sparse_inline_history primitive original form literal checked (bindings.trans original.sameHistory.symm)
      (bindings.symm ▸ frame) inputs _ history source.operator values
      (cast_represents bindings.symm frame represented) read executed
  let stateEq := RuntimeIntervalStates.same_after original.interval primitive.interval.interval
  let outputChecked := RuntimeNamedThreeFrameChain.checkedAt stateEq original.owners.after
  have incoming := congrArg RuntimeStructuralAction.SourceState.bindings ownerState
  refine ⟨[{source with owners := original.after, operator}],?_,.cons
    ⟨rfl,sameHidden.trans hidden,?_,agreesAfter,_,outputChecked,?_,resultFrame,resultRepresents⟩ .nil⟩
  · simp only [sourceInlineHistory,incoming,← bindings,sourceRead,Option.map_some]
  · rw [sameValues]
    exact bits
  · exact RuntimeNamedThreeFrameChain.checkedAt_bindings stateEq original.owners.after

def NeedsNonInline {dependencies program block} : @Step dependencies program block → Prop
  | .pure (.primitive primitive _) => (literalForm primitive).isNone
  | _ => True

noncomputable def withSparseInline {dependencies program block}
    (fallback : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .pure (.primitive primitive original) =>
    match literalForm primitive with
    | none => fallback prior step source
    | some _ => sourceInlineHistory original source
  | _ => fallback prior step source

theorem sourceStep_with_sparse_inline {dependencies program block}
    (steps : List (@Step dependencies program block)) (inputs : List Nat)
    (certifies : Step dependencies program block → Prop)
    (fallback : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (remaining : StepRefinement steps (fun step => certifies step ∧ NeedsNonInline step)
      fallback (fun _ => SemanticHistoryAgrees inputs)) :
    StepRefinement steps certifies (withSparseInline fallback) (fun _ => SemanticHistoryAgrees inputs) := by
  intro prior first later position certified ownerBefore ownerAfter ordinaryBefore ordinaryAfter
    owners ordinary chunk read source history outputs agrees executed
  cases first
  case pure node =>
    cases node
    case primitive primitive original =>
      cases found : literalForm primitive with
      | none =>
        obtain ⟨expected,evaluated,related⟩ :=
          remaining prior (.pure (.primitive primitive original)) later position
            ⟨certified,by simp [NeedsNonInline,found]⟩ owners ordinary read agrees executed
        exact ⟨expected,by simpa only [withSparseInline,found] using evaluated,related⟩
      | some form =>
        obtain ⟨expected,evaluated,related⟩ :=
          sparse_inline_refines primitive original form.val form.property inputs owners ordinary read agrees executed
        exact ⟨expected,by simpa only [withSparseInline,found] using evaluated,related⟩
    all_goals
      exact remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read agrees executed
  all_goals
    exact remaining prior _ later position ⟨certified,trivial⟩ owners ordinary read agrees executed

#print axioms sparse_inline_refines
#print axioms sourceStep_with_sparse_inline
end Qleisli.RuntimeLiteralBody
