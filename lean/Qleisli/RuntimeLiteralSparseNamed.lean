import Qleisli.RuntimeSparseHeadAction
import Qleisli.RuntimeLiteralStructuralRefinement

/-! The actual single-primitive child run uses the same sparse caller
action as a direct primitive. The original call and its result order remain
bound to the checked parent interval.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (run)
open Qleisli.RuntimeLiteralHistory (applySourceOwner sourcePrimitive named_primitive_execution)
open Qleisli.RuntimeLiteralBranchChoice (measurementBits)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory pureHistory_operator_congr)
open Qleisli.RuntimeSemanticForest (action)
open Qleisli.RuntimeStructuralHistory (Represents)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.RuntimeNamedChildRuns (ChildRun OrdinaryAligned)
open RuntimePureBody (Step runBlockCore)
open RuntimeNamedPrimitiveOccurrence (Occurrence inspect?)

theorem sparse_named_primitive_refines {artifact root mode fuel program block step}
    (held : @Occurrence root.dependencies program block step)
    (call : ChildRun artifact root mode (runBlockCore artifact root mode (fuel+1)) step)
    (inputs : List Nat) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter step) (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter step)
    {chunk source history outputs}
    (read : readOps block.fuel (stepSpan step).checked.before.quantum.reference (stepSpan step).operations =
      some ((stepSpan step).checked.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgrees inputs (stepSpan step).checked.before ownerBefore ordinaryBefore source history)
    (executed : run root.dependencies block.fuel chunk history = some outputs) :
    ∃ expected, sourceNamedPrimitive held source = some expected ∧
      List.Forall₂ (SemanticHistoryAgrees inputs (stepSpan step).checked.after ownerAfter ordinaryAfter)
        expected outputs := by
  cases held with
  | @named start count tokens sources caller before childHistory childRetired old first size inputToken outputToken role kind
      event scope body bodyRead boundary finalOrdinary primitive original bound =>
    let occurrence := Occurrence.named (read := bodyRead) (finalOrdinary := finalOrdinary) original bound
    rcases owners with ⟨rfl,rfl⟩
    rcases ordinary with ⟨rfl,rfl⟩
    obtain ⟨ownerState,hidden,bits,values,_,checked,bindings,input,represented⟩ := agrees
    obtain ⟨rawEvents,on,bounded,rfl,measurements,agreesAfter⟩ :=
      named_primitive_execution occurrence call inputs history values read executed
    obtain ⟨returned,mapped,returnedMember,outputRead⟩ :=
      RuntimeNamedPrimitiveOutputs.actual_occurrence_output_code occurrence call
    obtain ⟨geometricReturn,geometricMap,_,wires,frames,spectators⟩ :=
      RuntimeNamedCallerGeometry.actual_geometry occurrence call rawEvents on checked bindings
    have sameReturn : geometricReturn = returned := (List.cons.inj (geometricMap.symm.trans mapped)).1
    subst geometricReturn
    have selection := RuntimeSelectionPartition.order_values _ _ _ boundary.input.orderRead
    have targetMember : bound.binding ∈ checked.bindings := by
      rw [bindings]
      exact selection.1 ((congrArg (fun bs => bound.binding ∈ bs) bound.singleton).mpr
        (List.mem_singleton_self _))
    have carriers := RuntimeNamedPrimitiveInputs.actual_occurrence_input occurrence call
    change primitive.interval.selected.map (fun port => (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) =
      RuntimeForestCode.carrierOwners boundary.input.ordered at carriers
    have inputRead := primitive.inputRead
    rw [carriers,bound.singleton] at inputRead
    obtain ⟨_,_,operand,localLaw⟩ := on
    have ports : scope.selected = [bound.binding.port] :=
      (RuntimeNamedFrameAxes.mixed_bound_ports scope boundary).trans
        (congrArg (List.map RuntimeOwnerMap.Binding.port) bound.singleton)
    have axes : RuntimeNamedFrameAxes.mixedAxes scope =
        RuntimeNamedGateLift.portAxes scope.interval.before.quantum bound.binding.port := by
      change (scope.selected.flatMap (·.wires)).map scope.interval.before.quantum.frame.idxOf = _
      simpa only [List.flatMap_singleton] using
        congrArg (fun selected : List Semantics.Raw.Port =>
          (selected.flatMap (·.wires)).map scope.interval.before.quantum.frame.idxOf) ports
    rw [axes] at localLaw
    have inputShape := primitive.action.logicalShape.1
    have outputShape := primitive.action.logicalShape.2
    rw [primitive.equation] at inputShape outputShape
    let orderedInput := bindings.symm ▸ input
    obtain ⟨output,whole⟩ := Qleisli.RuntimeSparseHeadAction.whole_action checked boundary.afterFrame
      orderedInput scope.interval.history.1 bound.binding returned targetMember returnedMember
      spectators frames wires primitive.inputCode primitive.outputCode primitive.expected inputRead outputRead
      inputShape outputShape rawEvents
      (fun amplitudes base row reference bounded =>
        localLaw amplitudes base row reference (by rwa [primitive.action.physicalShape.2]))
    let operator := applySourceOwner checked.bindings boundary.afterFrame.bindings
      bound.binding returned primitive.expected source.operator
    let result := pureHistory root.dependencies rawEvents history
    have representedInput := cast_represents bindings.symm input represented
    have representedOutput : Represents output scope.interval.after result operator := by
      intro column row boundRow
      have actual := pureHistory_operator_congr bounded root.dependencies history
        (fun row col => action orderedInput scope.interval.before.quantum.frame source.operator row col)
        representedInput column row boundRow
      exact actual.trans (whole source.operator row column)
    have sourceRead : sourcePrimitive original.event checked.bindings boundary.afterFrame.bindings
        bound.binding returned source.operator = some operator := by
      simp [sourcePrimitive,operand,operator]
    have incoming := congrArg RuntimeStructuralAction.SourceState.bindings ownerState
    refine ⟨[{source with owners := boundary.after, operator}],?_,.cons
      ⟨rfl,hidden,?_,agreesAfter,_,boundary.afterFrame,boundary.sameAfter,boundary.sameAfter ▸ output,
        cast_represents boundary.sameAfter output representedOutput⟩ .nil⟩
    · simp only [sourceNamedPrimitive,mapped,incoming,← bindings,← boundary.sameAfter,bind,Option.bind,pure,sourceRead]
    · change measurementBits _ history.values = _
      rw [measurements]
      exact bits

noncomputable def withSparseNamed {dependencies program block}
    (fallback : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match step with
  | .named .. =>
    match inspect? step with
    | none => fallback prior step source
    | some held => sourceNamedPrimitive held source
  | _ => fallback prior step source

#print axioms sparse_named_primitive_refines
end Qleisli.RuntimeLiteralBody
