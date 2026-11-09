import Qleisli.RuntimeLiteralObservationAction
import Qleisli.RuntimeNamedThreeFrameChain

/-! Derive a named primitive's source action in the original caller
coordinates and compare it with the actual literal history. The full
spectator and reference state is carried through each coordinate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralHistory
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open QleisliKernel.Semantics.Observation (Event readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeOriginalBranchJoin (RepresentsOperator)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory pureHistory_operator_congr run_pure)
open Qleisli.RuntimeNamedCallerAction (canonicalJoint updatedJoint)
open Qleisli.RuntimeNamedHeadCoefficients (applyHead)
open Qleisli.RuntimeForestProduct (referenceAction)
open RuntimeForestCode (Frame)
open RuntimeOwnerMap (Binding Map)
open RuntimeNamedPrimitiveOccurrence (Occurrence)
open RuntimeOwnerCodeReindex (dimensionAt)

private def NamedPrimitiveOrdinary {dependencies program block} :
    RuntimePureBody.Step dependencies program block → Prop
  | .named _ scope _ _ _ final (.cons (.pure (.primitive ..)) .nil) => final = scope.visible.ssa
  | _ => True

private theorem named_primitive_ordinary {artifact root execution fuel program block step}
    (call : @RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) program block step) :
    NamedPrimitiveOrdinary step := by
  cases call with
  | @named start count inputs caller before ordinary event scope body bodyRead
      rootOwner rootName path request plan assigned result receipts boundary beforeInput afterInput afterChild inputRead childRead =>
    cases emitted : result.steps with
    | nil => trivial
    | cons first rest =>
      cases rest with
      | cons second rest =>
        cases first
        case pure node => cases node <;> trivial
        all_goals trivial
      | nil =>
        cases first
        case pure node =>
          cases node
          case primitive action binding =>
            simp only [NamedPrimitiveOrdinary,RuntimePureBody.Steps.ofList,List.foldr_cons,List.foldr_nil]
            obtain ⟨_,_,_,flow,_⟩ := RuntimeNamedChildRuns.core_flow artifact root execution fuel
              .localScope (.whole body) path scope.program request plan _ scope.visible.ssa
              scope.prepared.block (result,receipts) ⟨afterInput,afterChild,childRead⟩
            have values := flow.ordinary
            change RuntimeNamedChildRuns.OrdinaryRun scope.visible.ssa result.steps result.ordinary at values
            rw [emitted] at values
            cases values with
            | cons head tail =>
              cases tail
              exact head
          all_goals trivial
        all_goals trivial

noncomputable def applySourceOwner {Reference : Type} (incoming outgoing : Map)
    (input output : Binding) (matrix : Semantics.Exact.Matrix) (joint : Nat → Reference → ℂ) :
    Nat → Reference → ℂ :=
  let source := fun logical ref =>
    joint (Qleisli.MixedRadix.recode (input::incoming.erase input) incoming (sourceDimension incoming) logical) ref
  fun logical ref => applyHead matrix source
    (Qleisli.MixedRadix.recode outgoing (output::outgoing.erase output) (sourceDimension outgoing) logical) ref

/-- Interpret the actual source operand and the specified primitive. The
matrix and both coordinate changes come from the original source data. -/
noncomputable def sourcePrimitive {sources : Sources} {caller : String} {Reference : Type}
    (event : SourceRuntimeContext.Event sources caller) (incoming outgoing : Map)
    (input output : Binding) (joint : Nat → Reference → ℂ) : Option (Nat → Reference → ℂ) := do
  let matrix ← (RuntimeSourcePrimitiveAction.operand event).bind fun (kind,owner) =>
    Semantics.PrimitiveOperator.meaning kind owner.basis
  return applySourceOwner incoming outgoing input output matrix joint

private theorem updatedJoint_source {Reference : Type}
    {inputRoles outputRoles before after inputChecked outputChecked}
    (input : @Frame inputRoles before inputChecked) (output : @Frame outputRoles after outputChecked)
    (inputTarget outputTarget : Binding) (matrix : Semantics.Exact.Matrix) (joint : Nat → Reference → ℂ) :
    updatedJoint input output inputTarget outputTarget matrix joint =
      applySourceOwner inputChecked.bindings outputChecked.bindings inputTarget outputTarget matrix joint := by
  funext logical ref
  unfold updatedJoint canonicalJoint RuntimeForestRegroup.regroupIndex applySourceOwner
  rw [funext (dimensionAt_source input.owners), funext (dimensionAt_source output.owners)]

/-- The retained source primitive and returned caller owner determine the
entire operator after the named interval. Its literal history retains the
incoming visible values and hidden outcomes. -/
def NamedPrimitiveHistory {dependencies program block} :
    ∀ {step}, @Occurrence dependencies program block step → Prop
  | _, @Occurrence.named _ _ _ start count _ _ _ before _ _ ordinary _ _ _ _ _ _ _ scope _ _ boundary final _ original bound =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (input : Frame checked),
      checked.bindings = before.bindings →
      ∀ (inputs : List Nat) (history : History) (joint : Nat → Nat → ℂ),
      Agrees inputs scope.interval.before ordinary history → RepresentsOperator input history joint →
      ∀ {events : List Event} {results : List History},
      readOps block.fuel scope.interval.before.quantum.reference ((block.operations.drop start).take count) =
        some (scope.interval.after.quantum.reference,events) →
      run dependencies block.fuel events history = some results →
      ∃ returned, boundary.mapped = [returned] ∧
      ∃ output : Frame boundary.afterFrame, ∃ expected result,
        sourcePrimitive original.event checked.bindings boundary.afterFrame.bindings bound.binding returned joint =
          some expected ∧ results = [result] ∧ result.values = history.values ∧
          result.hidden = history.hidden ∧ final.measurements = ordinary.measurements ∧
          Agrees inputs scope.interval.after final result ∧
          RepresentsOperator output result expected

theorem named_primitive_history {artifact root execution fuel program block step}
    (held : @Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step) :
    NamedPrimitiveHistory held := by
  cases held with
  | @named start count tokens sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body bodyRead boundary finalOrdinary primitive original bound =>
    intro roles checked input bindings inputs history joint agrees represented events results read executed
    let occurrence := Occurrence.named (read := bodyRead) (finalOrdinary := finalOrdinary) original bound
    obtain ⟨rawEvents,folded,traced⟩ :=
      (RuntimeIntervalRawFold.mixed_call_traces scope [bound.operation] bound.parent).1
    have on := RuntimeNamedOccurrenceAction.on_span occurrence rawEvents folded
    obtain ⟨output⟩ := RuntimeNamedThreeFrameChain.primitive_after_frame occurrence call rawEvents on
      checked input bindings
    obtain ⟨returned,mapped,whole⟩ :=
      RuntimeNamedCallerAction.actual_whole_caller_action occurrence call rawEvents on checked input bindings output
    have same : results = [pureHistory root.dependencies rawEvents history] := by
      cases depth : block.fuel with
      | zero =>
        rw [depth] at executed
        cases executed
      | succ depthFuel =>
        rw [bound.parent,depth] at read
        have readPure := RuntimeAdjacentSlices.readOps_pure depthFuel _ _ _ traced
        have eventsEq : events = rawEvents.map Semantics.Observation.Event.pure :=
          congrArg Prod.snd (Option.some.inj (read.symm.trans readPure))
        rw [depth,eventsEq] at executed
        exact Option.some.inj (executed.symm.trans (run_pure root.dependencies depthFuel rawEvents history))
    let expected := applySourceOwner checked.bindings boundary.afterFrame.bindings
      bound.binding returned primitive.expected joint
    have source := (RuntimeSourcePrimitiveAction.reference_action primitive original).2.1
    have bounded := RawFiniteRows.checked_slice (RuntimeNamedOccurrenceAction.span occurrence).slice rawEvents traced
    have final : finalOrdinary = scope.visible.ssa := named_primitive_ordinary call
    refine ⟨returned,mapped,output,expected,pureHistory root.dependencies rawEvents history,?_,same,rfl,rfl,
      ?_,?_,?_⟩
    · simp [sourcePrimitive,source,expected]
    · rw [final]
      exact scope.visible.measurements
    · rw [final]
      refine ⟨?_,?_⟩
      · intro id expression member
        change (id,expression) ∈ scope.visible.table at member
        rw [scope.visible.original] at member
        exact agrees.1 id expression (List.mem_filter.mp member).1
      · obtain ⟨work,left,intervalRead⟩ := scope.interval.intervalRead
        have issued := (Raw.Observation.checkOps_history _ _ _ _ _ _ _ intervalRead).2.2
        intro id member
        exact Qleisli.RuntimeObservingPrefix.issued_mono issued (agrees.2 member)
    · intro col row boundRow
      have actual := pureHistory_operator_congr bounded root.dependencies history
        (fun row col => referenceAction input joint row col) represented col row boundRow
      have representedOutput := whole joint row col
      rw [updatedJoint_source] at representedOutput
      exact actual.trans representedOutput

#print axioms named_primitive_history
end Qleisli.RuntimeLiteralHistory
