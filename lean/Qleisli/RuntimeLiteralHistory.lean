import Qleisli.RuntimeLiteralBody
import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeIntervalTrace
import Qleisli.RuntimeOriginalObservationValues
import Qleisli.RuntimeOriginalObservation
import Qleisli.RuntimeOriginalBranchJoin
import Qleisli.RuntimeBoundaryOwnerEvidence
import Qleisli.RuntimeNamedOutputOrder

/-! Local history laws for the literal classical and erasure intervals of the
original body. The operator follows the source action on each inherited
reference column, and ordinary agreement uses the actual resulting history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralHistory
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (Event readOps)
open QleisliKernel.Semantics.Finite (Dependency)
open RuntimeForestCode (Frame OwnerCode)
open RuntimeOrdinaryBody (valuation)
open RuntimeOrdinarySSA (Agreement)
open Qleisli.Semantics.ObservingAction (History run step)
open Qleisli.RuntimeForestProduct (referenceAction)
open Qleisli.RuntimeOriginalBranchJoin (RepresentsOperator)
open Qleisli.RuntimeOriginalObservation (outcomeJoint)
open Qleisli.RuntimeObservingPrefix (Issued issued_mono)
open Qleisli.RuntimeObservingValueRetention (Supports)
open Qleisli.RuntimeNamedThreePackedInstrument (advance pureHistory run_pure)
open RuntimeOwnerCodeReindex (dimensionAt reindex_exists)
open Qleisli.RuntimeForestOrderedProduct (frame_product_agrees ordered_product_action product_agrees sparseProduct)
open Qleisli.HierarchicalSemantics (mapM_members)
open Qleisli.RuntimeLiteralBody (nodeSpan)

def AgreesWithInherited (inherited : Option (Nat → Prop))
    (inputs : List Nat) (raw : Raw.Observation.State) (ordinary : RuntimeOrdinaryBody.State)
    (history : History) : Prop :=
  Agreement (valuation inputs ordinary.measurements history.values) history.values ordinary.table ∧
  Supports (fun id => match inherited with
    | none => Issued raw id
    | some holds => holds id ∨ Issued raw id) history

abbrev Agrees := AgreesWithInherited none

private theorem pure_node_operations {dependencies program block}
    (node : RuntimePureBody.Node dependencies program block) :
    ∃ operations : List Semantics.Raw.Op,
      (nodeSpan node).operations = operations.map Semantics.Observation.Op.pure := by
  cases node with
  | primitive action _ => exact ⟨_,action.interval.literal⟩
  | structural action => exact ⟨[action.operation],action.literal⟩
  | named _ frame _ _ _ _ => exact ⟨_,frame.literal⟩
  | operation frame _ _ _ _ _ _ _ _ _ => exact ⟨_,frame.literal⟩
  | selection frame _ _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_,frame.literal⟩

/-- Every pure node runs its exact Raw trace on all reference columns. Its
ordinary valuation and hidden outcomes remain those of the incoming history. -/
theorem pure_history_with_inherited {dependencies program block}
    (node : RuntimePureBody.Node dependencies program block)
    (inherited : Option (Nat → Prop)) (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State) (history : History)
    {events : List Event} {results : List History} :
    let span := nodeSpan node
    AgreesWithInherited inherited inputs span.checked.before ordinary history →
    readOps block.fuel span.checked.before.quantum.reference span.operations =
      some (span.checked.after.quantum.reference,events) →
    run dependencies block.fuel events history = some results →
    ∃ operations rawEvents,
      span.operations = operations.map Semantics.Observation.Op.pure ∧
      RuntimeLocalEvents.trace span.checked.before.quantum.reference operations =
        some ⟨span.checked.after.quantum.reference,rawEvents,span.checked.before.quantum.frame.length⟩ ∧
      results = [pureHistory dependencies rawEvents history] ∧
      AgreesWithInherited inherited inputs span.checked.after ordinary (pureHistory dependencies rawEvents history) := by
  intro span agrees read executed
  obtain ⟨operations,literal⟩ := pure_node_operations node
  obtain ⟨work,left,checked⟩ := span.checked.intervalRead
  change span.operations = _ at literal
  change (Raw.Observation.checkOps dependencies block.fuel span.checked.before span.operations).run work =
    (.ok span.checked.after,left) at checked
  rw [literal] at checked read
  obtain ⟨rawEvents,traced⟩ := RuntimeIntervalTrace.checkOps_pure_trace dependencies block.fuel
    span.checked.before span.checked.after operations work left checked
  cases depth : block.fuel with
  | zero =>
    rw [depth] at executed
    cases executed
  | succ fuel =>
    have literalEvents := RuntimeAdjacentSlices.readOps_pure fuel _ operations _ traced
    rw [depth] at read executed
    have same : events = rawEvents.map Semantics.Observation.Event.pure :=
      congrArg Prod.snd (Option.some.inj (read.symm.trans literalEvents))
    rw [same] at executed
    have exactRun := run_pure dependencies fuel rawEvents history
    have keep := (Raw.Observation.checkOps_history _ _ _ _ _ _ _ checked).2.2
    refine ⟨operations,rawEvents,literal,traced,Option.some.inj (executed.symm.trans exactRun),agrees.1,?_⟩
    intro id member
    cases inherited with
    | none => exact issued_mono keep (agrees.2 member)
    | some _ => exact (agrees.2 member).imp (fun retained => retained) (issued_mono keep)

theorem pure_history {dependencies program block}
    (node : RuntimePureBody.Node dependencies program block)
    (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State) (history : History)
    {events : List Event} {results : List History} :
    let span := nodeSpan node
    Agrees inputs span.checked.before ordinary history →
    readOps block.fuel span.checked.before.quantum.reference span.operations =
      some (span.checked.after.quantum.reference,events) →
    run dependencies block.fuel events history = some results →
    ∃ operations rawEvents,
      span.operations = operations.map Semantics.Observation.Op.pure ∧
      RuntimeLocalEvents.trace span.checked.before.quantum.reference operations =
        some ⟨span.checked.after.quantum.reference,rawEvents,span.checked.before.quantum.frame.length⟩ ∧
      results = [pureHistory dependencies rawEvents history] ∧
      Agrees inputs span.checked.after ordinary (pureHistory dependencies rawEvents history) :=
  pure_history_with_inherited node none inputs ordinary history

private theorem gap_bindings {dependencies program block start count before ssa}
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count before ssa) :
    gap.beforeFrame.bindings = gap.afterFrame.bindings :=
  (RuntimeBoundaryOwnerEvidence.check_bindings gap.beforeFrame gap.beforeRead).trans
    (RuntimeBoundaryOwnerEvidence.check_bindings gap.afterFrame gap.afterRead).symm

private def gapFrame {dependencies program block start count before ssa}
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count before ssa)
    (input : Frame gap.beforeFrame) : Frame gap.afterFrame :=
  ⟨gap_bindings gap ▸ input.owners,input.code,by
    rw [← gap_bindings gap]
    exact input.original⟩

private theorem gap_action {dependencies program block start count before ssa}
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count before ssa)
    (input : Frame gap.beforeFrame) (joint : Nat → Nat → ℂ) (row col : Nat) :
    referenceAction (gapFrame gap input) joint row col = referenceAction input joint row col := by
  simp only [referenceAction,Frame.embedding,gapFrame,← gap_bindings gap,gap.quantum]

/-- The actual classical interval returns one history, with the same
operator in exactly the same source code and the checked new SSA values. -/
theorem gap_history {dependencies program block start count before ssa}
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count before ssa)
    (input : Frame gap.beforeFrame) (inputs : List Nat) (history : History) (joint : Nat → Nat → ℂ)
    (agrees : Agrees inputs gap.checked.interval.before ssa history)
    (represented : RepresentsOperator input history joint)
    {events : List Event} {results : List History}
    (read : readOps block.fuel gap.checked.interval.before.quantum.reference
      ((block.operations.drop start).take count) =
        some (gap.checked.interval.after.quantum.reference,events))
    (executed : run dependencies block.fuel events history = some results) :
    ∃ output : Frame gap.afterFrame,
      List.Forall₂ (fun expected result =>
        result.hidden = history.hidden ∧ Agrees inputs gap.checked.interval.after gap.ssa result ∧
        RepresentsOperator output result expected) [joint] results := by
  obtain ⟨original,result,literal,ran,hidden,operator,values,support⟩ :=
    RuntimeOriginalObservationValues.original_gap_values gap inputs history agrees.1 agrees.2
  have same : events = original := congrArg Prod.snd (Option.some.inj (read.symm.trans literal))
  subst events
  have sameResults := Option.some.inj (executed.symm.trans ran)
  subst results
  refine ⟨gapFrame gap input,.cons ⟨hidden,⟨values,support⟩,?_⟩ .nil⟩
  intro col row bound
  change result.operator row col = referenceAction (gapFrame gap input) joint row col
  rw [operator,gap_action]
  exact represented col row (by simpa only [gap.quantum] using bound)

theorem run_single (dependencies : List Dependency) (fuel : Nat) (event : Event) (history : History) :
    run dependencies (fuel+1) [event] history = step dependencies (run dependencies fuel) event history := by
  change [event].foldlM (advance dependencies (run dependencies fuel)) [history] = _
  simp only [List.foldlM_cons,List.foldlM_nil,bind_pure]
  cases executed : step dependencies (run dependencies fuel) event history <;> simp [advance,executed]

theorem observation_permutation {sources caller functionName dependencies program event block position previous roles}
    (observed : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous)
    (source : RuntimeOwnerMap.Checked roles observed.interval.before)
    (bindings : source.bindings = previous) :
    observed.before.bindings.Perm source.bindings := by
  have selected := RuntimeOriginalObservation.original_before_bindings observed
  have subset : observed.before.bindings ⊆ source.bindings := by
    intro binding member
    obtain ⟨_,_,found⟩ := mapM_members _ _ _ selected binding member
    rw [bindings]
    exact List.mem_of_find?_eq_some found
  have size : observed.before.bindings.length = source.bindings.length := by
    have ports := observed.before.complete.trans source.complete.symm
    simpa only [List.length_map] using ports.length_eq
  have distinct : observed.before.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : RuntimeOwnerMap.Binding => binding.port.token)
      (fun _ _ different equal => different (congrArg (fun binding : RuntimeOwnerMap.Binding =>
        binding.port.token) equal)) observed.before.tokensDistinct
  obtain ⟨other,permuted,contained⟩ := List.subperm_iff.mp (distinct.subperm subset)
  have same := contained.eq_of_length (size.trans permuted.length_eq.symm)
  exact same ▸ permuted

/-- The incoming source's actual frame can be ordered for the observation
without changing its operator. The recoding uses its retained owner layouts. -/
theorem observation_entry {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa roles}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    {source : RuntimeOwnerMap.Checked roles observation.checked.interval.before}
    (bindings : source.bindings = before.bindings)
    (input : Frame source) (history : History) (joint : Nat → Nat → ℂ)
    (represented : RepresentsOperator input history joint) :
    ∃ reordered : Frame observation.checked.before,
      RepresentsOperator reordered history (fun logical col =>
        joint (Qleisli.MixedRadix.recode observation.checked.before.bindings source.bindings
          (dimensionAt input.owners) logical) col) := by
  let wanted := observation.checked.before.bindings
  have permutation : wanted.Perm source.bindings := observation_permutation observation.checked source bindings
  obtain ⟨codes,read⟩ := reindex_exists input.owners wanted permutation.subset
  obtain ⟨reordered,retained⟩ := RuntimeForestFrameEvidence.with_ownerCodes observation.checked.before codes
  have dimension : reordered.code.dimension = (sparseProduct codes).dimension := by
    rw [(frame_product_agrees reordered).dimension,retained,(product_agrees codes).dimension]
  refine ⟨reordered,?_⟩
  intro col row bound
  change history.operator row col = referenceAction reordered (fun logical col =>
    joint (Qleisli.MixedRadix.recode wanted source.bindings (dimensionAt input.owners) logical) col) row col
  calc
    _ = referenceAction input joint row col := represented col row bound
    _ = _ := by
      rw [RuntimeNamedOutputOrder.regroup_dense_action input wanted ⟨codes,read⟩ permutation,
        ordered_product_action reordered,dimension,retained]

/-- Each result of the actual observation interval carries exactly its
source outcome action and its updated ordinary valuation. The result order
and the entire hidden outcome history come from the original interpreter. -/
theorem observation_history {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    (input : Frame observation.checked.before) (inputs : List Nat) (history : History) (joint : Nat → Nat → ℂ)
    (agrees : Agrees inputs observation.checked.interval.before ssa history)
    (represented : RepresentsOperator input history joint)
    {events : List Event} {results : List History}
    (read : readOps block.fuel observation.checked.interval.before.quantum.reference
      ((block.operations.drop position.start).take position.count) =
        some (observation.checked.interval.after.quantum.reference,events))
    (executed : run dependencies block.fuel events history = some results) :
    event.value = RuntimeObservationAction.result functionName event observation.checked.operand
      observation.checked.measured ∧
    ∃ consumed : OwnerCode observation.checked.input, ∃ output : Frame observation.checked.after,
    ∃ branch : Nat → History,
      let count := 2^observation.checked.input.port.wires.length
      results = (List.range count).map branch ∧
      ∀ outcome, outcome < count →
        (branch outcome).values = (match observation.checked.measured with
          | none => history.values
          | some id => history.values ++ [(id,outcome == 1)]) ∧
        (branch outcome).hidden = history.hidden++[outcome] ∧
        Agrees inputs observation.checked.interval.after observation.ordinary (branch outcome) ∧
        RepresentsOperator output (branch outcome) (outcomeJoint consumed outcome joint) := by
  let axes := observation.checked.input.port.wires.map observation.checked.interval.before.quantum.reference.frame.idxOf
  let erasure := Event.erase observation.checked.interval.before.quantum.reference.frame.length axes
    observation.checked.measured
  obtain ⟨literal,source,consumed,output,action⟩ :=
    RuntimeOriginalObservation.original_observation_histories observation.checked input
  have same : events = [erasure] := congrArg Prod.snd (Option.some.inj (read.symm.trans literal))
  subst events
  cases depth : block.fuel with
  | zero =>
    rw [depth] at executed
    cases executed
  | succ fuel =>
    obtain ⟨branch,performed,facts⟩ := action (run dependencies fuel) joint history
      (fun row bound col => represented col row bound)
    have ordered : results = (List.range (2^axes.length)).map branch := by
      rw [depth,run_single,performed] at executed
      exact (Option.some.inj executed).symm
    have values := RuntimeOriginalObservationValues.observation_step_values observation inputs history
      agrees.1 agrees.2 (run dependencies fuel) performed
    have width : axes.length = observation.checked.input.port.wires.length := List.length_map _
    refine ⟨source,consumed,output,branch,by rw [← width]; exact ordered,?_⟩
    intro outcome bound
    have inRange : outcome < 2^axes.length := by simpa only [width] using bound
    obtain ⟨visible,hidden,operator⟩ := facts outcome inRange
    have member : branch outcome ∈ (List.range (2^axes.length)).map branch :=
      List.mem_map_of_mem (List.mem_range.mpr inRange)
    exact ⟨visible,hidden,values _ member,fun col row rowBound => operator row rowBound col⟩

#print axioms pure_history
#print axioms gap_history
#print axioms observation_entry
#print axioms observation_history
end Qleisli.RuntimeLiteralHistory
