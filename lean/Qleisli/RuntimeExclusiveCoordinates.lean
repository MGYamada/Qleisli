import Qleisli.RawAccessCommutation
import Qleisli.RuntimeCallHistorySourceRefinement
import Qleisli.RuntimeLiteralHistory
import Qleisli.RuntimeLiteralStructuralRefinement
import Qleisli.RuntimeSparseBlockEncoding
import QleisliKernel.Qirf.RuntimeExclusiveAction

/-! Finite coordinate lift of a separately established source action through
the actual selected axes and spectators of an indexed access.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeExclusiveCoordinates
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (gather scatter)
open Qleisli.RuntimeCallTraceFrames (WireOrder native_wires)
open Qleisli.RuntimeCallTraceProjection (split_axes split_eq sum_split)
open Qleisli.RuntimeForestProduct (gather_bound)
open RuntimeOwnerMap (Owner Map)
open RuntimeStructuralAction (SourceState)
open RuntimeExclusiveAction (Repartition)
open Qleisli.RuntimeLiteralBody (SourceHistory SemanticHistoryAgreesWithInherited TraceWriteBound
  WithChunkWriteBound StepRefinement At ScopedSourceSteps)
open Qleisli.RuntimeCallHistory (SourceAgreementWithin)
open Qleisli.RuntimeNamedChildRuns (OrdinaryAligned)
open RuntimePureBody (Node Step)
open RuntimeSelectionSteps (Edge)
open Qleisli.Semantics.ObservingAction (History run)
open Semantics.Observation (readOps)
open Qleisli.RuntimeSemanticForest (Frame action frame_exists)
open Qleisli.RuntimeSparseBlockEncoding (full_register_layout repartitionOperator repartition_checked_frames)

/-- The checked blocks and common spectators determine a source coordinate
change. It applies to each reference column of the original history. -/
noncomputable def repartitionHistory {before after : SourceState}
    (partition : Repartition before.bindings after.bindings) (physicalFrame : List Nat)
    (source : SourceHistory) : SourceHistory :=
  {source with
    owners := after
    operator := repartitionOperator physicalFrame before.bindings after.bindings partition.oldBlock
      partition.newBlock partition.spectators source.operator}

private theorem repartition_represents {beforeRoles afterRoles beforeState afterState beforeBindings afterBindings}
    (before : RuntimeOwnerMap.Checked beforeRoles beforeState)
    (after : RuntimeOwnerMap.Checked afterRoles afterState)
    (sourceBindings : before.bindings = beforeBindings) (targetBindings : after.bindings = afterBindings)
    (beforeValid : Raw.stateValid beforeState.quantum = true)
    (afterValid : Raw.stateValid afterState.quantum = true)
    (sameFrame : afterState.quantum.frame = beforeState.quantum.frame)
    (partition : Repartition beforeBindings afterBindings) (source : Frame beforeBindings) :
    ∃ target : Frame afterBindings,
      ∀ {Reference : Type} (operator : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
        action source beforeState.quantum.frame operator row reference =
          action target afterState.quantum.frame
            (repartitionOperator beforeState.quantum.frame beforeBindings afterBindings
              partition.oldBlock partition.newBlock partition.spectators operator) row reference := by
  subst beforeBindings
  subst afterBindings
  obtain ⟨target⟩ := frame_exists (bindings := after.bindings) (by
    intro binding member
    rcases List.mem_append.mp (partition.outputOrder.mem_iff.mpr member) with changed | spectator
    · obtain ⟨basis,width,wires⟩ := partition.newLayout binding changed
      exact (full_register_layout binding basis width wires).1
    · exact source.available binding (partition.inputOrder.mem_iff.mp (List.mem_append_right _ spectator)))
  refine ⟨target,?_⟩
  apply repartition_checked_frames before after beforeValid afterValid sameFrame
    partition.inputOrder partition.outputOrder source target
  · intro binding member
    obtain ⟨basis,width,wires⟩ := partition.oldLayout binding member
    exact (full_register_layout binding basis width wires).2
  · intro binding member
    obtain ⟨basis,width,wires⟩ := partition.newLayout binding member
    exact (full_register_layout binding basis width wires).2

/-- Structural routing changes the source owner representation while the
physical operator, ordinary values and observed outcomes are retained. -/
theorem repartition_history_agrees {beforeRoles afterRoles : List Owner}
    {beforeState afterState : RuntimeInterval.State} {before after : SourceState}
    {inputs : List Nat} {inherited : Option (Nat → Prop)} {ordinary : RuntimeOrdinaryBody.State}
    {source : SourceHistory} {history : History}
    (beforeMap : RuntimeOwnerMap.Checked beforeRoles beforeState)
    (afterMap : RuntimeOwnerMap.Checked afterRoles afterState)
    (entry : beforeMap.bindings = before.bindings) (exit : afterMap.bindings = after.bindings)
    (beforeValid : Raw.stateValid beforeState.quantum = true)
    (afterValid : Raw.stateValid afterState.quantum = true)
    (sameFrame : afterState.quantum.frame = beforeState.quantum.frame)
    (kept : beforeState.classical ⊆ afterState.classical)
    (partition : Repartition before.bindings after.bindings)
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs beforeState before ordinary source history) :
    SemanticHistoryAgreesWithInherited inherited inputs afterState after ordinary
      (repartitionHistory partition beforeState.quantum.frame source) history := by
  obtain ⟨_owners,hidden,bits,ordinaryValues,_,_,_,input,represented⟩ := agrees
  obtain ⟨output,converted⟩ :=
    repartition_represents beforeMap afterMap entry exit beforeValid afterValid sameFrame partition input
  refine ⟨rfl,hidden,bits,⟨ordinaryValues.1,?_⟩,afterRoles,afterMap,exit,output,?_⟩
  · intro id member
    cases inherited with
    | none => exact Qleisli.RuntimeObservingPrefix.issued_mono kept (ordinaryValues.2 member)
    | some _ =>
      exact (ordinaryValues.2 member).imp (fun inherited => inherited)
        (Qleisli.RuntimeObservingPrefix.issued_mono kept)
  · intro column row bounded
    have previous : row < 2^beforeState.quantum.frame.length := by simpa only [sameFrame] using bounded
    exact (represented column row previous).trans (converted source.operator row column)

/-- The checked enclosing literal and the two routing receipts start and end
in the same complete Raw states. This ties the source-frame conversion to
the boundaries that the existing literal interpreter consumes. -/
theorem active_literal_states {dependencies program block start count entry places returned}
    {inner : @RuntimeInterval.Checked dependencies program block start count}
    (opening : RuntimeAccessPartition.ActiveEntry inner entry places)
    (closing : RuntimeAccessPartition.ActiveExit opening returned)
    (outer : RuntimeInterval.Checked block (start-RuntimeAccessPartition.activeCount places)
      (RuntimeAccessPartition.activeCount places+count+RuntimeAccessPartition.activeCount places)) :
    outer.before = opening.preamble.before ∧ outer.after = closing.after := by
  have startAt := Qleisli.RuntimeAdjacentSlices.checkOps_unique outer.prefixRead opening.preamble.prefixRead
  have pre := opening.preamble.intervalRead
  rw [opening.connected] at pre
  have entire := outer.intervalRead
  rw [startAt,Qleisli.RuntimeAdjacentSlices.three_adjacent_slices _ _ _ _ opening.bounded] at entire
  exact ⟨startAt,Qleisli.RuntimeAdjacentSlices.checkOps_three_unique pre inner.intervalRead closing.original entire⟩

private theorem keeps_classical {dependencies fuel before after ops}
    (read : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies fuel before ops) after) :
    before.classical ⊆ after.classical := by
  obtain ⟨work,left,ran⟩ := read
  exact (Raw.Observation.checkOps_history _ _ _ _ _ work left ran).2.2

noncomputable def enterHistory {sources caller dependencies program block start count access interval suspended before}
    (opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
      access interval suspended before) (source : SourceHistory) : SourceHistory :=
  repartitionHistory opening.repartition opening.route.preamble.before.quantum.frame source

theorem enter_history_agrees {sources caller dependencies program block start count access interval suspended before}
    (opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
      access interval suspended before) {inherited inputs ordinary source history}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs opening.route.preamble.before
      before ordinary source history) :
    SemanticHistoryAgreesWithInherited inherited inputs interval.before opening.initial ordinary
      (enterHistory opening source) history := by
  obtain ⟨_,_,_,axes⟩ := Qleisli.Raw.AccessCommutation.structural_interval opening.route.preamble opening.route.routes
  have kept := keeps_classical opening.route.preamble.intervalRead
  rw [opening.route.connected] at axes kept
  exact repartition_history_agrees opening.route.frame opening.frame opening.route.originalFrame
    opening.nativeBindings opening.route.preamble.history.1 interval.history.1 axes kept opening.repartition agrees

noncomputable def exitHistory {sources caller dependencies program block start count access interval suspended before
    child retired}
    {opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
      access interval suspended before}
    (closing : RuntimeExclusiveAction.Closed opening child retired) (source : SourceHistory) : SourceHistory :=
  repartitionHistory closing.repartition interval.after.quantum.frame source

theorem exit_history_agrees {sources caller dependencies program block start count access interval suspended before
    child retired}
    {opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
      access interval suspended before}
    (closing : RuntimeExclusiveAction.Closed opening child retired) {inherited inputs ordinary source history}
    (agrees : SemanticHistoryAgreesWithInherited inherited inputs interval.after child ordinary source history) :
    SemanticHistoryAgreesWithInherited inherited inputs closing.literal.interval.after closing.after ordinary
      (exitHistory closing source) history := by
  have endAt := (active_literal_states opening.route closing.route closing.literal.interval).2
  obtain ⟨_,_,_,axes⟩ := Qleisli.Raw.AccessCommutation.structural_trace closing.route.original closing.route.routes
  have kept := keeps_classical closing.route.original
  rw [← endAt] at axes kept
  exact repartition_history_agrees closing.childFrame closing.afterFrame closing.childBindings closing.afterBindings
    interval.history.2.2.1 closing.literal.interval.history.2.2.1 axes kept closing.repartition agrees

/-- Apply the separately interpreted source child between the two actual
owner-coordinate changes. This evaluator obtains no operator from Raw. -/
noncomputable def evaluateAccess {sources caller dependencies program block start count access interval suspended before
    child retired}
    {opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
      access interval suspended before}
    (closing : RuntimeExclusiveAction.Closed opening child retired)
    (evaluateChild : SourceHistory → Option (List SourceHistory)) (source : SourceHistory) :
    Option (List SourceHistory) :=
  (evaluateChild (enterHistory opening source)).map (List.map (exitHistory closing))

private theorem transport_agreement {domain inherited inputs ordinary raw nextRaw before after source result history}
    (transport : SemanticHistoryAgreesWithInherited inherited inputs raw before ordinary source history →
      SemanticHistoryAgreesWithInherited inherited inputs nextRaw after ordinary result history)
    (agreement : SourceAgreementWithin domain inherited inputs raw before ordinary source history) :
    SourceAgreementWithin domain inherited inputs nextRaw after ordinary result history := by
  cases domain with
  | none => exact transport agreement
  | some admits => exact ⟨agreement.1,transport agreement.2⟩

/-- Lift the local semantic law for the actual child to the enclosing
indexed call. The runtime reader contributes only the checked event trace
and the native boundaries for the owner match. -/
theorem exclusive_history_refines {sources caller dependencies program block start count access interval suspended before
    child retired}
    {opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
      access interval suspended before}
    (closing : RuntimeExclusiveAction.Closed opening child retired)
    (inner : RuntimePureBody.Node dependencies program block)
    (location : Qleisli.RuntimeLiteralBody.At start (start+count) (.pure inner))
    (evaluateChild : SourceHistory → Option (List SourceHistory))
    (inputs : List Nat) (domain : Option (RuntimeOrdinaryBody.State → Prop))
    (inherited : Option (Nat → Prop)) (ordinary : RuntimeOrdinaryBody.State)
    (childLaw : ∀ {trace snapshot actual results},
      readOps block.fuel interval.before.quantum.reference ((block.operations.drop start).take count) =
        some (interval.after.quantum.reference,trace) →
      TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) trace →
      SourceAgreementWithin domain inherited inputs interval.before opening.initial ordinary snapshot actual →
      run dependencies block.fuel trace actual = some results →
      ∃ computed, evaluateChild snapshot = some computed ∧
        List.Forall₂ (SourceAgreementWithin domain inherited inputs interval.after child ordinary) computed results)
    {source history events results}
    (agrees : SourceAgreementWithin domain inherited inputs closing.literal.interval.before before
      ordinary source history)
    (read : readOps block.fuel closing.literal.interval.before.quantum.reference
      ((block.operations.drop (start-RuntimeExclusiveAction.routeCount access)).take
        (RuntimeExclusiveAction.routeCount access+count+RuntimeExclusiveAction.routeCount access)) =
      some (closing.literal.interval.after.quantum.reference,events))
    (writes : TraceWriteBound (inherited.map (fun holds id => ¬ holds id)) events)
    (executed : run dependencies block.fuel events history = some results) :
    ∃ expected, evaluateAccess closing evaluateChild source = some expected ∧
      List.Forall₂ (SourceAgreementWithin domain inherited inputs closing.literal.interval.after closing.after
        ordinary) expected results := by
  obtain ⟨depth,depthRead⟩ : ∃ depth, block.fuel = depth+1 := by
    cases found : block.fuel with
    | zero =>
      obtain ⟨_,_,checked⟩ := interval.intervalRead
      rw [found] at checked
      cases checked
    | succ depth => exact ⟨depth,rfl⟩
  have boundaries := active_literal_states opening.route closing.route closing.literal.interval
  have atEntry := transport_agreement (enter_history_agrees opening) (boundaries.1 ▸ agrees)
  obtain ⟨innerEvents,innerRead⟩ := Qleisli.RuntimeLiteralHistory.pure_node_read_at inner interval location
  have actualRead := Qleisli.Raw.AccessCommutation.active_checked_events opening.route closing.route depthRead innerRead
  rw [boundaries.1,boundaries.2] at read
  have sameEvents := congrArg Prod.snd (Option.some.inj (actualRead.symm.trans read))
  change innerEvents = events at sameEvents
  subst events
  obtain ⟨expected,checked,paired⟩ := childLaw innerRead writes atEntry executed
  refine ⟨expected.map (exitHistory closing),by simp only [evaluateAccess,checked,Option.map_some],?_⟩
  clear checked executed
  induction paired with
  | nil => exact .nil
  | cons head _ ih => exact .cons (transport_agreement (exit_history_agrees closing) head) ih

theorem sole_step {α : Type} {first step : α} {prior later : List α}
    (position : prior ++ first :: later = [step]) : first = step := by
  cases prior with
  | nil => exact (List.cons.inj position).1
  | cons head tail =>
    have length := congrArg List.length position
    simp at length

/-- Reuse a one-step source law at the actual reserved owner boundary. Both
steps inherit the same restriction on which ordinary IDs may be written. -/
theorem exclusive_step_refines {sources caller dependencies program block start count access interval suspended before
    child retired sourceEvent}
    {opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
      access interval suspended before}
    (occurrence : RuntimeSourceEvent.Location (.exclusive access sourceEvent) start count)
    (closing : RuntimeExclusiveAction.Closed opening child retired)
    (inner : RuntimePureBody.Node dependencies program block)
    (callOrdinary : RuntimeOrdinaryBody.State)
    (location : Qleisli.RuntimeLiteralBody.At start (start+count) (.pure inner))
    (aligned : Qleisli.RuntimeNamedSourceFlow.NodeAligned opening.initial child inner)
    (sameOrdinary : OrdinaryAligned callOrdinary callOrdinary (.pure inner))
    (evaluateChild : SourceHistory → Option (List SourceHistory))
    (inputs : List Nat) (domain : Option (RuntimeOrdinaryBody.State → Prop)) (inherited : Option (Nat → Prop))
    (childLaw : StepRefinement [.pure inner] (fun _ => True) (fun _ _ => evaluateChild)
      (fun _ => SourceAgreementWithin domain inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) :
    StepRefinement [.pure (.exclusive occurrence closing inner callOrdinary)] (fun _ => True)
      (fun _ _ => evaluateAccess closing evaluateChild)
      (fun _ => SourceAgreementWithin domain inherited inputs)
      (inherited.map (fun holds id => ¬ holds id)) := by
  intro prior first later position _ ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary trace read
  have same := sole_step position
  subst first
  change ownerBefore = before ∧ ownerAfter = closing.after at owners
  rcases owners with ⟨rfl,rfl⟩
  change ordinaryBefore = callOrdinary ∧ ordinaryAfter = callOrdinary at ordinary
  obtain ⟨ordinaryIn,ordinaryOut⟩ := ordinary
  subst ordinaryBefore
  subst ordinaryAfter
  apply WithChunkWriteBound.of_trace
  intro writes source history results agrees executed
  apply exclusive_history_refines closing inner location evaluateChild inputs domain inherited callOrdinary
    (agrees := agrees) (read := read) (writes := writes) (executed := executed)
  intro events snapshot actual outputs innerRead innerWrites atEntry innerExecution
  obtain ⟨slice,boundaryIn,boundaryOut⟩ := Qleisli.RuntimeLiteralHistory.pure_node_bounds_at inner interval location
  have childRead : readOps block.fuel (Qleisli.RuntimeLiteralBody.nodeSpan inner).checked.before.quantum.reference
      (Qleisli.RuntimeLiteralBody.nodeSpan inner).operations =
      some ((Qleisli.RuntimeLiteralBody.nodeSpan inner).checked.after.quantum.reference,events) := by
    simpa only [slice,boundaryIn,boundaryOut] using innerRead
  have childResult := (childLaw [] (.pure inner) [] rfl trivial aligned sameOrdinary childRead).apply
    innerWrites (boundaryIn.symm ▸ atEntry) innerExecution
  change ∃ expected, evaluateChild snapshot = some expected ∧
    List.Forall₂ (SourceAgreementWithin domain inherited inputs
      (Qleisli.RuntimeLiteralBody.nodeSpan inner).checked.after child callOrdinary) expected outputs at childResult
  simpa only [boundaryOut] using childResult

/-- The access changes the scope of the actual action and retains its ordinal
within the enclosing body. The same prefix still locates its source site. -/
noncomputable def evaluatePureAccess {dependencies program block}
    (evaluate : List Edge → List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (Step dependencies program block)) (scope : List Edge)
    (node : Node dependencies program block) (source : SourceHistory) : Option (List SourceHistory) :=
  match node with
  | .exclusive _ closing inner _ =>
    evaluateAccess closing (evaluatePureAccess evaluate prior (scope ++ [.exclusive prior.length]) inner) source
  | node => evaluate scope prior (.pure node) source
termination_by structural node

noncomputable def withIndexedAccess {dependencies} (evaluate : ScopedSourceSteps dependencies) :
    ScopedSourceSteps dependencies :=
  fun scope prior step source => match step with
    | .pure node => evaluatePureAccess evaluate prior scope node source
    | step => evaluate scope prior step source

def AccessLeaf {dependencies program block} : Node dependencies program block → Prop
  | .exclusive .. => False
  | _ => True

/-- This local law uses the same source evaluator and allowed writes as an
ordinary body step. The callback can still use the original prefix. -/
abbrev PureStepLaw {dependencies program block} (node : Node dependencies program block)
    (evaluate : SourceHistory → Option (List SourceHistory)) (inputs : List Nat)
    (domain : Option (RuntimeOrdinaryBody.State → Prop)) (inherited : Option (Nat → Prop)) : Prop :=
  StepRefinement [.pure node] (fun _ => True) (fun _ _ => evaluate)
    (fun _ => SourceAgreementWithin domain inherited inputs)
    (inherited.map (fun holds id => ¬ holds id))

theorem pure_step_law_of_occurrence {dependencies program block} (node : Node dependencies program block)
    {steps before after : List (Step dependencies program block)} (atStep : before ++ .pure node :: after = steps)
    {certifies evaluate inputs domain inherited}
    (law : StepRefinement steps certifies evaluate (fun _ => SourceAgreementWithin domain inherited inputs)
      (inherited.map (fun holds id => ¬ holds id))) (valid : certifies (.pure node)) :
    PureStepLaw node (evaluate before (.pure node)) inputs domain inherited := by
  intro prior first later position _
  have same := sole_step position
  subst first
  intro ownerBefore ownerAfter ordinaryBefore ordinaryAfter owners ordinary chunk read
  exact law before (.pure node) after atStep valid owners ordinary read

/-- Peel each original access from the source action and apply the law for
the innermost node at its authenticated occurrence. -/
theorem evaluate_pure_access_refines {dependencies program block}
    (evaluate : List Edge → List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (Step dependencies program block)) (inputs : List Nat)
    (domain : Option (RuntimeOrdinaryBody.State → Prop)) (inherited : Option (Nat → Prop))
    (certifies : Node dependencies program block → Prop)
    (innerReceipt : ∀ {sources caller start count access interval suspended before child retired sourceEvent}
      {opening : @RuntimeExclusiveAction.Opened sources caller dependencies program block start count
        access interval suspended before}
      (occurrence : RuntimeSourceEvent.Location (.exclusive access sourceEvent) start count)
      (closing : RuntimeExclusiveAction.Closed opening child retired) (inner : Node dependencies program block)
      (callOrdinary : RuntimeOrdinaryBody.State),
      certifies (.exclusive occurrence closing inner callOrdinary) →
        Qleisli.RuntimeNamedSourceFlow.NodeAligned opening.initial child inner ∧
        At start (start+count) (.pure inner) ∧ OrdinaryAligned callOrdinary callOrdinary (.pure inner) ∧ certifies inner)
    (leafLaw : ∀ scope node, AccessLeaf node → certifies node →
      PureStepLaw node (evaluate scope prior (.pure node)) inputs domain inherited)
    (scope : List Edge) (node : Node dependencies program block) (checked : certifies node) :
    PureStepLaw node (evaluatePureAccess evaluate prior scope node) inputs domain inherited := by
  revert checked
  cases node with
  | @exclusive program block sources caller start count access sourceEvent suspended before activeAfter activeRetired
      interval opening occurrence closing inner callOrdinary =>
    intro checked
    obtain ⟨aligned,location,ordinary,childChecked⟩ := innerReceipt occurrence closing inner callOrdinary checked
    exact exclusive_step_refines occurrence closing inner callOrdinary location aligned ordinary _ inputs domain inherited
      (evaluate_pure_access_refines evaluate prior inputs domain inherited certifies innerReceipt leafLaw
        (scope ++ [.exclusive prior.length]) inner childChecked)
  | _ => exact leafLaw scope _ trivial
termination_by sizeOf node
decreasing_by decreasing_tactic

private theorem apply_selected_with_spectators {Reference : Type}
    {frame selected spectators : List Nat}
    (partition : frame.Perm (selected ++ spectators)) (unique : frame.Nodup)
    (coeff : Nat → Nat → ℂ) (joint : Nat → Reference → ℂ)
    (selectedRow spectatorRow : Nat) (reference : Reference)
    (spectatorBound : spectatorRow < 2^spectators.length) :
    let selectedAxes := selected.map frame.idxOf
    let spectatorAxes := spectators.map frame.idxOf
    ((List.range (2^frame.length)).map fun input =>
      if spectatorRow = gather input spectatorAxes then
        coeff selectedRow (gather input selectedAxes) * joint input reference else 0).sum =
    ((List.range (2^selected.length)).map fun input =>
      coeff selectedRow input *
        joint (scatter (scatter 0 spectatorAxes spectatorRow) selectedAxes input) reference).sum := by
  intro selectedAxes spectatorAxes
  let reconstruct := fun localInput spectator => scatter (scatter 0 spectatorAxes spectator) selectedAxes localInput
  let term := fun localInput spectator => coeff selectedRow localInput * joint (reconstruct localInput spectator) reference
  have axes : (selectedAxes ++ spectatorAxes).Perm (List.range frame.length) := split_axes partition unique
  have ordered := List.nodup_append.mp (axes.symm.nodup List.nodup_range)
  have disjoint : spectatorAxes.Disjoint selectedAxes :=
    List.disjoint_left.mpr (fun axis right left => ordered.2.2 axis left axis right rfl)
  have inside : ∀ axis ∈ selectedAxes ++ spectatorAxes, axis < frame.length :=
    fun axis member => List.mem_range.mp (axes.subset member)
  have invert (input : Nat) (bound : input < 2^frame.length) :
      reconstruct (gather input selectedAxes) (gather input spectatorAxes) = input := by
    have spectatorFits : scatter 0 spectatorAxes (gather input spectatorAxes) < 2^frame.length :=
      Qleisli.Finite.Pull.scatter_bound _ _ _ _ (Nat.two_pow_pos _) (fun axis member =>
        inside axis (List.mem_append_right _ member))
    have fits : reconstruct (gather input selectedAxes) (gather input spectatorAxes) < 2^frame.length :=
      Qleisli.Finite.Pull.scatter_bound _ _ _ _ spectatorFits (fun axis member =>
        inside axis (List.mem_append_left _ member))
    apply (split_eq partition unique fits bound).mpr
    change (gather (reconstruct (gather input selectedAxes) (gather input spectatorAxes)) selectedAxes =
        gather input selectedAxes) ∧
      (gather (reconstruct (gather input selectedAxes) (gather input spectatorAxes)) spectatorAxes =
        gather input spectatorAxes)
    unfold reconstruct
    exact ⟨Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ ordered.1 (gather_bound _ _),
      (Qleisli.RuntimeTargetScatter.gather_disjoint _ _ _ _ disjoint).trans
        (Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ ordered.2.1 (gather_bound _ _))⟩
  calc
    _ = ((List.range (2^frame.length)).map fun input =>
        if spectatorRow = gather input spectatorAxes then
          term (gather input selectedAxes) (gather input spectatorAxes) else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro input member
      rw [show term (gather input selectedAxes) (gather input spectatorAxes) =
          coeff selectedRow (gather input selectedAxes) * joint input reference by
        simp only [term,invert input (List.mem_range.mp member)]]
    _ = ((List.range (2^spectators.length)).map fun spectator =>
        ((List.range (2^selected.length)).map fun localInput =>
          if spectatorRow = spectator then term localInput spectator else 0).sum).sum :=
      sum_split partition unique (fun localInput spectator =>
        if spectatorRow = spectator then term localInput spectator else 0)
    _ = _ := by
      calc
        _ = ((List.range (2^spectators.length)).map fun spectator =>
            if spectatorRow = spectator then ((List.range (2^selected.length)).map fun localInput =>
              term localInput spectator).sum else 0).sum := by
          apply Qleisli.Exact.sum_map_congr
          intro spectator _
          by_cases same : spectatorRow = spectator <;> simp [same]
        _ = _ := Qleisli.Exact.range_delta_sum _ _ _ spectatorBound

/-- Extend a selected computational-basis source action by identity on the
actual spectator ports. Both structural routes preserve the physical frames.
The checked returned axes select output rows in their written return order.
`coeff` keeps the phase of the independently proved selected source action. -/
theorem active_spectator_extension {Reference : Type}
    {dependencies program block start count entry places returned}
    {inner : @RuntimeInterval.Checked dependencies program block start count}
    (opening : RuntimeAccessPartition.ActiveEntry inner entry places)
    (closing : RuntimeAccessPartition.ActiveExit opening returned)
    (coeff : Nat → Nat → ℂ) (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference) :
    let inputFrame := opening.preamble.before.quantum.frame
    let outputFrame := closing.after.quantum.frame
    let spectators := WireOrder (opening.remainders.filterMap Prod.snd)
    let selectedAxes := (WireOrder opening.selected).map inputFrame.idxOf
    let spectatorAxes := spectators.map inputFrame.idxOf
    let selectedRow := gather row ((WireOrder returned).map outputFrame.idxOf)
    let spectatorRow := gather row (spectators.map outputFrame.idxOf)
    inner.before.quantum.frame = inputFrame ∧ outputFrame = inner.after.quantum.frame ∧
      ((List.range (2^inputFrame.length)).map fun input =>
        if spectatorRow = gather input spectatorAxes then
          coeff selectedRow (gather input selectedAxes) * joint input reference else 0).sum =
      ((List.range (2^(WireOrder opening.selected).length)).map fun input =>
        coeff selectedRow input *
          joint (scatter (scatter 0 spectatorAxes spectatorRow) selectedAxes input) reference).sum := by
  intro inputFrame outputFrame spectators selectedAxes spectatorAxes selectedRow spectatorRow
  obtain ⟨⟨_,_,_,inputSame⟩,⟨_,_,_,outputSame⟩⟩ :=
    Qleisli.Raw.AccessCommutation.active_routing_traces opening closing
  have actual := native_wires inner.before.quantum inner.history.1
  have ports := opening.partition.flatMap_right Semantics.Raw.Port.wires
  rw [List.flatMap_append] at ports
  have partition : inputFrame.Perm (WireOrder opening.selected ++ spectators) := by
    change opening.preamble.before.quantum.frame.Perm _
    rw [← inputSame]
    exact actual.symm.trans ports.symm
  have unique : inputFrame.Nodup := (QleisliKernel.Raw.Ownership.valid _ opening.preamble.history.1).frame
  refine ⟨inputSame,outputSame,?_⟩
  apply apply_selected_with_spectators partition unique coeff joint selectedRow spectatorRow reference
  simpa only [spectatorRow,List.length_map] using gather_bound row (spectators.map outputFrame.idxOf)

#print axioms active_literal_states
#print axioms enter_history_agrees
#print axioms exit_history_agrees
#print axioms exclusive_history_refines
#print axioms exclusive_step_refines
#print axioms evaluate_pure_access_refines
#print axioms active_spectator_extension
end Qleisli.RuntimeExclusiveCoordinates
