import Qleisli.RuntimeLiteralSparseNamed
import Qleisli.RuntimeSparseSelectionOutput
import Qleisli.RuntimeSourceOrdinalAction

/-! Follow the retained named selection through its original parent event
slice, keeping the actual visible SSA and inherited observation history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open Semantics.Observation (Event readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeLiteralHistory (Agrees)
open Qleisli.RuntimeLiteralBranchChoice (measurementBits)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory pureHistory_operator_congr run_pure)
open Qleisli.RuntimeNamedChildRuns (ChildRun OrdinaryAligned OrdinaryRun)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.RuntimeSparseSelectionOutput (callerAction callerUpdate actual_occurrence_whole_output)
open Qleisli.RuntimeMultiwayGram (sourceAction selector_card)
open Qleisli.RuntimeSemanticForest (action product)
open RuntimeSelectionPartition (complement)
open RuntimeNamedThreeOccurrence (Middle RetainedData)
open RuntimePureBody (Step Steps runBlockCore)

private def PureOnly {dependencies program block} : Steps dependencies program block → Prop
  | .nil => True
  | .cons (.pure _) rest => PureOnly rest
  | .cons _ _ => False

private theorem pure_steps_ordinary {dependencies program block initial steps final}
    (flow : @OrdinaryRun dependencies program block initial steps final)
    (onlyPure : PureOnly (Steps.ofList steps)) : final = initial := by
  induction flow with
  | nil => rfl
  | @cons initial middle final first rest head _ ih =>
    cases first
    case pure node => exact (ih onlyPure).trans head
    all_goals exact False.elim onlyPure

private theorem named_stepList_ofList {dependencies program block} (steps : List (Step dependencies program block)) :
    stepList (Steps.ofList steps) = steps := by
  induction steps with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons first) ih

private def NamedChildFlow {dependencies program block} : Step dependencies program block → Prop
  | .named _ scope _ _ _ final children =>
    Partition 0 (stepList children) scope.prepared.block.operations.length ∧
      (PureOnly children → final = scope.visible.ssa)
  | _ => True

private theorem named_child_flow {artifact root mode fuel program block step}
    (call : @ChildRun artifact root mode (runBlockCore artifact root mode (fuel+1)) program block step) :
    NamedChildFlow step := by
  cases call with
  | @named _ _ _ _ _ _ _ scope body _ _ _ path request plan _ result receipts _ _ afterInput afterChild _ childRead =>
    obtain ⟨_,_,_,flow,_⟩ := RuntimeNamedChildRuns.core_flow artifact root mode fuel
      .localScope (.whole body) path scope.program request plan _ scope.visible.ssa
      scope.prepared.block (result,receipts) ⟨afterInput,afterChild,childRead⟩
    exact ⟨by simpa only [named_stepList_ofList] using flow.literal,pure_steps_ordinary flow.ordinary⟩

private theorem singleton_at {dependencies program block start stop step}
    (partition : @Partition dependencies program block start [step] stop) : At start stop step := by
  cases partition with
  | cons head tail =>
    cases tail
    exact head

/-- The actual child has a single selection, so its retained interval is the
whole checked child block and covers the exact parent call slice. -/
theorem named_selection_coverage {artifact root mode fuel program block step rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness root.dependencies rootItem rootCount}
    (occurrence : @Middle root.dependencies program block step)
    (call : ChildRun artifact root mode (runBlockCore artifact root mode (fuel+1)) step)
    (held : RetainedData witness occurrence) : RuntimeNamedSelectionOn.Coverage occurrence held := by
  have flow := named_child_flow call
  cases occurrence with
  | @named start count args sources caller before child retired old event scope body bodyRead boundary final node selected =>
    have position := singleton_at (step := .pure node) flow.1
    dsimp only [RuntimeNamedSelectionOn.Coverage]
    cases held.literal with
    | @selection first size _ _ _ _ frame _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have atZero : first = 0 := position.1
      have stop : first+size = ((block.operations.drop start).take count).length := position.2
      change first = 0 ∧ size = ((block.operations.drop start).take count).length
      exact ⟨atZero,by simpa only [atZero,Nat.zero_add] using stop⟩

private theorem named_pure_history {dependencies program block start count args old effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count args old effect)
    (ops : List Semantics.Raw.Op)
    (literal : (block.operations.drop start).take count = ops.map Semantics.Observation.Op.pure)
    (rawEvents : List Semantics.Raw.Event)
    (traced : RuntimeLocalEvents.trace scope.interval.before.quantum.reference ops =
      some ⟨scope.interval.after.quantum.reference,rawEvents,scope.interval.before.quantum.frame.length⟩)
    (inputs : List Nat) (history : History)
    (agrees : Agrees inputs scope.interval.before old history)
    {chunk : List Event} {outputs : List History}
    (read : readOps block.fuel scope.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (scope.interval.after.quantum.reference,chunk))
    (executed : run dependencies block.fuel chunk history = some outputs) :
    outputs = [pureHistory dependencies rawEvents history] ∧
      Agrees inputs scope.interval.after scope.visible.ssa (pureHistory dependencies rawEvents history) := by
  have same : outputs = [pureHistory dependencies rawEvents history] := by
    cases depth : block.fuel with
    | zero =>
      rw [depth] at executed
      cases executed
    | succ depthFuel =>
      rw [literal,depth] at read
      have readPure := RuntimeAdjacentSlices.readOps_pure depthFuel _ _ _ traced
      have eventsEq : chunk = rawEvents.map Semantics.Observation.Event.pure :=
        congrArg Prod.snd (Option.some.inj (read.symm.trans readPure))
      rw [depth,eventsEq] at executed
      exact Option.some.inj (executed.symm.trans (run_pure dependencies depthFuel rawEvents history))
  refine ⟨same,?_,?_⟩
  · intro id expression member
    change (id,expression) ∈ scope.visible.table at member
    rw [scope.visible.original] at member
    exact agrees.1 id expression (List.mem_filter.mp member).1
  · obtain ⟨work,left,intervalRead⟩ := scope.interval.intervalRead
    have issued := (Raw.Observation.checkOps_history _ _ _ _ _ _ _ intervalRead).2.2
    intro id member
    exact Qleisli.RuntimeObservingPrefix.issued_mono issued (agrees.2 member)

/-- The source update uses the actual occurrence's ordered selected arguments
and original source table. Its evaluator uses only source coordinates. -/
noncomputable def sourceNamedSelection {dependencies program block step}
    (occurrence : @Middle dependencies program block step)
    (source : SourceHistory) : List SourceHistory := by
  cases occurrence with
  | @named start count args sources caller before child retired old event scope body bodyRead boundary final node selected =>
    cases node with
    | selection frame selectorBits targetBits retained restricted inputCode outputCode labels arms logical equations codes layouts =>
      let selected := boundary.input.ordered
      let spectators := complement before.bindings selected
      let operator := callerAction codes.owners.transport.after.bindings before.bindings (selected++spectators)
        child.bindings boundary.afterFrame.bindings (boundary.mapped++spectators) (product selected).labels.length
        (product boundary.mapped).labels.length (Qleisli.RuntimeSourceOrdinalAction.sourceAction
          codes.owners.transport.after.bindings codes.owners.returned.first codes.owners.returned.second arms)
        source.operator
      exact [{source with owners := boundary.after, operator}]
    | primitive _ _ => exact False.elim selected
    | structural _ => exact False.elim selected
    | named _ _ _ _ _ _ => exact False.elim selected
    | operation _ _ _ _ _ _ _ _ _ _ => exact False.elim selected

noncomputable def withSparseSelection {dependencies program block}
    (fallback : List (Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (Step dependencies program block)) (step : Step dependencies program block)
    (source : SourceHistory) : Option (List SourceHistory) :=
  match RuntimeNamedThreeOccurrence.middle? step with
  | some occurrence => some (sourceNamedSelection occurrence source)
  | none => fallback prior step source

/-- The actual selected child updates the same sparse history used by its
caller's other original steps. The source table, literal events, output
owner order, visible SSA and inherited outcomes are tied to one occurrence. -/
theorem sparse_named_selection_refines {artifact root mode fuel program block step rootItem rootCount}
    {witness : @RuntimeSelectionSteps.Witness root.dependencies rootItem rootCount}
    (occurrence : @Middle root.dependencies program block step)
    (call : ChildRun artifact root mode (runBlockCore artifact root mode (fuel+1)) step)
    (held : RetainedData witness occurrence)
    (inputs : List Nat) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter step) (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter step)
    {chunk source history outputs}
    (read : readOps block.fuel (stepSpan step).checked.before.quantum.reference (stepSpan step).operations =
      some ((stepSpan step).checked.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgrees inputs (stepSpan step).checked.before ownerBefore ordinaryBefore source history)
    (executed : run root.dependencies block.fuel chunk history = some outputs) :
    List.Forall₂ (SemanticHistoryAgrees inputs (stepSpan step).checked.after ownerAfter ordinaryAfter)
      (sourceNamedSelection occurrence source) outputs := by
  have flow := named_child_flow call
  have coverage := named_selection_coverage occurrence call held
  cases occurrence with
  | @named start count args sources caller before child retired old event scope body bodyRead boundary final node selected =>
    let occurrence := Middle.named (read := bodyRead) (boundary := boundary) (finalOrdinary := final) node selected
    let span := RuntimeNamedSelectionOn.middle occurrence held coverage
    have literal : (block.operations.drop start).take count = span.slice.ops.map Semantics.Observation.Op.pure :=
      span.slice.literal
    obtain ⟨rawEvents,_,traced⟩ := (RuntimeIntervalRawFold.mixed_call_traces scope span.slice.ops literal).1
    have on := RuntimeNamedSelectionOn.on_middle occurrence held coverage rawEvents traced
    have whole := actual_occurrence_whole_output occurrence call held coverage rawEvents on
    have bounded : RawFiniteRows.BoundedEvents scope.interval.before.quantum.frame.length rawEvents
        scope.interval.after.quantum.frame.length := RawFiniteRows.checked_slice span.slice rawEvents traced
    rcases owners with ⟨rfl,rfl⟩
    rcases ordinary with ⟨rfl,rfl⟩
    obtain ⟨_,hidden,bits,values,_,checked,bindings,input,represented⟩ := agrees
    let orderedInput := bindings.symm ▸ input
    have representedInput := cast_represents bindings.symm input
      (state := scope.interval.before) (history := history) (operator := source.operator) represented
    obtain ⟨rfl,agreesAfter⟩ := named_pure_history scope span.slice.ops literal rawEvents traced
      inputs history values read executed
    have finalEq : ordinaryAfter = scope.visible.ssa := flow.2 True.intro
    dsimp only [occurrence,RuntimeSparseSelectionOutput.OccurrenceWholeOutput] at whole
    cases stored : held.literal with
    | @selection first size localInputs outputs selector target frame selectorBits targetBits retained restricted
        inputCode outputCode labels expected logical equations codes layouts localLiteral nativeRead =>
      rw [stored] at whole
      obtain ⟨_,output,table,law⟩ := whole checked orderedInput bindings
      let spectators := complement ownerBefore.bindings boundary.input.ordered
      let operator := callerAction codes.owners.transport.after.bindings ownerBefore.bindings (boundary.input.ordered++spectators)
        child.bindings boundary.afterFrame.bindings (boundary.mapped++spectators)
        (product boundary.input.ordered).labels.length (product boundary.mapped).labels.length
        (Qleisli.RuntimeSourceOrdinalAction.sourceAction codes.owners.transport.after.bindings
          codes.owners.returned.first codes.owners.returned.second expected) source.operator
      let result := pureHistory root.dependencies rawEvents history
      have representedOutput : Qleisli.RuntimeStructuralHistory.Represents output scope.interval.after result operator := by
        intro column row boundRow
        have actual := pureHistory_operator_congr bounded root.dependencies history
          (fun row col => action orderedInput scope.interval.before.quantum.frame source.operator row col)
          representedInput column row boundRow
        apply actual.trans
        have same : callerUpdate localLiteral.outputCode checked.bindings
            (boundary.input.ordered++complement checked.bindings boundary.input.ordered)
            child.bindings boundary.afterFrame.bindings
            (boundary.mapped++complement checked.bindings boundary.input.ordered)
            (product boundary.input.ordered).labels.length (product boundary.mapped).labels.length
            (sourceAction frame codes layouts localLiteral table) source.operator = operator := by
          have childAction :
              (fun (joint : Nat → Nat → ℂ) =>
                Qleisli.RuntimeNamedSelectionWholeOutput.onFinite (sourceAction frame codes layouts localLiteral table joint)) =
              Qleisli.RuntimeSourceOrdinalAction.sourceAction codes.owners.transport.after.bindings
                codes.owners.returned.first codes.owners.returned.second expected := by
            funext joint
            exact Qleisli.RuntimeSourceOrdinalAction.onFinite_ordinalAction localLiteral.outputCode _ _ _
              table (selector_card frame codes layouts localLiteral) joint
          unfold callerUpdate operator spectators
          rw [childAction]
          rw [bindings]
        rw [← same]
        exact law source.operator row column
      change List.Forall₂ _ (sourceNamedSelection occurrence source) _
      change List.Forall₂ _ [{source with owners := boundary.after, operator}] _
      refine .cons ⟨rfl,hidden,?_,finalEq.symm ▸ agreesAfter,_,boundary.afterFrame,boundary.sameAfter,
        boundary.sameAfter ▸ output,cast_represents boundary.sameAfter output
          (state := scope.interval.after) (history := result) (operator := operator) representedOutput⟩ .nil
      change measurementBits ordinaryAfter.measurements history.values = _
      rw [finalEq,scope.visible.measurements]
      exact bits

/-- The source prefix selects the very same occurrence in the original root
traversal and in its retained selection witness. -/
theorem original_body_sparse_selection_refines {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (prior later : List (Step body.root.dependencies body.root.program body.checked.native.block))
    {step : Step body.root.dependencies body.root.program body.checked.native.block}
    (occurrence : Middle step)
    (position : body.checked.result.steps = prior ++ step :: later)
    (inputs : List Nat) {ownerBefore ownerAfter ordinaryBefore ordinaryAfter}
    (owners : Aligned ownerBefore ownerAfter step) (ordinary : OrdinaryAligned ordinaryBefore ordinaryAfter step)
    {chunk source history outputs}
    (read : readOps body.checked.native.block.fuel (stepSpan step).checked.before.quantum.reference
      (stepSpan step).operations = some ((stepSpan step).checked.after.quantum.reference,chunk))
    (agrees : SemanticHistoryAgrees inputs (stepSpan step).checked.before ownerBefore ordinaryBefore source history)
    (executed : run body.root.dependencies body.checked.native.block.fuel chunk history = some outputs) :
    List.Forall₂ (SemanticHistoryAgrees inputs (stepSpan step).checked.after ownerAfter ordinaryAfter)
      (sourceNamedSelection occurrence source) outputs := by
  obtain ⟨_,_,_,flow,_⟩ := RuntimeNamedChildRuns.original_body body
  have checked := flow.calls step (by rw [position]; exact List.mem_append_right _ List.mem_cons_self)
  cases occurrence with
  | @named start count args sources caller before child retired old event scope childBody childRead
      boundary final node selected =>
    exact sparse_named_selection_refines (fuel := 126)
      (Middle.named (read := childRead) (boundary := boundary) (finalOrdinary := final) node selected)
      checked (RuntimeNamedThreeOccurrence.actual_body_selection body prior later
        (Middle.named (read := childRead) (boundary := boundary) (finalOrdinary := final) node selected) position)
      inputs owners ordinary read agrees executed

#print axioms named_selection_coverage
#print axioms sparse_named_selection_refines
#print axioms original_body_sparse_selection_refines
end Qleisli.RuntimeLiteralBody
