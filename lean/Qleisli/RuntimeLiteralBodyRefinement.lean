import Qleisli.RuntimeLiteralBodyExecution
import Mathlib.Data.List.Forall2

/-! Relate complete ordered source results to the actual original-body run.
The source step and its refinement law both see the exact prefix of checked
steps. They can distinguish occurrences with identical owner and SSA states.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeNamedChildRuns (CheckedStep OrdinaryAligned OrdinaryRun)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open RuntimePureBody (Step)

/-- Evaluate the source histories in order, extending the exact prefix at each
step. Branch-specific information belongs to the source history. -/
def runSourceHistories {dependencies program block} {SourceHistory : Type}
    (next : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (prior : List (@Step dependencies program block)) :
    List (@Step dependencies program block) → List SourceHistory → Option (List SourceHistory)
  | [], histories => some histories
  | first :: rest, histories => do
    let groups ← histories.mapM (next prior first)
    runSourceHistories next (prior ++ [first]) rest groups.flatten

private theorem relatedGroups {SourceHistory : Type}
    {before after : SourceHistory → History → Prop}
    {source : SourceHistory → Option (List SourceHistory)}
    {literal : History → Option (List History)}
    {sources incoming groups}
    (related : List.Forall₂ before sources incoming)
    (executed : incoming.mapM literal = some groups)
    (localLaw : ∀ {expected actual outputs}, before expected actual → literal actual = some outputs →
      ∃ result, source expected = some result ∧ List.Forall₂ after result outputs) :
    ∃ results, sources.mapM source = some results ∧ List.Forall₂ (List.Forall₂ after) results groups := by
  induction related generalizing groups with
  | nil =>
    cases executed
    exact ⟨[], rfl, .nil⟩
  | @cons expected actual sources incoming pair tail ih =>
    cases step : literal actual with
    | none => simp [List.mapM_cons, step] at executed
    | some outputs =>
      cases rest : incoming.mapM literal with
      | none => simp [List.mapM_cons, step, rest] at executed
      | some groups =>
        simp [List.mapM_cons, step, rest] at executed
        cases executed
        obtain ⟨result, sourceStep, relatedStep⟩ := localLaw pair step
        obtain ⟨results, sourceTail, relatedTail⟩ := ih rest
        exact ⟨result :: results, by simp [List.mapM_cons, sourceStep, sourceTail],
          .cons relatedStep relatedTail⟩

/-- A local refinement law may use the checked child execution for the exact
occurrence. The original list decomposition fixes its position even when two
occurrences have the same Raw bounds. -/
def StepRefinement {dependencies program block} {SourceHistory : Type}
    (steps : List (@Step dependencies program block))
    (certifies : Step dependencies program block → Prop)
    (next : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (related : List (@Step dependencies program block) → Raw.Observation.State →
      RuntimeStructuralAction.SourceState → RuntimeOrdinaryBody.State → SourceHistory → History → Prop) : Prop :=
  ∀ earlier first later, earlier ++ (first :: later) = steps → certifies first →
    ∀ {ownerBefore ownerAfter ordinaryBefore ordinaryAfter},
    Aligned ownerBefore ownerAfter first → OrdinaryAligned ordinaryBefore ordinaryAfter first →
    ∀ {chunk}, readOps block.fuel (stepSpan first).checked.before.quantum.reference
      (stepSpan first).operations = some ((stepSpan first).checked.after.quantum.reference,chunk) →
    ∀ {expected actual outputs},
      related earlier (stepSpan first).checked.before ownerBefore ordinaryBefore expected actual →
      run dependencies block.fuel chunk actual = some outputs →
      ∃ expectedOutputs, next earlier first expected = some expectedOutputs ∧
        List.Forall₂ (related (earlier ++ [first]) (stepSpan first).checked.after ownerAfter ordinaryAfter)
          expectedOutputs outputs

/-- Transport an exact prefix-indexed law along the same checked intervals,
owner states and ordinary states as the actual execution. The result lists
retain both order and multiplicity. -/
theorem Execution.ordered_refinement {dependencies program block initial final steps events incoming results}
    (execution : @Execution dependencies program block initial steps final events incoming results)
    {ownerStart ownerEnd : RuntimeStructuralAction.SourceState}
    {ordinaryStart ordinaryEnd : RuntimeOrdinaryBody.State}
    (owners : RuntimeNamedSourceFlow.Run ownerStart steps ownerEnd)
    (ordinary : OrdinaryRun ordinaryStart steps ordinaryEnd)
    {SourceHistory : Type} {sourceIncoming : List SourceHistory}
    (next : List (@Step dependencies program block) → Step dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (related : List (@Step dependencies program block) → Raw.Observation.State →
      RuntimeStructuralAction.SourceState → RuntimeOrdinaryBody.State → SourceHistory → History → Prop)
    (prior : List (@Step dependencies program block))
    (certifies : Step dependencies program block → Prop)
    (checked : ∀ first ∈ steps, certifies first)
    (localLaw : StepRefinement (prior ++ steps) certifies next related)
    (starts : List.Forall₂ (related prior initial ownerStart ordinaryStart) sourceIncoming incoming) :
    ∃ expectedResults, runSourceHistories next prior steps sourceIncoming = some expectedResults ∧
      List.Forall₂ (related (prior ++ steps) final ownerEnd ordinaryEnd) expectedResults results := by
  induction execution generalizing prior ownerStart ownerEnd ordinaryStart ordinaryEnd sourceIncoming with
  | nil =>
    cases owners
    cases ordinary
    exact ⟨sourceIncoming, rfl, by simpa using starts⟩
  | @cons first rest final earlier later incoming groups results read executed tail ih =>
    cases owners with
    | cons ownerStep ownerTail =>
      cases ordinary with
      | cons ordinaryStep ordinaryTail =>
        obtain ⟨sourceGroups, sourceStep, grouped⟩ :=
          relatedGroups starts executed
            (localLaw prior first rest rfl (checked first List.mem_cons_self) ownerStep ordinaryStep read)
        have same : (prior ++ [first]) ++ rest = prior ++ (first :: rest) := by
          simp [List.append_assoc]
        obtain ⟨expected, sourceTail, aligned⟩ :=
          ih ownerTail ordinaryTail (prior ++ [first])
            (fun current member => checked current (List.mem_cons_of_mem _ member))
            (fun preceding current remaining position =>
              localLaw preceding current remaining (position.trans same))
            (List.rel_flatten grouped)
        exact ⟨expected, by simpa [runSourceHistories, sourceStep] using sourceTail,
          by simpa only [same] using aligned⟩

/-- Reuse the ordered induction on any complete original block traversal.
The independently read Raw execution uses the actual partition and receipts. -/
theorem refineFlow {artifact root mode next program block start finish steps initialOrdinary finalOrdinary}
    (flow : @RuntimeNamedChildRuns.Flow artifact root mode next program block start steps finish
      initialOrdinary finalOrdinary block.operations.length)
    (last : RuntimeInterval.Checked block block.operations.length 0)
    {SourceHistory : Type} (sourceInitial : SourceHistory) (initial : History) {results : List History}
    (sourceStep : List (Step root.dependencies program block) → Step root.dependencies program block →
      SourceHistory → Option (List SourceHistory))
    (related : List (Step root.dependencies program block) → Raw.Observation.State →
      RuntimeStructuralAction.SourceState → RuntimeOrdinaryBody.State → SourceHistory → History → Prop)
    (executed : (do
      let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
      run root.dependencies block.fuel events initial) = some results)
    (law : StepRefinement steps (CheckedStep next) sourceStep related)
    (starts : related [] block.entry start initialOrdinary sourceInitial initial) :
    ∃ expected, runSourceHistories sourceStep [] steps [sourceInitial] = some expected ∧
      List.Forall₂ (related steps last.before finish finalOrdinary) expected results := by
  obtain ⟨events,trace,read⟩ := flow.literal.original_trace last
  rw [read] at executed
  exact (trace.executes_singleton executed).ordered_refinement flow.source flow.ordinary sourceStep related [] _
    flow.calls law (.cons starts .nil)

/-- Specialize the ordered proof to the real body. The same traversal supplies
the child receipts, the owner and SSA chains, the input ordering, and the
return ordering that follows the last literal step. -/
theorem original_body_ordered_refinement {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    {SourceHistory : Type} (sourceInitial : SourceHistory) (initial : History) (results : List History)
    (next : List (Step body.root.dependencies body.root.program body.checked.native.block) →
      Step body.root.dependencies body.root.program body.checked.native.block →
      SourceHistory → Option (List SourceHistory))
    (related : List (Step body.root.dependencies body.root.program body.checked.native.block) →
      Raw.Observation.State → RuntimeStructuralAction.SourceState → RuntimeOrdinaryBody.State →
      SourceHistory → History → Prop)
    (executed : let block := body.checked.native.block
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run body.root.dependencies block.fuel events initial) = some results) :
    let block := body.checked.native.block
    let source := SourceTypes.SourceRuntimeScope.Subject.whole prepared.source.body
    let mode := RuntimePureBody.ExecutionMode.planned
      (RuntimeBodyOperations.preparation artifact prepared.source.catalogue)
      (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)
    let history := RuntimeBodyOperations.initialHistory prepared body.checked.native runtime body.checked.inputs
    StepRefinement body.checked.result.steps (CheckedStep (RuntimePureBody.runBlockCore artifact body.root mode 127))
      next related →
    (∀ input : RuntimeOwnerMap.Checked source.initialRoles block.entry,
      RuntimeInterval.Computed (RuntimePureBody.reordered source.initialRoles block.entry history.bindings) input →
      related [] block.entry {history with bindings := input.bindings} body.checked.initial.ssa sourceInitial initial) →
    ∃ ownerEnd : RuntimeStructuralAction.SourceState,
    ∃ last : RuntimeInterval.Checked block block.operations.length 0,
      RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
      (∃ returned : RuntimeOwnerMap.Checked source.outputRoles last.after,
        RuntimeInterval.Computed (RuntimePureBody.reordered source.outputRoles last.after ownerEnd.bindings) returned ∧
        body.checked.result.history = {ownerEnd with bindings := returned.bindings}) ∧
      ∃ expected, runSourceHistories next [] body.checked.result.steps [sourceInitial] = some expected ∧
        List.Forall₂ (related body.checked.result.steps last.before ownerEnd body.checked.result.ordinary)
          expected results := by
  intro block source mode history localLaw starts
  obtain ⟨input,inputRead,ownerEnd,flow,last,lastRead,returned⟩ := RuntimeNamedChildRuns.original_body body
  exact ⟨ownerEnd,last,lastRead,returned,
    refineFlow flow last sourceInitial initial next related executed localLaw (starts input inputRead)⟩

#print axioms Execution.ordered_refinement
#print axioms original_body_ordered_refinement
end Qleisli.RuntimeLiteralBody
