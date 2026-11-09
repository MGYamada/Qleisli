import Qleisli.RuntimeLiteralBodyEvents
import Qleisli.RuntimeObservingComposition
import Qleisli.HierarchicalSemantics

/-! Group the actual observing run by the original source body's checked
intervals. Each result comes from an actual run on an inherited history.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (Event readOps)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeObservingComposition (runHistories runHistories_append runHistories_nil runHistories_singleton)
open RuntimePureBody (Step)
open Qleisli.RuntimeNamedChildRuns (OrdinaryAligned OrdinaryRun)
open Qleisli.RuntimeNamedSourceFlow (Aligned)
open Qleisli.HierarchicalSemantics (mapM_members)

inductive Execution {dependencies program block} :
    Raw.Observation.State → List (@Step dependencies program block) → Raw.Observation.State →
      List Event → List History → List History → Prop where
  | nil (state : Raw.Observation.State) (histories : List History) : Execution state [] state [] histories histories
  | cons {first rest final earlier later incoming groups results}
      (read : readOps block.fuel (stepSpan first).checked.before.quantum.reference
        (stepSpan first).operations = some ((stepSpan first).checked.after.quantum.reference,earlier))
      (executed : incoming.mapM (run dependencies block.fuel earlier) = some groups)
      (tail : Execution (stepSpan first).checked.after rest final later groups.flatten results) :
      Execution (stepSpan first).checked.before (first::rest) final (earlier++later) incoming results

theorem Trace.executes {dependencies program block initial final steps events}
    (trace : @Trace dependencies program block initial steps final events)
    (fuel : Nat) (depth : block.fuel = fuel+1) {incoming results : List History}
    (ran : runHistories dependencies block.fuel events incoming = some results) :
    Execution initial steps final events incoming results := by
  induction trace generalizing incoming with
  | nil state =>
    rw [depth,runHistories_nil] at ran
    cases ran
    exact .nil state _
  | @cons first rest final earlier later read tail ih =>
    rw [depth,runHistories_append,← depth] at ran
    cases grouped : incoming.mapM (run dependencies block.fuel earlier) with
    | none => simp [runHistories,grouped] at ran
    | some groups =>
      have suffix : runHistories dependencies block.fuel later groups.flatten = some results := by
        simpa only [runHistories,grouped,bind,pure,Option.bind] using ran
      exact .cons read grouped (ih suffix)

theorem Execution.runHistories_eq {dependencies program block initial final steps events incoming results}
    (execution : @Execution dependencies program block initial steps final events incoming results)
    (fuel : Nat) (depth : block.fuel = fuel+1) :
    runHistories dependencies block.fuel events incoming = some results := by
  induction execution with
  | nil state histories => rw [depth,runHistories_nil]
  | cons read executed tail ih =>
    rw [depth,runHistories_append,← depth]
    simpa only [runHistories,executed,bind,pure,Option.bind] using ih

/-- A local law for each original step transports an invariant along the
same source-owner and ordinary-state chains and every actual output history. -/
theorem Execution.invariant {dependencies program block initial final steps events incoming results}
    (execution : @Execution dependencies program block initial steps final events incoming results)
    {ownerStart ownerEnd : RuntimeStructuralAction.SourceState}
    {ordinaryStart ordinaryEnd : RuntimeOrdinaryBody.State}
    (owners : RuntimeNamedSourceFlow.Run ownerStart steps ownerEnd)
    (ordinary : OrdinaryRun ordinaryStart steps ordinaryEnd)
    (property : Raw.Observation.State → RuntimeStructuralAction.SourceState → RuntimeOrdinaryBody.State →
      History → Prop)
    (localLaw : ∀ first ∈ steps, ∀ {ownerBefore ownerAfter ordinaryBefore ordinaryAfter},
      Aligned ownerBefore ownerAfter first → OrdinaryAligned ordinaryBefore ordinaryAfter first →
      ∀ {chunk}, readOps block.fuel (stepSpan first).checked.before.quantum.reference
        (stepSpan first).operations = some ((stepSpan first).checked.after.quantum.reference,chunk) →
      ∀ {history outputs}, property (stepSpan first).checked.before ownerBefore ordinaryBefore history →
        run dependencies block.fuel chunk history = some outputs →
        ∀ output ∈ outputs, property (stepSpan first).checked.after ownerAfter ordinaryAfter output)
    (starts : ∀ history ∈ incoming, property initial ownerStart ordinaryStart history) :
    ∀ history ∈ results, property final ownerEnd ordinaryEnd history := by
  induction execution generalizing ownerStart ownerEnd ordinaryStart ordinaryEnd with
  | nil =>
    cases owners
    cases ordinary
    exact starts
  | @cons first rest final earlier later incoming groups results read executed tail ih =>
    cases owners with
    | cons ownerStep ownerTail =>
      cases ordinary with
      | cons ordinaryStep ordinaryTail =>
        apply ih ownerTail ordinaryTail (fun next member => localLaw next (List.mem_cons_of_mem _ member))
        intro output member
        obtain ⟨group,present,contains⟩ := List.mem_flatten.mp member
        obtain ⟨history,input,performed⟩ := mapM_members _ _ _ executed group present
        exact localLaw first List.mem_cons_self ownerStep ordinaryStep read
          (starts history input) performed output contains

/-- Successful independent execution of the original program body supplies
the per-step executions, with its actual native entry and final boundary. -/
theorem original_body_execution {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (initial : History) (results : List History)
    (executed : let block := body.checked.native.block
      (do
        let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
        run body.root.dependencies block.fuel events initial) = some results) :
    let block := body.checked.native.block
    ∃ last : RuntimeInterval.Checked block block.operations.length 0,
      RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
      ∃ events, readOps block.fuel block.entry.quantum.reference block.operations =
        some (last.before.quantum.reference,events) ∧
        Execution block.entry body.checked.result.steps last.before events [initial] results := by
  obtain ⟨last,checked,events,trace,read⟩ := original_body_trace body
  let block := body.checked.native.block
  have ran : run body.root.dependencies block.fuel events initial = some results := by
    change (do
      let (_,events) ← readOps block.fuel block.entry.quantum.reference block.operations
      run body.root.dependencies block.fuel events initial) = _ at executed
    rw [read] at executed
    exact executed
  refine ⟨last,checked,events,read,?_⟩
  cases depth : block.fuel with
  | zero =>
    rw [depth] at ran
    cases ran
  | succ fuel =>
    apply trace.executes fuel depth
    rw [runHistories_singleton]
    exact ran

#print axioms Execution.invariant
#print axioms original_body_execution
end Qleisli.RuntimeLiteralBody
