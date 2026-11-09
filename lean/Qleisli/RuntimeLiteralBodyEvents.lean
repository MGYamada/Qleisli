import Qleisli.RuntimeNamedChildRuns
import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeObservingPrefix

/-! Read the independent observing events of the exact checked body
partition. Neighbouring reads share the complete original Raw state.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimePureBody (Step)
open QleisliKernel.Semantics.Observation (Event readOps)

inductive Trace {dependencies program block} :
    Raw.Observation.State → List (@Step dependencies program block) → Raw.Observation.State → List Event → Prop where
  | nil (state : Raw.Observation.State) : Trace state [] state []
  | cons {first rest final earlier later}
      (read : readOps block.fuel (stepSpan first).checked.before.quantum.reference
        (stepSpan first).operations = some ((stepSpan first).checked.after.quantum.reference,earlier))
      (tail : Trace (stepSpan first).checked.after rest final later) :
      Trace (stepSpan first).checked.before (first::rest) final (earlier++later)

private theorem adjacent_spans {dependencies program block} (first next : @Span dependencies program block)
    (touches : first.stop = next.start) : first.checked.after = next.checked.before := by
  rcases first with ⟨start,count,first⟩
  rcases next with ⟨offset,size,next⟩
  change start+count = offset at touches
  subst offset
  exact RuntimeAdjacentSlices.adjacent first next

private theorem first_position {dependencies program block initial final first rest}
    (partition : @Partition dependencies program block initial (first::rest) final) :
    (stepSpan first).start = initial := by
  cases partition with
  | cons head _ => exact head.1

private theorem nil_positions {dependencies program block initial final}
    (partition : @Partition dependencies program block initial [] final) : initial = final := by
  cases partition
  rfl

private def firstState {dependencies program block}
    (steps : List (@Step dependencies program block)) (fallback : Raw.Observation.State) :
    Raw.Observation.State :=
  match steps with
  | [] => fallback
  | first::_ => (stepSpan first).checked.before

private theorem next_state {dependencies program block initial middle final first rest}
    (head : @At dependencies program block initial middle first)
    (tail : @Partition dependencies program block middle rest final)
    (last : RuntimeInterval.Checked block final 0) :
    (stepSpan first).checked.after = firstState rest last.before := by
  cases rest with
  | nil =>
    let boundary : Span block := ⟨final,0,last⟩
    exact adjacent_spans (stepSpan first) boundary (head.2.trans (nil_positions tail))
  | cons next rest =>
    exact adjacent_spans (stepSpan first) (stepSpan next) (head.2.trans (first_position tail).symm)

private theorem Partition.trace {dependencies program block initial final steps}
    (partition : @Partition dependencies program block initial steps final)
    (last : RuntimeInterval.Checked block final 0) :
    ∃ events, Trace (firstState steps last.before) steps last.before events := by
  induction partition with
  | nil => exact ⟨[],.nil _⟩
  | @cons initial middle final first rest head tail ih =>
    let span := stepSpan first
    obtain ⟨work,left,ran⟩ := span.checked.intervalRead
    obtain ⟨earlier,read⟩ := RuntimeObservingPrefix.checkOps_reference _ _ _ _ _ work left ran
    obtain ⟨later,restRead⟩ := ih last
    have adjacent := next_state head tail last
    exact ⟨earlier++later,.cons read (adjacent.symm ▸ restRead)⟩

/-- Concatenation keeps the independently read events in original order. -/
theorem Trace.read {dependencies program block initial final steps events}
    (trace : @Trace dependencies program block initial steps final events)
    (fuel : Nat) (depth : block.fuel = fuel+1) :
    readOps block.fuel initial.quantum.reference (steps.flatMap fun step => (stepSpan step).operations) =
      some (final.quantum.reference,events) := by
  induction trace with
  | nil =>
    rw [depth]
    rfl
  | cons first tail ih =>
    rw [depth] at first ih ⊢
    rw [List.flatMap_cons,RuntimeAdjacentSlices.readOps_append,first]
    change (do
      let (last,rest) ← readOps (fuel+1) _ _
      pure (last,_++rest)) = _
    rw [ih]
    rfl

private theorem at_zero {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (zero : start = 0) :
    interval.before = block.entry := by
  subst start
  have checked := interval.prefixRead
  simp only [List.take_zero] at checked
  cases depth : block.fuel with
  | zero =>
    rw [depth] at checked
    obtain ⟨_,_,impossible⟩ := checked
    cases impossible
  | succ fuel =>
    rw [depth] at checked
    obtain ⟨_,_,folded⟩ := RuntimeAdjacentSlices.underlying checked
    exact (pure_success _ _ _ _ folded).1

/-- The trace of the actual complete original body partitions into the same
steps the source traversal returned, from the original entry to its finish. -/
theorem Partition.original_trace {dependencies program block steps}
    (partition : @Partition dependencies program block 0 steps block.operations.length)
    (last : RuntimeInterval.Checked block block.operations.length 0) :
    ∃ events, Trace block.entry steps last.before events ∧
      readOps block.fuel block.entry.quantum.reference block.operations =
        some (last.before.quantum.reference,events) := by
  have starts : firstState steps last.before = block.entry := by
    cases steps with
    | nil => exact at_zero last (nil_positions partition).symm
    | cons first _ => exact at_zero (stepSpan first).checked (first_position partition)
  obtain ⟨events,trace⟩ := partition.trace last
  rw [starts] at trace
  refine ⟨events,trace,?_⟩
  cases depth : block.fuel with
  | zero =>
    have checked := last.prefixRead
    rw [depth] at checked
    obtain ⟨_,_,impossible⟩ := checked
    cases impossible
  | succ fuel =>
    have read := trace.read fuel depth
    rw [partition.operations,depth] at read
    exact read

#print axioms Partition.original_trace

/-- Use the actual root traversal and its own final boundary read. -/
theorem original_body_trace {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime) :
    let block := body.checked.native.block
    ∃ last : RuntimeInterval.Checked block block.operations.length 0,
      RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) last ∧
      ∃ events, Trace block.entry body.checked.result.steps last.before events ∧
        readOps block.fuel block.entry.quantum.reference block.operations =
          some (last.before.quantum.reference,events) := by
  obtain ⟨_,_,_,flow,last,lastRead,_⟩ := RuntimeNamedChildRuns.original_body body
  exact ⟨last,lastRead,flow.literal.original_trace last⟩

#print axioms original_body_trace
end Qleisli.RuntimeLiteralBody
