import Qleisli.RuntimeAdjacentInterval

/-! Complete boundary states of the same original checked interval agree
independently of successful starting/remaining work. The erased empty checks
are derived at zero charge; no nonempty runtime receipt is fabricated.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeIntervalStates
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite

theorem empty_read (dependencies : List Semantics.Finite.Dependency) (fuel : Nat)
    (state : Raw.Observation.State) (valid : Raw.stateValid state.quantum = true) :
    RuntimeInterval.Computed (Raw.Observation.checkOps dependencies (fuel+1) state []) state := by
  refine ⟨0,0,?_⟩
  have history : Raw.Observation.history state state = true := by
    simp [Raw.Observation.history_eq,List.all_eq_true]
  simp [Raw.Observation.checkOps,List.foldlM_nil,valid,history,Finite.guard]
  rfl

/-- Existing successful checks of the same original prefix have the same
complete state, independently of their successful starting/remaining budgets.
No claim about matching failures or available work is made. -/
theorem same_before {dependencies program block start firstCount secondCount}
    (first : @RuntimeInterval.Checked dependencies program block start firstCount)
    (second : RuntimeInterval.Checked block start secondCount) : first.before = second.before := by
  cases depth : block.fuel with
  | zero =>
    obtain ⟨work,left,read⟩ := first.prefixRead
    rw [depth] at read
    cases read
  | succ fuel =>
    obtain ⟨work,left,read⟩ := first.prefixRead
    have valid := (Raw.Observation.checkOps_invariants _ _ _ _ _ work left read).1
    let checkpoint : RuntimeInterval.Checked block start 0 :=
      { range := by have bounded := first.range; omega
        before := first.before
        prefixRead := first.prefixRead
        after := first.before
        intervalRead := by
          simpa only [List.take_zero,depth] using empty_read dependencies fuel first.before valid }
    exact RuntimeAdjacentSlices.adjacent checkpoint second

theorem prefix_unique {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start : Nat) (range : start ≤ block.operations.length) (first second : Raw.Observation.State)
    (left : RuntimeInterval.Computed
      (Raw.Observation.checkOps dependencies block.fuel block.entry (block.operations.take start)) first)
    (right : RuntimeInterval.Computed
      (Raw.Observation.checkOps dependencies block.fuel block.entry (block.operations.take start)) second) :
    first = second := by
  cases depth : block.fuel with
  | zero =>
    obtain ⟨work,left,read⟩ := left
    rw [depth] at read
    cases read
  | succ fuel =>
    obtain ⟨leftWork,leftRest,leftRead⟩ := left
    obtain ⟨rightWork,rightRest,rightRead⟩ := right
    have leftValid := (Raw.Observation.checkOps_invariants _ _ _ _ _ leftWork leftRest leftRead).1
    have rightValid := (Raw.Observation.checkOps_invariants _ _ _ _ _ rightWork rightRest rightRead).1
    let firstCheckpoint : RuntimeInterval.Checked block start 0 :=
      { range := by simpa only [Nat.add_zero] using range
        before := first
        prefixRead := ⟨leftWork,leftRest,leftRead⟩
        after := first
        intervalRead := by simpa only [List.take_zero,depth] using empty_read dependencies fuel first leftValid }
    let secondCheckpoint : RuntimeInterval.Checked block start 0 :=
      { range := by simpa only [Nat.add_zero] using range
        before := second
        prefixRead := ⟨rightWork,rightRest,rightRead⟩
        after := second
        intervalRead := by simpa only [List.take_zero,depth] using empty_read dependencies fuel second rightValid }
    exact same_before firstCheckpoint secondCheckpoint

/-- Both complete boundary states belong to the SAME original interval.
The proof uses the existing literal child block and its two actual nonempty
reads; only the erased zero-length checkpoints are derived separately. -/
theorem same_after {dependencies program block start count}
    (first second : @RuntimeInterval.Checked dependencies program block start count) :
    first.after = second.after := by
  have before := same_before first second
  let child := first.block
  have left : RuntimeInterval.Computed
      (Raw.Observation.checkOps dependencies child.fuel child.entry
        (child.operations.take child.operations.length)) first.after := by
    simpa only [child,RuntimeInterval.Checked.block,List.take_length] using first.intervalRead
  have right : RuntimeInterval.Computed
      (Raw.Observation.checkOps dependencies child.fuel child.entry
        (child.operations.take child.operations.length)) second.after := by
    have read := second.intervalRead
    rw [← before] at read
    simpa only [child,RuntimeInterval.Checked.block,List.take_length] using read
  exact prefix_unique child child.operations.length (Nat.le_refl _) first.after second.after left right

#print axioms same_before
#print axioms same_after
end Qleisli.RuntimeIntervalStates
