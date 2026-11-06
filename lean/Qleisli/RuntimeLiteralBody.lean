import QleisliKernel.Qirf.RuntimePureBody
import Qleisli.RuntimeAdjacentInterval

/-! Exact original operation ranges of the steps returned by the source body
traversal. A partition retains zero-length intervals and authentic Raw states.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBody
open QleisliKernel QleisliKernel.Qirf
open RuntimePureBody (Node Step)

structure Span {dependencies program} (block : RuntimeInterval.Block dependencies program) where
  start : Nat
  count : Nat
  checked : RuntimeInterval.Checked block start count

def Span.stop {dependencies program block} (span : @Span dependencies program block) : Nat :=
  span.start + span.count

def Span.operations {dependencies program block} (span : @Span dependencies program block) :
    List Semantics.Observation.Op :=
  (block.operations.drop span.start).take span.count

def nodeSpan {dependencies program block} : Node dependencies program block → Span block
  | .primitive action _ => ⟨_,_,action.interval.interval⟩
  | .structural action => ⟨_,_,action.interval⟩
  | .named _ frame _ _ _ _ => ⟨_,_,frame.interval⟩
  | .operation frame .. => ⟨_,_,frame.interval⟩
  | .selection frame .. => ⟨_,_,frame.interval⟩

def stepSpan {dependencies program block} : Step dependencies program block → Span block
  | .pure node => nodeSpan node
  | .gap gap => ⟨_,_,gap.checked.interval⟩
  | .observation observation => ⟨_,_,observation.checked.interval⟩
  | .named _ frame _ _ _ _ _ => ⟨_,_,frame.interval⟩
  | .conditional _ _ _ actual .. => ⟨_,_,actual.interval⟩

def At {dependencies program block} (start stop : Nat) (step : @Step dependencies program block) : Prop :=
  (stepSpan step).start = start ∧ (stepSpan step).stop = stop

inductive Partition {dependencies program block} :
    Nat → List (@Step dependencies program block) → Nat → Prop where
  | nil (cursor : Nat) : Partition cursor [] cursor
  | cons {initial middle final first rest}
      (head : At initial middle first) (tail : Partition middle rest final) :
      Partition initial (first :: rest) final

theorem Partition.snoc {dependencies program block initial middle final steps step}
    (partition : @Partition dependencies program block initial steps middle)
    (last : At middle final step) : Partition initial (steps ++ [step]) final := by
  induction partition with
  | nil => exact .cons last (.nil _)
  | cons head _ ih => exact .cons head (ih last)

/-- Concatenation of the checked ranges extends the literal Raw prefix. -/
theorem Partition.prefix_operations {dependencies program block initial final steps}
    (partition : @Partition dependencies program block initial steps final) :
    block.operations.take initial ++ steps.flatMap (fun step => (stepSpan step).operations) =
      block.operations.take final := by
  induction partition with
  | nil => simp
  | @cons initial middle final first rest head _ ih =>
    obtain ⟨start,stop⟩ := head
    rw [List.flatMap_cons,← List.append_assoc,← start]
    change (block.operations.take (stepSpan first).start ++
      (block.operations.drop (stepSpan first).start).take (stepSpan first).count) ++ _ = _
    rw [← RuntimeAdjacentSlices.prefixSplit,← Span.stop,stop,ih]

theorem Partition.operations {dependencies program block steps}
    (partition : @Partition dependencies program block 0 steps block.operations.length) :
    steps.flatMap (fun step => (stepSpan step).operations) = block.operations := by
  simpa using partition.prefix_operations

end Qleisli.RuntimeLiteralBody
