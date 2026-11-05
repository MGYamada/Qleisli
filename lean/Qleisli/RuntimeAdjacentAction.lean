import Qleisli.RuntimeAdjacentInterval
import Qleisli.RuntimeIntervalRawFold
import Qleisli.RawActionComposition

/-! Original pure intervals in one mixed parent. Their literal parent fold
accumulates all emitted events in order. Each independent trace matches its
own successful receipt. Parent output finalization is a separate operation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeAdjacentSlices
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite

abbrev Event := Semantics.Raw.Event
abbrev RawOp := Semantics.Raw.Op
abbrev Interval {deps program} (block : RuntimeInterval.Block deps program) (start size : Nat) :=
  RuntimeInterval.Checked block start size

structure Slice {deps program} (block : RuntimeInterval.Block deps program) (start size : Nat) where
  interval : Interval block start size
  ops : List RawOp
  literal : (block.operations.drop start).take size = ops.map Semantics.Observation.Op.pure

/-- Project a genuine pure named call onto its interval in the parent block. -/
def Slice.ofNamed {deps program block start size inputs}
    (scope : @RuntimeCallInterval.Checked deps program block start size inputs) : Slice block start size :=
  ⟨scope.interval,scope.operations,scope.literal⟩

/-- The existing sector reader identifies pure operations in the original mixed
call slice. Its successful result supplies the exact parent interval. -/
def Slice.ofMixedNamed {deps program block start size inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked deps program block start size inputs ordinary effect)
    (ops : List RawOp) (read : Sector.pureOps ((block.operations.drop start).take size) = some ops) :
    Slice block start size :=
  ⟨scope.interval,ops,Sector.pureOps_bound _ _ read⟩

/-- Ordinary successful step receipts over this slice. No synthetic finish. -/
def Fold (signatures : List Basis) (ops : List RawOp) (before after : Raw.State)
    (events : List Event) : Prop :=
  ops.foldlM (Raw.advance signatures) ⟨before,[],before.frame.length⟩ =
    .ok ⟨after,events,before.frame.length⟩

/-- Both receipts identify the same emitted events. This connects an interval
in the parent trace to the event list in a source-action theorem. -/
theorem Fold.events_unique {signatures ops before after otherAfter x y}
    (left : Fold signatures ops before after x) (right : Fold signatures ops before otherAfter y) : x = y :=
  congrArg Raw.Prepared.events (Except.ok.inj (left.symm.trans right))

private theorem sliceFold {deps program block start size} (slice : @Slice deps program block start size) :
    ∃ events, Fold (deps.map (·.signature)) slice.ops slice.interval.before.quantum slice.interval.after.quantum events := by
  obtain ⟨w,l,ran⟩ := slice.interval.intervalRead
  rw [slice.literal] at ran
  exact RuntimeIntervalRawFold.checkOps_pure_raw_fold deps block.fuel slice.interval.before
    slice.interval.after slice.ops w l ran

/-- Raw.advance appends the exact event list and carries the original input
width; neither field determines a Raw.step. -/
private theorem prependEvents (signatures : List Basis) (ops : List RawOp) (before after : Raw.State)
    (initial final earlier : List Event) (bits combinedBits : Nat)
    (read : ops.foldlM (Raw.advance signatures) ⟨before,initial,bits⟩ = .ok ⟨after,final,bits⟩) :
    ops.foldlM (Raw.advance signatures) ⟨before,earlier ++ initial,combinedBits⟩ =
      .ok ⟨after,earlier ++ final,combinedBits⟩ := by
  induction ops generalizing before initial with
  | nil =>
    have same := Except.ok.inj read
    have state := congrArg Raw.Prepared.state same
    have events := congrArg Raw.Prepared.events same
    change before = after at state
    change initial = final at events
    rw [state,events]
    rfl
  | cons op rest ih =>
    cases step : Raw.step signatures before op with
    | error error =>
      simp only [List.foldlM_cons,Raw.advance,step,bind,Except.bind] at read
      cases read
    | ok next =>
      simp only [List.foldlM_cons,Raw.advance,step,bind,Except.bind,pure,Except.pure] at read ⊢
      simpa only [List.append_assoc] using ih next.state (initial ++ next.events) read

private theorem appendFolds {signatures left right before middle after a b}
    (l : Fold signatures left before middle a) (r : Fold signatures right middle after b) :
    Fold signatures (left ++ right) before after (a ++ b) := by
  unfold Fold at l r ⊢
  rw [List.foldlM_append,l]
  simpa only [bind,Except.bind,List.append_nil] using
    prependEvents signatures right middle after [] b a middle.frame.length before.frame.length r

private theorem splitSlice {α : Type} (xs : List α) (s a b : Nat) :
    (xs.drop s).take (a+b) = (xs.drop s).take a ++ (xs.drop (s+a)).take b := by
  simpa only [List.drop_drop] using prefixSplit (xs.drop s) a b

structure Three {deps program} {block : RuntimeInterval.Block deps program} {s a b c}
    (pre : Slice block s a) (choose : Slice block (s+a) b) (post : Slice block (s+a+b) c)
    (preEvents chooseEvents postEvents : List Event) : Prop where
  toChoose : pre.interval.after = choose.interval.before
  toPost : choose.interval.after = post.interval.before
  literal : (block.operations.drop s).take (a+b+c) =
    (pre.ops ++ choose.ops ++ post.ops).map Semantics.Observation.Op.pure
  preFold : Fold (deps.map (·.signature)) pre.ops pre.interval.before.quantum pre.interval.after.quantum preEvents
  chooseFold : Fold (deps.map (·.signature)) choose.ops choose.interval.before.quantum choose.interval.after.quantum chooseEvents
  postFold : Fold (deps.map (·.signature)) post.ops post.interval.before.quantum post.interval.after.quantum postEvents
  parentFold : Fold (deps.map (·.signature)) (pre.ops ++ choose.ops ++ post.ops)
    pre.interval.before.quantum post.interval.after.quantum (preEvents ++ chooseEvents ++ postEvents)
  parentTrace : RuntimeLocalEvents.trace pre.interval.before.quantum.reference (pre.ops ++ choose.ops ++ post.ops) =
    some ⟨post.interval.after.quantum.reference,preEvents ++ chooseEvents ++ postEvents,pre.interval.before.quantum.frame.length⟩

/-- Two genuine interfaces cannot be substituted just because they have equal
widths. Both boundary identities come from deterministic checking of the actual
original mixed prefixes. -/
theorem three {deps program} {block : RuntimeInterval.Block deps program} {s a b c}
    (pre : Slice block s a) (choose : Slice block (s+a) b) (post : Slice block (s+a+b) c) :
    ∃ preEvents chooseEvents postEvents, Three pre choose post preEvents chooseEvents postEvents := by
  have join1 := adjacent pre.interval choose.interval
  have join2 := adjacent choose.interval post.interval
  obtain ⟨preEvents,first⟩ := sliceFold pre
  obtain ⟨chooseEvents,middle⟩ := sliceFold choose
  obtain ⟨postEvents,last⟩ := sliceFold post
  have middle' := middle
  rw [← join1] at middle'
  have last' := last
  rw [← join2] at last'
  have total := appendFolds (appendFolds first middle') last'
  refine ⟨preEvents,chooseEvents,postEvents,join1,join2,?_,first,middle,last,total,?_⟩
  · rw [splitSlice block.operations s (a+b) c,splitSlice block.operations s a b,
      ← Nat.add_assoc s a b,pre.literal,choose.literal,post.literal,List.map_append,List.map_append]
  · exact Raw.operations_reference (deps.map (·.signature)) (pre.ops ++ choose.ops ++ post.ops)
      ⟨pre.interval.before.quantum,[],pre.interval.before.quantum.frame.length⟩
      ⟨post.interval.after.quantum,preEvents ++ chooseEvents ++ postEvents,pre.interval.before.quantum.frame.length⟩ total

/-- Bare parent execution on every joint-reference amplitude. The final state
and its complete original frame remain in the pair. -/
theorem Three.execute {deps program block s a b c pre choose post preEvents chooseEvents postEvents}
    (result : @Three deps program block s a b c pre choose post preEvents chooseEvents postEvents)
    {Reference : Type} (joint : Nat → Reference → ℂ) (ref : Reference) :
    RawActionComposition.execute deps (pre.ops ++ choose.ops ++ post.ops)
      pre.interval.before.quantum.reference (fun v => joint v ref) =
    some (post.interval.after.quantum.reference,Qleisli.Semantics.RawAction.events deps postEvents
      (Qleisli.Semantics.RawAction.events deps chooseEvents (Qleisli.Semantics.RawAction.events deps preEvents (fun v => joint v ref)))) := by
  let initial : Semantics.RawTrace.Prepared :=
    ⟨pre.interval.before.quantum.reference,[],pre.interval.before.quantum.frame.length⟩
  have h := RawActionComposition.execute_trace deps (pre.ops ++ choose.ops ++ post.ops) initial (fun v => joint v ref)
  have observed : (pre.ops ++ choose.ops ++ post.ops).foldlM Semantics.RawTrace.advance initial =
      some ⟨post.interval.after.quantum.reference,preEvents ++ chooseEvents ++ postEvents,pre.interval.before.quantum.frame.length⟩ :=
    result.parentTrace
  rw [observed] at h
  simpa only [initial,Qleisli.Semantics.RawAction.events,List.foldl_append,List.foldl_nil,Option.map_some] using h

#print axioms three
#print axioms Three.execute
end Qleisli.RuntimeAdjacentSlices
