import Qleisli.RuntimeOwnerBindingFacts
import QleisliKernel.Qirf.RuntimePureBody

/-! Alignment of actual named-call, primitive and selection source states. This is
an administrative property of the native traversal, not a logical action or
code equation. Other step kinds carry no state assertion here; named entry/exit
queries retain their original scope.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSourceFlow
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimeStructuralAction (SourceState)
open RuntimeOwnerMap (Binding Map)

def NodeAligned {dependencies program block} (before after : RuntimeStructuralAction.SourceState)
    (node : RuntimePureBody.Node dependencies program block) : Prop :=
  match node with
  | .primitive _ binding => before = binding.history ∧ after = binding.after
  | .selection (codes := codes) .. =>
    before.bindings = codes.owners.before.bindings ∧
      after = {before with bindings := codes.owners.transport.after.bindings}
  | _ => True

def Aligned {dependencies program block} (before after : SourceState)
    (step : @RuntimePureBody.Step dependencies program block) : Prop :=
  match step with
  | .named (before := original) _ _ _ _ boundary _ _ =>
    before = original ∧ after = boundary.after
  | .pure node => NodeAligned before after node
  | .gap .. | .observation .. | .conditional .. => True

def entryState {dependencies program block}
    (step : @RuntimePureBody.Step dependencies program block) : Option SourceState :=
  match step with
  | .named (before := original) .. => some original
  | .pure .. | .gap .. | .observation .. | .conditional .. => none

def exitState {dependencies program block}
    (step : @RuntimePureBody.Step dependencies program block) : Option SourceState :=
  match step with
  | .named _ _ _ _ boundary _ _ => some boundary.after
  | .pure .. | .gap .. | .observation .. | .conditional .. => none

theorem Aligned.entry_eq {dependencies program block before after step state}
    (aligned : @Aligned dependencies program block before after step)
    (entry : entryState step = some state) : before = state := by
  cases step <;> simp_all [entryState,Aligned]

theorem Aligned.exit_eq {dependencies program block before after step state}
    (aligned : @Aligned dependencies program block before after step)
    (exit : exitState step = some state) : after = state := by
  cases step <;> simp_all [exitState,Aligned]

theorem Aligned.entry {dependencies program block before after step}
    (aligned : @Aligned dependencies program block before after step)
    (present : ∃ state, entryState step = some state) : entryState step = some before := by
  obtain ⟨state,read⟩ := present
  exact read.trans (congrArg some (aligned.entry_eq read).symm)

theorem Aligned.exit {dependencies program block before after step}
    (aligned : @Aligned dependencies program block before after step)
    (present : ∃ state, exitState step = some state) : exitState step = some after := by
  obtain ⟨state,read⟩ := present
  exact read.trans (congrArg some (aligned.exit_eq read).symm)

inductive Run {dependencies program block} : SourceState →
    List (@RuntimePureBody.Step dependencies program block) → SourceState → Prop where
  | nil (state : SourceState) : Run state [] state
  | cons {initial middle final first rest}
      (head : Aligned initial middle first) (tail : Run middle rest final) :
      Run initial (first :: rest) final

theorem Run.append {dependencies program block initial middle final first rest}
    (left : @Run dependencies program block initial first middle) (right : Run middle rest final) :
    Run initial (first ++ rest) final := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head (ih right)

theorem Run.snoc {dependencies program block initial middle final steps step}
    (before : @Run dependencies program block initial steps middle) (next : Aligned middle final step) :
    Run initial (steps ++ [step]) final :=
  before.append (.cons next (.nil _))

/-- Two actual adjacent named calls share their complete source state, not
only widths or an assumed equality of encoding matrices. -/
theorem Run.adjacent {dependencies program block initial final first second rest after before}
    (flow : @Run dependencies program block initial (first :: second :: rest) final)
    (exit : exitState first = some after) (entry : entryState second = some before) :
    after = before := by
  cases flow with
  | cons first rest =>
    cases rest with
    | cons second _ => exact (first.exit_eq exit).symm.trans (second.entry_eq entry)

def Invariant {dependencies program block Cursor Receipt}
    (initial : SourceState)
    (state : @RuntimePureBody.QueryState dependencies program block Cursor Receipt) : Prop :=
  match state with
  | (history,_,_,_,steps,_,_,_,_) => Run initial steps history

/-- The real final frame read and original source-return order connect the
last traversal state to the returned state, preserving the full owner history. -/
def Returned {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (roles : List RuntimeOwnerMap.Owner) (before after : SourceState) : Prop :=
  ∃ native : RuntimeInterval.Checked block block.operations.length 0,
    RuntimeInterval.Computed (RuntimeInterval.check block block.operations.length 0) native ∧
    ∃ owners : RuntimeOwnerMap.Checked roles native.after,
      RuntimeInterval.Computed (RuntimePureBody.reordered roles native.after before.bindings) owners ∧
      after = {before with bindings := owners.bindings}

/-- Ordering a complete original map by its own ordered owner identities
returns the same bindings, including their full bases and zero-width ports. -/
theorem order_self (bindings ordered : Map)
    (unique : (bindings.map (fun binding => binding.owner.ordinal)).Nodup)
    (read : RuntimeInterval.Computed (RuntimeOwnerMap.order (bindings.map (·.owner)) bindings) ordered) :
    ordered = bindings := by
  have facts : ordered ⊆ bindings ∧
      ordered.map Binding.owner = bindings.map Binding.owner :=
    RuntimeSelectionPartition.order_values bindings (bindings.map Binding.owner) ordered read
  exact RuntimeOwnerTransitionAction.owner_order_eq bindings ordered unique facts.1 facts.2

/-- The actual complete reorder/check wrapper supplies uniqueness and its
own original order receipt; no assumed equality of unrelated source maps is used. -/
theorem reordered_self {state bindings result}
    (checked : RuntimeInterval.Computed
      (RuntimePureBody.reordered (bindings.map (·.owner)) state bindings) result) :
    result.bindings = bindings := by
  obtain ⟨work,left,ran⟩ := checked
  unfold RuntimePureBody.reordered at ran
  obtain ⟨ordered,middle,read,rest⟩ := bind_success _ _ _ _ _ ran
  unfold RuntimeOwnerMap.check at rest
  obtain ⟨certificate,budget,_checked,returned⟩ := bind_success _ _ _ _ _ rest
  have same : result = certificate.val := (pure_success _ _ _ _ returned).1
  subst result
  have unique : (bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using certificate.val.ownersDistinct
  exact certificate.property.trans (order_self bindings ordered unique ⟨work,middle,read⟩)

#print axioms order_self
#print axioms reordered_self
#print axioms Run.adjacent
end Qleisli.RuntimeNamedSourceFlow
