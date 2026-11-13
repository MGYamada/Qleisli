import Qleisli.RuntimeOwnerBindingFacts
import Qleisli.RuntimeStructuralWires
import QleisliKernel.Qirf.RuntimePureBody

/-! Alignment of the original traversal's source states. It retains complete
owner states across named calls, observations, classical gaps and branches,
as well as the primitive and selection joins. Logical actions are separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSourceFlow
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open RuntimeStructuralAction (SourceState)
open RuntimeOwnerMap (Binding Map)

def OperationOwnerOrder {dependencies program block start count arity inputs outputs roles}
    (_frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    (before after : SourceState) : Prop :=
  after = {before with bindings := after.bindings} ∧
  (∃ entry exit,
    RuntimeInterval.Computed (RuntimePureBody.rolePorts roles before.bindings) entry ∧
    RuntimeInterval.Computed (RuntimePureBody.rolePorts roles after.bindings) exit ∧
    entry.map (·.token) = inputs ∧ exit.map (·.token) = outputs) ∧
  ∃ (interval : RuntimeInterval.Checked block start count)
    (incoming : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before)
    (transport : RuntimeOwnerTransition.Checked interval incoming.bindings),
    incoming.bindings = before.bindings ∧ transport.after.bindings = after.bindings ∧
    RuntimeInterval.Computed (RuntimeOwnerTransition.read interval incoming.bindings) transport

def NodeAligned {dependencies program block} (before after : RuntimeStructuralAction.SourceState)
    (node : RuntimePureBody.Node dependencies program block) : Prop :=
  match node with
  | .named (before := original) _ _ _ _ boundary _ =>
    before = original ∧ after = boundary.after
  | .primitive _ binding => before = binding.history ∧ after = binding.after
  | .structural (before := original) action => before = original ∧ after = action.after
  | .basis (event := event) (before := original) _ _ _ action =>
    before = original ∧ after = RuntimeBasisAction.continued event original action.output
  | .computed (event := event) (before := original) _ _ _ action =>
    before = original ∧ after = RuntimeComputedPredicate.continued event original action.literal.output
  | .certifiedComputed (event := event) (before := original) _ _ _ action =>
    before = original ∧ after = RuntimeComputedPredicate.continued event original action.literal.output
  | .operation frame .. => OperationOwnerOrder frame before after
  | .rectangularOperation (before := original) checked =>
    before = original ∧ after =
      RuntimeRectangularOperation.continued original checked.source.input checked.source.output checked.returned
  | .transform (before := original) _ _ _ _ _ owners _ _ =>
    before = original ∧ after = owners.after
  | .selection (codes := codes) .. =>
    before.bindings = codes.owners.before.bindings ∧
      after = {before with bindings := codes.owners.transport.after.bindings}

/-- A source-ordered selection of complete bindings, including zero-width
owners, gives exactly the ports read by the native interval. -/
def OrderedPorts (roles : List RuntimeOwnerMap.Owner) (bindings : Map)
    (ports : List Semantics.Raw.Port) : Prop :=
  ∃ selected : Map,
    RuntimeInterval.Computed (RuntimeOwnerMap.order roles bindings) selected ∧
    selected ⊆ bindings ∧ selected.map (·.owner) = roles ∧ ports = selected.map (·.port)

private theorem original_ports {roles allRoles state found actual}
    (frame : RuntimeOwnerMap.Checked allRoles state)
    (valid : Raw.stateValid state.quantum = true)
    (read : RuntimeInterval.Computed (RuntimePureBody.rolePorts roles frame.bindings) found)
    (native : PureInterval.ports state (found.map (·.token)) = some actual) :
    OrderedPorts roles frame.bindings actual := by
  obtain ⟨work,left,ran⟩ := read
  unfold RuntimePureBody.rolePorts RuntimePrimitiveSource.rolePorts at ran
  obtain ⟨selected,middle,ordered,returned⟩ := bind_success _ _ _ _ _ ran
  have same := (pure_success _ _ _ _ returned).1
  subst found
  have selection : RuntimeInterval.Computed (RuntimeOwnerMap.order roles frame.bindings) selected :=
    ⟨work,middle,ordered⟩
  obtain ⟨contained,owners⟩ := RuntimeSelectionPartition.order_values frame.bindings roles selected selection
  have present : selected.map (·.port) ⊆ state.quantum.live := by
    intro port member
    obtain ⟨binding,found,rfl⟩ := List.mem_map.mp member
    exact frame.complete.mem_iff.mp (List.mem_map_of_mem (contained found))
  have literal := Qleisli.RuntimeStructuralWires.ports_read state.quantum.reference
    (selected.map (·.port)) (Raw.Ownership.valid _ valid).owners present
  exact ⟨selected,selection,contained,owners,Option.some.inj (native.symm.trans literal)⟩

/-- Recover both source-ordered owner selections on the exact entry and exit
of the original operation interval. -/
theorem OperationOwnerOrder.ordered_ports {dependencies program block start count arity inputs outputs roles}
    {frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles}
    {before after : SourceState} (aligned : OperationOwnerOrder frame before after)
    {inputRoles outputRoles} (input : RuntimeOwnerMap.Checked inputRoles frame.interval.before)
    (output : RuntimeOwnerMap.Checked outputRoles frame.interval.after)
    (initial : input.bindings = before.bindings) (final : output.bindings = after.bindings) :
    OrderedPorts roles before.bindings frame.selected ∧ OrderedPorts roles after.bindings frame.returned := by
  obtain ⟨_,⟨entry,exit,entryRead,exitRead,entryTokens,exitTokens⟩,_⟩ := aligned
  exact ⟨initial ▸ original_ports input frame.interval.history.1 (initial.symm ▸ entryRead)
      (entryTokens.symm ▸ frame.atEntry),
    final ▸ original_ports output frame.interval.history.2.2.1 (final.symm ▸ exitRead)
      (exitTokens.symm ▸ frame.atExit)⟩

def Aligned {dependencies program block} (before after : SourceState)
    (step : @RuntimePureBody.Step dependencies program block) : Prop :=
  match step with
  | .named (before := original) _ _ _ _ boundary _ _ =>
    before = original ∧ after = boundary.after
  | .pure node => NodeAligned before after node
  | .observation (before := original) observed => before = original ∧ after = observed.after
  | .gap (before := original) gap => before = original ∧ after = gap.after
  | .conditional _ _ _ _ _ (before := original) action _ _ => before = original ∧ after = action.next

def entryState {dependencies program block}
    (step : @RuntimePureBody.Step dependencies program block) : Option SourceState :=
  match step with
  | .named (before := original) .. => some original
  | .observation (before := original) _ => some original
  | .gap (before := original) _ => some original
  | .conditional _ _ _ _ _ (before := original) _ _ _ => some original
  | .pure .. => none

def exitState {dependencies program block}
    (step : @RuntimePureBody.Step dependencies program block) : Option SourceState :=
  match step with
  | .named _ _ _ _ boundary _ _ => some boundary.after
  | .observation observed => some observed.after
  | .gap gap => some gap.after
  | .conditional _ _ _ _ _ action _ _ => some action.next
  | .pure .. => none

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

theorem Run.suffix {dependencies program block initial final first rest}
    (flow : @Run dependencies program block initial (first++rest) final) :
    ∃ middle, Run middle rest final := by
  induction first generalizing initial with
  | nil => exact ⟨initial,flow⟩
  | cons step first ih =>
    cases flow with
    | cons _ tail => exact ih tail

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
