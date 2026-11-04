import Qleisli.RawActionLocality
import Qleisli.RuntimeIntervalRawFold
import Qleisli.RuntimeFoldLocality
import Qleisli.RuntimeIntervalTrace
import QleisliKernel.Qirf.RuntimeNamedFrameAxes
import Mathlib.Data.List.Perm.Subperm

/-! Relate the original parent events of a named call to the stored child
selection. The scope and selection must cover the same literal interval.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedSelectionParent
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Raw (Port)

private theorem named_embedding {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect) :
    ∃ spectators, scope.interval.before.quantum.live.Perm (scope.localEntry.quantum.live ++ spectators) := by
  have selected := congrArg Semantics.RawTrace.Interface.live (RuntimeNamedFrameAxes.mixedAxes_input scope).2.1
  change scope.localEntry.quantum.live = scope.selected at selected
  have distinct := (Raw.Ownership.valid _ (RuntimeNamedFrameAxes.initialized scope.entryRead).2.1).owners
  have unique : scope.localEntry.quantum.live.Nodup :=
    List.Pairwise.of_map Port.token (fun _ _ ne h => ne (congrArg Port.token h)) distinct
  have subset : scope.localEntry.quantum.live ⊆ scope.interval.before.quantum.live := by
    rw [selected]
    exact (RuntimeNamedFrameAxes.selectedPorts _ _ _ scope.atEntry).1
  obtain ⟨ordered,permuted,contained⟩ := unique.subperm subset
  obtain ⟨spectators,split⟩ := contained.exists_perm_append
  exact ⟨spectators,split.trans (permuted.append_right spectators)⟩

private theorem circuit_pieces (bits : Nat) (axes : List Nat) (chunks : List (List Step)) :
    Exact.ListRel (Raw.Sector.EventPiece bits) (RuntimeLocalEvents.circuitEvents bits axes chunks)
      (chunks.map (fun chunk => chunk.map (Semantics.RawTrace.localize axes))) := by
  induction chunks with
  | nil => trivial
  | cons first rest ih => exact ⟨Or.inl rfl,ih⟩

private theorem local_events (deps : List Dependency) (bits : Nat) (chunks : List (List Step)) (values : Nat → ℂ) :
    Qleisli.Semantics.RawAction.events deps (RuntimeLocalEvents.localEvents bits chunks) values =
      Qleisli.Semantics.RawAction.circuit deps chunks.flatten values := by
  induction chunks generalizing values with
  | nil => rfl
  | cons first rest ih =>
    change Qleisli.Semantics.RawAction.events deps (RuntimeLocalEvents.localEvents bits rest)
      (Qleisli.Semantics.RawAction.circuit deps first values) = _
    rw [ih]
    simp only [List.flatten_cons,Qleisli.Semantics.RawAction.circuit,List.foldl_append]

private theorem pull_events (deps : List Dependency) (globalBits localBits : Nat) (axes : List Nat)
    (unique : axes.Nodup) (lengthAxes : axes.length = localBits) (chunks : List (List Step))
    (bounded : RuntimeLocalEvents.bounds localBits chunks = true) (base : Nat) (values : Nat → ℂ) :
    Qleisli.Semantics.RawAction.Locality.pull base axes
        (Qleisli.Semantics.RawAction.events deps (RuntimeLocalEvents.circuitEvents globalBits axes chunks) values) =
      Qleisli.Semantics.RawAction.events deps (RuntimeLocalEvents.localEvents localBits chunks)
        (Qleisli.Semantics.RawAction.Locality.pull base axes values) := by
  rw [Qleisli.Semantics.RawAction.Locality.circuit_events,local_events]
  apply Qleisli.Semantics.RawAction.Locality.circuit_selected deps base axes unique
  · intro op opMem ctl ctlMem
    obtain ⟨chunk,chunkMem,member⟩ := List.mem_flatten.mp opMem
    rw [lengthAxes]
    exact RuntimeLocalEvents.bounds_controls bounded chunk chunkMem op member ctl ctlMem
  · intro op opMem axis axisMem
    obtain ⟨chunk,chunkMem,member⟩ := List.mem_flatten.mp opMem
    rw [lengthAxes]
    exact RuntimeLocalEvents.bounds_targets bounded chunk chunkMem op member axis axisMem

theorem at_zero {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (zero : start = 0) :
    interval.before.quantum.reference = block.entry.quantum.reference := by
  obtain ⟨work,left,actual⟩ := interval.prefixRead
  have empty : block.operations.take start = ([] : List Semantics.Raw.Op).map Semantics.Observation.Op.pure := by simp [zero]
  rw [empty] at actual
  obtain ⟨events,reader⟩ := Qleisli.RuntimeIntervalTrace.checkOps_pure_trace dependencies block.fuel _ _ [] work left actual
  exact (congrArg Semantics.RawTrace.Prepared.state (Option.some.inj reader)).symm

private theorem embedded_chunks (signatures : List Basis) (ops : List Semantics.Raw.Op)
    (parent child : Raw.State) (parentResult childResult : Raw.Prepared) (spectators : List Port)
    (ownerBefore ownerAfter : Semantics.RawOwnerFlow.Frame) (pieces : List (List Step))
    (embedding : parent.live.Perm (child.live ++ spectators))
    (parentFold : ops.foldlM (Raw.advance signatures) ⟨parent,[],parent.frame.length⟩ = .ok parentResult)
    (childFold : ops.foldlM (Raw.advance signatures) ⟨child,[],child.frame.length⟩ = .ok childResult)
    (ownerFold : ops.foldlM Semantics.RawOwnerFlow.step ownerBefore = some ownerAfter)
    (related : Exact.ListRel (Raw.Sector.EventPiece child.frame.length) childResult.events pieces) :
    ∃ chunks, childResult.events = RuntimeLocalEvents.localEvents child.frame.length chunks ∧
      parentResult.events = RuntimeLocalEvents.circuitEvents parent.frame.length (child.frame.map parent.frame.idxOf) chunks ∧
      RuntimeLocalEvents.bounds child.frame.length chunks = true := by
  obtain ⟨chunks,stored⟩ := RuntimeFoldLocality.folds_locality signatures ops parent child parentResult childResult
    spectators ownerBefore ownerAfter pieces embedding parentFold childFold ownerFold related
  exact ⟨chunks,stored.1,stored.2.1,stored.2.2.2.1⟩

private theorem lift_folds (dependencies : List Dependency) (ops : List Semantics.Raw.Op)
    (parent after child childAfter : Raw.State) (axes : List Nat) (childResult : Semantics.RawTrace.Prepared)
    (parentRan : RuntimeIntervalRawFold.Traced (dependencies.map (·.signature)) ops parent after)
    (childRan : RuntimeIntervalRawFold.Traced (dependencies.map (·.signature)) ops child childAfter)
    (original : RuntimeLocalEvents.trace child.reference ops = some childResult)
    (pieces : List (List Step)) (related : Exact.ListRel (Raw.Sector.EventPiece child.frame.length) childResult.events pieces)
    (ownerBefore ownerAfter : Semantics.RawOwnerFlow.Frame)
    (ownerFold : ops.foldlM Semantics.RawOwnerFlow.step ownerBefore = some ownerAfter)
    (spectators : List Port) (embedding : parent.live.Perm (child.live ++ spectators))
    (coordinates : child.frame.map parent.frame.idxOf = axes) (unique : axes.Nodup) :
    ∃ events, RuntimeLocalEvents.trace parent.reference ops = some ⟨after.reference,events,parent.frame.length⟩ ∧
      ∀ (values : Nat → ℂ) (base : Nat), Qleisli.Semantics.RawAction.Locality.pull base axes
        (Qleisli.Semantics.RawAction.events dependencies events values) =
        Qleisli.Semantics.RawAction.events dependencies childResult.events
          (Qleisli.Semantics.RawAction.Locality.pull base axes values) := by
  obtain ⟨events,parentFold,parentTrace⟩ := parentRan
  obtain ⟨childEvents,childFold,childTrace⟩ := childRan
  have emitted : childEvents = childResult.events :=
    congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (childTrace.symm.trans original))
  let parentResult : Raw.Prepared := ⟨after,events,parent.frame.length⟩
  let selectedResult : Raw.Prepared := ⟨childAfter,childEvents,child.frame.length⟩
  have savedPieces : Exact.ListRel (Raw.Sector.EventPiece child.frame.length) childEvents pieces := by
    rw [emitted]
    exact related
  change ops.foldlM (Raw.advance (dependencies.map Semantics.Finite.Dependency.signature))
    ⟨parent,[],parent.frame.length⟩ = .ok parentResult at parentFold
  change ops.foldlM (Raw.advance (dependencies.map Semantics.Finite.Dependency.signature))
    ⟨child,[],child.frame.length⟩ = .ok selectedResult at childFold
  change Exact.ListRel (Raw.Sector.EventPiece child.frame.length) selectedResult.events pieces at savedPieces
  have locality : ∃ chunks, selectedResult.events = RuntimeLocalEvents.localEvents child.frame.length chunks ∧
      parentResult.events = RuntimeLocalEvents.circuitEvents parent.frame.length (child.frame.map parent.frame.idxOf) chunks ∧
      RuntimeLocalEvents.bounds child.frame.length chunks = true := by
    with_reducible
      exact embedded_chunks (dependencies.map Semantics.Finite.Dependency.signature)
        ops parent child parentResult selectedResult spectators ownerBefore ownerAfter pieces embedding parentFold childFold ownerFold savedPieces
  obtain ⟨chunks,localRun,parentRun,bounded⟩ := locality
  have parentEvents : events = RuntimeLocalEvents.circuitEvents parent.frame.length axes chunks :=
    parentRun.trans (congrArg (fun a => RuntimeLocalEvents.circuitEvents parent.frame.length a chunks) coordinates)
  have childData : childResult.events = RuntimeLocalEvents.localEvents child.frame.length chunks := emitted.symm.trans localRun
  have width : axes.length = child.frame.length := by rw [← coordinates,List.length_map]
  refine ⟨events,parentTrace,?_⟩
  intro values base
  rw [parentEvents,childData]
  exact pull_events dependencies _ _ _ unique width chunks bounded base values

/-- The localRaw executable fold and the stored selection use the same
original subject. No comparison between producer-supplied event lists occurs. -/
theorem parent_action {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    {first size localInputs outputs roles}
    (frame : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs roles)
    (starts : first = 0) (covers : size = ((block.operations.drop start).take count).length)
    {selectorBits targetBits retained restricted beforeRoles afterRoles before after}
    (literal : @RuntimeLocalEvents.Literal dependencies scope.program scope.prepared.block first size localInputs outputs roles
      frame selectorBits targetBits retained restricted beforeRoles afterRoles before after) :
    ∃ parentEvents,
      RuntimeLocalEvents.trace scope.interval.before.quantum.reference frame.operations =
        some ⟨scope.interval.after.quantum.reference,parentEvents,scope.interval.before.quantum.frame.length⟩ ∧
      ∀ (values : Nat → ℂ) (base : Nat),
        Qleisli.Semantics.RawAction.Locality.pull base (RuntimeNamedFrameAxes.mixedAxes scope)
          (Qleisli.Semantics.RawAction.events dependencies parentEvents values) =
        Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
          (Qleisli.Semantics.RawAction.Locality.pull base (RuntimeNamedFrameAxes.mixedAxes scope) values) := by
  have actual : (block.operations.drop start).take count = frame.operations.map Semantics.Observation.Op.pure := by
    calc
      _ = (((block.operations.drop start).take count).drop first).take size := by rw [starts,List.drop_zero,covers,List.take_length]
      _ = _ := frame.literal
  have folds := RuntimeIntervalRawFold.mixed_call_traces scope frame.operations actual
  have entry : frame.interval.before.quantum.reference = scope.localEntry.quantum.reference :=
    (at_zero frame.interval starts).trans ((RuntimeNamedFrameAxes.mixedAxes_input scope).2.2.1.trans
      (RuntimeNamedFrameAxes.mixedAxes_input scope).2.1.symm)
  have written : RuntimeLocalEvents.trace scope.localEntry.quantum.reference frame.operations = some literal.traceResult := by
    rw [← entry]
    exact literal.executed
  have frameEq : frame.interval.before.quantum.frame = scope.localEntry.quantum.frame :=
    congrArg Semantics.RawTrace.Interface.frame entry
  let inner := RuntimeForestCode.forestAxes frame.interval.before.quantum.frame literal.selection.selected
  let pieces := literal.chunks.map (fun chunk => chunk.map (Semantics.RawTrace.localize inner))
  have related : Exact.ListRel (Raw.Sector.EventPiece scope.localEntry.quantum.frame.length) literal.traceResult.events pieces := by
    rw [literal.literal,← frameEq]
    exact circuit_pieces _ _ _
  obtain ⟨spectators,embedding⟩ := named_embedding scope
  have returned := frame.ownerReturn
  unfold Semantics.RawOwnerFlow.Returns Semantics.RawOwnerFlow.run at returned
  obtain ⟨ownerBefore,_,rest⟩ := Option.bind_eq_some_iff.mp returned
  obtain ⟨ownerAfter,ownerFold,_⟩ := Option.bind_eq_some_iff.mp rest
  change frame.operations.foldlM Semantics.RawOwnerFlow.step ownerBefore = some ownerAfter at ownerFold
  have localFrame := congrArg Semantics.RawTrace.Interface.frame (RuntimeNamedFrameAxes.mixedAxes_input scope).2.1
  change scope.localEntry.quantum.frame = scope.selected.flatMap (·.wires) at localFrame
  have axes : scope.localEntry.quantum.frame.map scope.interval.before.quantum.frame.idxOf =
      RuntimeNamedFrameAxes.mixedAxes scope := by
    exact congrArg (List.map scope.interval.before.quantum.frame.idxOf) localFrame
  exact lift_folds dependencies frame.operations scope.interval.before.quantum scope.interval.after.quantum
    scope.localEntry.quantum scope.localAfter.quantum (RuntimeNamedFrameAxes.mixedAxes scope) literal.traceResult
    folds.1 folds.2 written pieces related ownerBefore ownerAfter ownerFold spectators embedding axes
    (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1

#print axioms parent_action
end Qleisli.RuntimeNamedSelectionParent
