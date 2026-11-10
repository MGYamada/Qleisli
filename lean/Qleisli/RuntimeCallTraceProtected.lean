import Qleisli.RuntimeCallTraceComputed

/-! Protected compute/use/uncompute in the original paired call traces.
The target fold preserves the literal order of all target ports, including
zero-width ports. The independent action uses the original protected body.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallTraceProtected
open QleisliKernel
open Semantics.Finite (gather)
open Semantics.Raw (Port Target Use)
open Semantics.RawTrace (Interface take insert axes)
open RuntimeCallTraceFrames (Partition WireOrder taken_member)
open Qleisli.Semantics.RawAction (events event)

private def takeTarget (state : List Port × Interface) (target : Target) :
    Option (List Port × Interface) := do
  let (port,next) ← take state.2 target.input
  pure (state.1 ++ [port],next)

private def putTarget (state : Interface) (target : Target × Port) : Interface :=
  insert state target.1.output target.2.wires

private theorem take_subset {before after : Interface} {token : Nat} {port : Port}
    (read : take before token = some (port,after)) : after.live ⊆ before.live := by
  unfold take at read
  obtain ⟨found,_,finished⟩ := Option.bind_eq_some_iff.mp read
  rw [← (Prod.mk.inj (Option.some.inj finished)).2]
  intro port member
  exact (List.mem_filter.mp member).1

private theorem paired_targets (targets : List Target) (spectators : List Port)
    {parent child : Interface} {ports out : List Port} {childAfter : Interface}
    (partition : parent.live.Perm (child.live ++ spectators)) (unique : (parent.live.map (·.token)).Nodup)
    (read : targets.foldlM takeTarget (ports,child) = some (out,childAfter)) :
    ∃ parentAfter, targets.foldlM takeTarget (ports,parent) = some (out,parentAfter) ∧
      parentAfter.live.Perm (childAfter.live ++ spectators) ∧
      parentAfter.frame = parent.frame ∧ childAfter.frame = child.frame ∧
      out ⊆ ports ++ child.live := by
  induction targets generalizing parent child ports with
  | nil =>
    have equal : (ports,child) = (out,childAfter) := Option.some.inj read
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    exact ⟨parent,rfl,partition,rfl,rfl,fun _ present => List.mem_append_left _ present⟩
  | cons target rest ih =>
    simp only [List.foldlM_cons,takeTarget,bind_assoc,pure_bind] at read
    obtain ⟨⟨port,childTaken⟩,childRead,childRest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨parentTaken,parentRead,taken,parentFrame,childFrame,takenUnique⟩ :=
      RuntimeTraceSpectators.take_spectators _ _ _ partition unique childRead
    obtain ⟨parentAfter,parentRest,live,pFrame,cFrame,covered⟩ := ih taken takenUnique childRest
    refine ⟨parentAfter,?_,live,pFrame.trans parentFrame,cFrame.trans childFrame,?_⟩
    · simpa only [List.foldlM_cons,takeTarget,parentRead,bind,Option.bind,pure] using parentRest
    · intro port present
      have member := covered present
      rw [List.append_assoc] at member
      rcases List.mem_append.mp member with old | added
      · exact List.mem_append_left _ old
      · rcases List.mem_cons.mp added with same | original
        · subst port
          exact List.mem_append_right _ (taken_member childRead)
        · exact List.mem_append_right _ (take_subset childRead original)

private theorem paired_put (targets : List (Target × Port)) (spectators : List Port)
    {parent child : Interface} (partition : parent.live.Perm (child.live ++ spectators)) :
    (targets.foldl putTarget parent).live.Perm ((targets.foldl putTarget child).live ++ spectators) ∧
      (targets.foldl putTarget parent).frame = parent.frame ∧
      (targets.foldl putTarget child).frame = child.frame := by
  induction targets generalizing parent child with
  | nil => exact ⟨partition,rfl,rfl⟩
  | cons target rest ih =>
    obtain ⟨next,pFrame,cFrame⟩ := RuntimeTraceSpectators.insert_spectators
      parent child spectators partition target.1.output target.2.wires
    obtain ⟨live,pTail,cTail⟩ := ih next
    exact ⟨live,pTail.trans pFrame,cTail.trans cFrame⟩

/-- Both actual native reads bind the same protected source and ordered
targets. The protected action retains the spectator slice in each row. -/
theorem protected_compute_correlated (dependencies : List Semantics.Finite.Dependency)
    (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (input output : Nat) (targets : List Target) (ancilla function : List Nat) (uses : List Use)
    (parentAfter childAfter : Raw.Transition)
    (parentRead : Raw.step (dependencies.map (·.signature)) parent
      (.computeUseUncompute input output targets ancilla function uses) = .ok parentAfter)
    (childRead : Raw.step (dependencies.map (·.signature)) child
      (.computeUseUncompute input output targets ancilla function uses) = .ok childAfter) :
    let other := WireOrder spectators
    Partition parentAfter.state.reference childAfter.state.reference spectators ∧
    parentAfter.state.frame = parent.frame ∧ childAfter.state.frame = child.frame ∧
    ∀ (joint : Nat → Nat → ℂ) (row : Nat),
    events dependencies parentAfter.events
      (fun input => joint (gather input (child.frame.map parent.frame.idxOf))
        (gather input (other.map parent.frame.idxOf))) row =
      events dependencies childAfter.events
        (fun input => joint input (gather row (other.map parent.frame.idxOf)))
        (gather row (child.frame.map parent.frame.idxOf)) := by
  intro other
  have parentFacts := Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ parentRead).1
  have childFacts := Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ childRead).1
  have parentTrace := Raw.step_reference _ _ _ _ parentRead
  have childTrace := Raw.step_reference _ _ _ _ childRead
  simp only [Semantics.RawTrace.step] at childTrace
  obtain ⟨⟨source,childTaken⟩,childTake,childRest⟩ := Option.bind_eq_some_iff.mp childTrace
  obtain ⟨parentTaken,parentTake,live,parentFrame,childFrame,unique⟩ :=
    RuntimeTraceSpectators.take_spectators _ _ _ partition.live parentFacts.owners childTake
  obtain ⟨⟨ports,childRest⟩,childTargets,childResult⟩ := Option.bind_eq_some_iff.mp childRest
  obtain ⟨parentRest,parentTargets,restLive,restParentFrame,restChildFrame,covered⟩ :=
    paired_targets targets spectators live unique childTargets
  let p := (targets.zip ports).foldl putTarget (insert parentRest output source.wires)
  let c := (targets.zip ports).foldl putTarget (insert childRest output source.wires)
  let wires := source.wires ++ ports.flatMap (·.wires)
  have pResult : (p,[Semantics.Raw.Event.protectedComputed parent.frame.length (axes parent.reference wires)
      source.bits ancilla.length function uses]) = (parentAfter.state.reference,parentAfter.events) := by
    apply Option.some.inj
    have trace := parentTrace
    simp only [Semantics.RawTrace.step,parentTake,bind,Option.bind,pure] at trace
    change ((targets.foldlM takeTarget ([],parentTaken)).bind _) = _ at trace
    rw [parentTargets] at trace
    exact trace
  have cResult : (c,[Semantics.Raw.Event.protectedComputed child.frame.length (axes child.reference wires)
      source.bits ancilla.length function uses]) = (childAfter.state.reference,childAfter.events) :=
    Option.some.inj childResult
  obtain ⟨pState,pEvents⟩ := Prod.mk.inj pResult
  obtain ⟨cState,cEvents⟩ := Prod.mk.inj cResult
  obtain ⟨joined,pFixed,cFixed⟩ := RuntimeTraceSpectators.insert_spectators _ _ _ restLive output source.wires
  obtain ⟨afterLive,pFinal,cFinal⟩ := paired_put (targets.zip ports) spectators joined
  have pFrame : parentAfter.state.frame = parent.frame :=
    (congrArg Interface.frame pState).symm.trans (pFinal.trans (pFixed.trans (restParentFrame.trans parentFrame)))
  have cFrame : childAfter.state.frame = child.frame :=
    (congrArg Interface.frame cState).symm.trans (cFinal.trans (cFixed.trans (restChildFrame.trans childFrame)))
  have inside : wires ⊆ child.frame := by
    intro wire member
    rcases List.mem_append.mp member with sourceWire | targetWire
    · exact childFacts.covered wire (List.mem_flatMap.mpr ⟨source,taken_member childTake,sourceWire⟩)
    · obtain ⟨port,present,portWire⟩ := List.mem_flatMap.mp targetWire
      have taken : port ∈ childTaken.live := by simpa only [List.nil_append] using covered present
      exact childFacts.covered wire (List.mem_flatMap.mpr ⟨port,take_subset childTake taken,portWire⟩)
  refine ⟨⟨?_,?_⟩,pFrame,cFrame,?_⟩
  · rw [← pState,← cState]
    exact afterLive
  · change parentAfter.state.frame.Perm (childAfter.state.frame ++ other)
    rw [pFrame,cFrame]
    exact partition.frame
  · intro joint row
    rw [← pEvents,← cEvents]
    simp only [events,List.foldl_cons,List.foldl_nil,event,axes]
    exact RuntimeCallTraceComputed.embed_partition partition.frame parentFacts.frame inside _ joint row

#print axioms protected_compute_correlated
end Qleisli.RuntimeCallTraceProtected
