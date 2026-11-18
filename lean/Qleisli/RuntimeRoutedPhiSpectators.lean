import Qleisli.RuntimeRoutedPhiGeometry
import QleisliKernel.Qirf.RuntimeBranchProjection

/-! Connect each parked source owner to its actual Raw phi in both
original arms. Spectator order is its witnessed order through the full
phi list, including owners with zero physical wires.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes)
open Semantics.Observation (QuantumPhi phiWires phiInterface)
open Raw.Observation (phiValid)
open RuntimeCallTraceFrames (WireOrder)

private theorem ports_members {live : List Port} {tokens : List Nat} {ports : List Port}
    (read : PureInterval.portsOf live tokens = some ports) : ports ⊆ live := by
  induction tokens generalizing ports with
  | nil =>
    have same : [] = ports := Option.some.inj read
    subst ports
    simp
  | cons token tokens ih =>
    unfold PureInterval.portsOf at read
    rw [List.mapM_cons] at read
    obtain ⟨head,found,rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨tail,more,done⟩ := Option.bind_eq_some_iff.mp rest
    have same := Option.some.inj done
    subst ports
    intro port member
    rcases List.mem_cons.mp member with rfl | there
    · exact List.mem_of_find?_eq_some found
    · exact ih more there

private theorem move_axis_slots (left right : Raw.State) (phis : List QuantumPhi) (choice : Bool)
    {spectators : RuntimeOwnerMap.Map}
    (moves : List ((phi : QuantumPhi) × RuntimeBranchProjection.Move spectators phi))
    (valid : phiValid left right phis = true)
    (armValid : Raw.stateValid (if choice then left else right) = true)
    (distinct : (phiInterface phis).frame.Nodup)
    (occurs : ∀ move ∈ moves, move.1 ∈ phis)
    (retained : ∀ binding ∈ spectators, binding.port ∈ (if choice then left else right).live) :
    let arm := (if choice then left else right).reference
    let permutation := axes arm (phiWires arm phis choice)
    List.Forall₂ (fun new old => permutation[new]? = some old)
      (axes (phiInterface phis) (WireOrder (moves.map (·.2.original.binding.port))))
      (axes arm (WireOrder (moves.map (·.2.original.thenBinding.port)))) := by
  intro arm permutation
  induction moves with
  | nil => exact .nil
  | cons head tail ih =>
    let old := head.2.original.thenBinding.port
    have oldMember : old ∈ arm.live := retained _ head.2.original.thenMember
    have found := RuntimeNamedFrameAxes.tokenLookup arm.live old
      (Raw.Ownership.valid _ armValid).owners oldMember
    have token : old.token = if choice then head.1.thenToken else head.1.elseToken := by
      cases choice
      · exact (congrArg (fun (binding : RuntimeOwnerMap.Binding) => binding.port.token) head.2.same).trans
          head.2.original.elseToken
      · exact head.2.original.thenToken
    have incoming : incomingWires arm choice head.1 = old.wires := by
      unfold incomingWires
      rw [← token,found]
      rfl
    have occursHere := occurs head List.mem_cons_self
    have width := (incoming_width left right phis choice valid armValid head.1 occursHere).trans
      (congrArg List.length incoming)
    let pairs := head.1.wires.zip old.wires
    have destinations : pairs.map Prod.fst = head.1.wires := List.map_fst_zip width.le
    have sources : pairs.map Prod.snd = old.wires := List.map_snd_zip width.ge
    have firstSlots : List.Forall₂ (fun new old => permutation[new]? = some old)
        (head.1.wires.map (phiInterface phis).frame.idxOf) (old.wires.map arm.frame.idxOf) := by
      rw [← destinations,← sources]
      simp only [List.map_map,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same,Function.comp_def]
      intro pair member
      exact raw_phi_axis left right phis choice valid armValid distinct head.1 occursHere pair (by
        rw [incoming]
        exact member)
    have suffix := ih (fun move member => occurs move (List.mem_cons_of_mem _ member))
    simpa only [List.map_cons,List.flatMap_cons,axes,List.map_append] using List.rel_append firstSlots suffix

/-- Witnessed spectator effects give the actual permutation slots in
incoming owner order, even when the parked port has no physical axes. -/
theorem checked_spectator_phi_slots {dependencies program block offset roles inputTokens ordinary}
    {branch : @RuntimeInterval.Branch dependencies program block offset}
    {entry : RuntimeOwnerMap.Checked roles branch.interval.before}
    (checked : RuntimeBranchProjection.Checked branch entry inputTokens ordinary)
    (choice : Bool)
    (armValid : Raw.stateValid (if choice then branch.thenState.quantum else branch.elseState.quantum) = true)
    (distinct : (phiInterface branch.quantum).frame.Nodup) :
    let arm := (if choice then branch.thenState.quantum else branch.elseState.quantum).reference
    let permutation := axes arm (phiWires arm branch.quantum choice)
    List.Forall₂ (fun new old => permutation[new]? = some old)
      (axes (phiInterface branch.quantum) (WireOrder (checked.moves.map (·.2.original.binding.port))))
      (axes arm (WireOrder (checked.moves.map (·.2.original.thenBinding.port)))) := by
  exact move_axis_slots branch.thenState.quantum branch.elseState.quantum branch.quantum choice checked.moves
    (RuntimeOriginalBranch.original_branch_phi_checks branch).1 armValid distinct
    (fun move member => by
      have included : move.1 ∈ checked.moves.map Sigma.fst := List.mem_map_of_mem member
      rw [checked.allMoves] at included
      exact (List.mem_filter.mp included).1)
    (fun binding member => by
      cases choice
      · exact ports_members checked.elseParked (List.mem_map_of_mem member)
      · exact ports_members checked.thenParked (List.mem_map_of_mem member))

#print axioms checked_spectator_phi_slots
end Qleisli.RuntimeCallHistory
