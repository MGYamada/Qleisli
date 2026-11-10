import Qleisli.RuntimeCallBranchRead
import Qleisli.RuntimeCallHistoryPhi

/-! The complete native phi guard determines the arm's exact coordinate
permutation, including zero-width owners. Destination wires may be fresh.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes)
open Semantics.Observation (QuantumPhi phiWires phiInterface)
open Raw.Observation (phiValid)
open RuntimeCallTraceFrames (WireOrder Partition)

private def sourceToken (choice : Bool) (phi : QuantumPhi) : Nat :=
  if choice then phi.thenToken else phi.elseToken

private theorem selected_ports (state : Raw.State) (choice : Bool) (phis : List QuantumPhi)
    (valid : Raw.stateValid state = true)
    (lookup : ∀ phi ∈ phis, ∃ port,
      state.live.find? (fun p => p.token == sourceToken choice phi) = some port ∧
      phi.wires.length = port.bits) :
    ∃ ports : List Port, ports.map Port.token = phis.map (sourceToken choice) ∧
      ports ⊆ state.live ∧ WireOrder ports = phiWires state.reference phis choice ∧
      (WireOrder ports).length = (phiInterface phis).frame.length := by
  induction phis with
  | nil => exact ⟨[],rfl,by simp,rfl,rfl⟩
  | cons phi rest ih =>
    obtain ⟨port,read,width⟩ := lookup phi List.mem_cons_self
    have present := List.mem_of_find?_eq_some read
    have token := beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == sourceToken choice phi) read)
    have shape := ((Raw.Ownership.valid _ valid).ports port present).1
    obtain ⟨tail,keys,inside,wires,tailWidth⟩ := ih
      (fun selected member => lookup selected (List.mem_cons_of_mem _ member))
    refine ⟨port::tail,?_,?_,?_,?_⟩
    · simp only [List.map_cons,token,keys]
    · intro selected member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact present
      · exact inside inTail
    · change port.wires ++ WireOrder tail = _
      have found : state.reference.live.find? (fun p => p.token == (if choice then phi.thenToken else phi.elseToken)) =
          some port := read
      simp only [wires,phiWires,List.flatMap_cons,found,Option.map_some,Option.getD_some]
    · change (port.wires ++ WireOrder tail).length = (phi.wires ++ (phiInterface rest).frame).length
      rw [List.length_append,List.length_append,tailWidth,← shape,← width]

/-- The complete original phi list visits every arm port once and consumes
the corresponding ordered wires. Its destination frame has that same width. -/
theorem phi_arm_geometry (left right : Raw.State) (phis : List QuantumPhi)
    (valid : phiValid left right phis = true) (choice : Bool)
    (armValid : Raw.stateValid (if choice then left else right) = true) :
    let arm := if choice then left else right
    (phiWires arm.reference phis choice).Perm arm.frame ∧
      (phiWires arm.reference phis choice).length = (phiInterface phis).frame.length := by
  intro arm
  simp only [phiValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  rcases valid with ⟨⟨⟨⟨⟨⟨leftKeys,rightKeys⟩,leftCount⟩,rightCount⟩,_⟩,_⟩,shapes⟩
  have count : phis.length = arm.live.length := by cases choice <;> assumption
  have keys : (phis.map (sourceToken choice)).Nodup := by
    cases choice
    · exact Raw.Ownership.unique_nodup _ rightKeys
    · exact Raw.Ownership.unique_nodup _ leftKeys
  have lookup (phi : QuantumPhi) (member : phi ∈ phis) :
      ∃ port, arm.live.find? (fun p => p.token == sourceToken choice phi) = some port ∧
        phi.wires.length = port.bits := by
    have shape := shapes phi member
    cases pRead : left.live.find? (fun p => p.token == phi.thenToken) with
    | none => simp [pRead] at shape
    | some p =>
      cases cRead : right.live.find? (fun p => p.token == phi.elseToken) with
      | none => simp [pRead,cRead] at shape
      | some c =>
        simp only [pRead,cRead,Bool.and_eq_true,beq_iff_eq] at shape
        cases choice
        · exact ⟨c,cRead,shape.2.trans shape.1⟩
        · exact ⟨p,pRead,shape.2⟩
  obtain ⟨ports,tokens,covered,wires,width⟩ := selected_ports arm choice phis armValid lookup
  have distinct : ports.Nodup :=
    List.Pairwise.of_map Port.token (fun _ _ different same => different (congrArg Port.token same))
      (tokens.symm ▸ keys)
  have size : ports.length = arm.live.length := by
    have equal := congrArg List.length tokens
    simpa only [List.length_map,count] using equal
  obtain ⟨ordered,permutation,sublist⟩ := List.subperm_iff.mp (distinct.subperm covered)
  have complete : ports = ordered := sublist.eq_of_length (size.trans permutation.length_eq.symm)
  have live : ports.Perm arm.live := complete ▸ permutation
  rw [← wires]
  exact ⟨(live.flatMap_right Port.wires).trans (RuntimeCallTraceFrames.native_wires arm armValid),width⟩

theorem complete_phi_has_no_spectators {pLeft pRight cLeft cRight : Raw.State}
    (phis : List QuantumPhi) (pValid : phiValid pLeft pRight phis = true)
    (cValid : phiValid cLeft cRight phis = true) {spectators : List Port}
    (live : pLeft.live.Perm (cLeft.live ++ spectators)) : spectators = [] := by
  simp only [phiValid,Bool.and_eq_true,beq_iff_eq] at pValid cValid
  have same : pLeft.live.length = cLeft.live.length := pValid.1.1.1.1.2.symm.trans cValid.1.1.1.1.2
  have count := live.length_eq
  rw [List.length_append,same] at count
  exact List.length_eq_zero_iff.mp (by omega)

/-- Both actual readers reorder the same input wires to the common phi
destination frame. The input and destination wire identities stay distinct. -/
theorem paired_phi_reorder {dependencies : List Semantics.Finite.Dependency}
    {pLeft pRight cLeft cRight : Raw.State} (phis : List QuantumPhi) (choice : Bool)
    (pGuard : phiValid pLeft pRight phis = true) (cGuard : phiValid cLeft cRight phis = true)
    {parent child : Raw.State} (pArm : parent = if choice then pLeft else pRight)
    (cArm : child = if choice then cLeft else cRight)
    (pValid : Raw.stateValid parent = true) (cValid : Raw.stateValid child = true)
    (partition : Partition parent.reference child.reference [])
    (finalUnique : (phiInterface phis).frame.Nodup)
    {actual : Qleisli.Semantics.ObservingAction.History}
    {localHistory : Nat → Qleisli.Semantics.ObservingAction.History}
    (agrees : Agrees parent.reference child.reference [] actual localHistory) :
    Agrees (phiInterface phis) (phiInterface phis) []
      (Qleisli.RuntimeNamedThreePackedInstrument.pureHistory dependencies
        [.reorder parent.frame.length (axes parent.reference (phiWires parent.reference phis choice))] actual)
      (fun high => Qleisli.RuntimeNamedThreePackedInstrument.pureHistory dependencies
        [.reorder child.frame.length (axes child.reference (phiWires child.reference phis choice))] (localHistory high)) := by
  have live : parent.live.Perm child.live := by simpa only [List.append_nil] using partition.live
  have same := RuntimeCallTraceFrames.branch_wires live pValid cValid phis choice
  have pGeometry : (phiWires parent.reference phis choice).Perm parent.frame ∧
      (phiWires parent.reference phis choice).length = (phiInterface phis).frame.length := by
    subst parent
    exact phi_arm_geometry pLeft pRight phis pGuard choice pValid
  have cGeometry : (phiWires child.reference phis choice).Perm child.frame ∧
      (phiWires child.reference phis choice).length = (phiInterface phis).frame.length := by
    subst child
    exact phi_arm_geometry cLeft cRight phis cGuard choice cValid
  have pAxes := (pGeometry.1.map parent.frame.idxOf).trans
    (List.Perm.of_eq (RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ pValid).frame))
  have cAxes := (cGeometry.1.map child.frame.idxOf).trans
    (List.Perm.of_eq (RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ cValid).frame))
  rw [same] at pAxes ⊢
  exact reorder_join dependencies parent.reference child.reference (phiInterface phis) _
    cGeometry.1.subset finalUnique cGeometry.2.symm pAxes cAxes agrees

#print axioms phi_arm_geometry
#print axioms paired_phi_reorder
end Qleisli.RuntimeCallHistory
