import Qleisli.RuntimeCallBranchGeometry
import Qleisli.RuntimeRoutedBranchCoordinates

/-! Recover the positional relation directly from the actual Raw phi lists.
A phi zips each original ordered port with its own written destination wires.
The widths are supplied by the checked Raw arm, including a zero-width port.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes)
open Semantics.Observation (QuantumPhi phiWires phiInterface)
open Raw.Observation (phiValid)
open RuntimeCallTraceFrames (Partition WireOrder)

def incomingWires (arm : Interface) (choice : Bool) (phi : QuantumPhi) : List Nat :=
  ((arm.live.find? (fun port => port.token == (if choice then phi.thenToken else phi.elseToken))).map
    (·.wires)).getD []

private def wirePairs (arm : Interface) (choice : Bool) (phis : List QuantumPhi) : List (Nat × Nat) :=
  phis.flatMap fun phi => phi.wires.zip (incomingWires arm choice phi)

private theorem incoming_port (left right : Raw.State) (phis : List QuantumPhi) (choice : Bool)
    (valid : phiValid left right phis = true)
    (phi : QuantumPhi) (member : phi ∈ phis) :
    ∃ port, (if choice then left else right).live.find?
      (fun port => port.token == (if choice then phi.thenToken else phi.elseToken)) = some port ∧
      phi.wires.length = port.bits := by
  simp only [phiValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have widths := valid.2 phi member
  cases leftRead : left.live.find? (fun port => port.token == phi.thenToken) with
  | none => simp [leftRead] at widths
  | some l =>
    cases rightRead : right.live.find? (fun port => port.token == phi.elseToken) with
    | none => simp [leftRead,rightRead] at widths
    | some r =>
      simp only [leftRead,rightRead,Bool.and_eq_true,beq_iff_eq] at widths
      cases choice
      · exact ⟨r,rightRead,widths.2.trans widths.1⟩
      · exact ⟨l,leftRead,widths.2⟩

theorem incoming_width (left right : Raw.State) (phis : List QuantumPhi) (choice : Bool)
    (valid : phiValid left right phis = true)
    (armValid : Raw.stateValid (if choice then left else right) = true)
    (phi : QuantumPhi) (member : phi ∈ phis) :
    phi.wires.length = (incomingWires (if choice then left else right).reference choice phi).length := by
  obtain ⟨port,read,width⟩ := incoming_port left right phis choice valid phi member
  have found : (if choice then left else right).reference.live.find?
      (fun port => port.token == (if choice then phi.thenToken else phi.elseToken)) = some port := read
  simp only [incomingWires,found,Option.map_some,Option.getD_some]
  exact width.trans ((Raw.Ownership.valid _ armValid).ports port (List.mem_of_find?_eq_some read)).1

private theorem wirePairs_maps (arm : Interface) (choice : Bool) (phis : List QuantumPhi)
    (width : ∀ phi ∈ phis, phi.wires.length = (incomingWires arm choice phi).length) :
    (wirePairs arm choice phis).map Prod.fst = (phiInterface phis).frame ∧
    (wirePairs arm choice phis).map Prod.snd = phiWires arm phis choice := by
  induction phis with
  | nil => exact ⟨rfl,rfl⟩
  | cons head rest ih =>
    have headWidth := width head List.mem_cons_self
    obtain ⟨outWires,inWires⟩ := ih (fun phi member => width phi (List.mem_cons_of_mem _ member))
    constructor
    · change ((head.wires.zip (incomingWires arm choice head) ++ wirePairs arm choice rest).map Prod.fst) =
        head.wires ++ (phiInterface rest).frame
      rw [List.map_append,List.map_fst_zip headWidth.le,outWires]
    · change ((head.wires.zip (incomingWires arm choice head) ++ wirePairs arm choice rest).map Prod.snd) =
        incomingWires arm choice head ++ phiWires arm rest choice
      rw [List.map_append,List.map_snd_zip headWidth.ge,inWires]

private theorem wirePair_axis (arm : Interface) (choice : Bool) (phis : List QuantumPhi)
    (width : ∀ phi ∈ phis, phi.wires.length = (incomingWires arm choice phi).length)
    (distinct : (phiInterface phis).frame.Nodup) {pair : Nat × Nat}
    (member : pair ∈ wirePairs arm choice phis) :
    (axes arm (phiWires arm phis choice))[(phiInterface phis).frame.idxOf pair.1]? =
      some (arm.frame.idxOf pair.2) := by
  obtain ⟨destinations,sources⟩ := wirePairs_maps arm choice phis width
  obtain ⟨index,bound,found⟩ := List.getElem_of_mem member
  have destinationBound : index < (phiInterface phis).frame.length := by rw [← destinations,List.length_map]; exact bound
  have originRead : (phiInterface phis).frame[index]? = some pair.1 := by
    rw [← destinations,List.getElem?_map,List.getElem?_eq_getElem bound,found]
    rfl
  have origin : (phiInterface phis).frame[index] = pair.1 := (List.getElem?_eq_some_iff.mp originRead).2
  have slot := distinct.idxOf_getElem index destinationBound
  rw [origin] at slot
  unfold axes
  rw [slot,← sources,List.getElem?_map,List.getElem?_map,List.getElem?_eq_getElem bound,found]
  rfl

/-- An actual phi's own output wire points to exactly the corresponding
ordered input wire of that same phi and selected arm. -/
theorem raw_phi_axis (left right : Raw.State) (phis : List QuantumPhi) (choice : Bool)
    (valid : phiValid left right phis = true)
    (armValid : Raw.stateValid (if choice then left else right) = true)
    (distinct : (phiInterface phis).frame.Nodup)
    (phi : QuantumPhi) (member : phi ∈ phis) (pair : Nat × Nat)
    (paired : pair ∈ phi.wires.zip (incomingWires (if choice then left else right).reference choice phi)) :
    let arm := (if choice then left else right).reference
    (axes arm (phiWires arm phis choice))[(phiInterface phis).frame.idxOf pair.1]? =
      some (arm.frame.idxOf pair.2) := by
  exact wirePair_axis _ choice phis (incoming_width left right phis choice valid armValid) distinct
    (List.mem_flatMap.mpr ⟨phi,member,paired⟩)

/-- Every selected projected phi is a literal phi of the parent branch and
reads the same actual selected port. Distinct destination names in the
spectator phis therefore cannot shift a selected logical axis. -/
theorem selected_phi_slots (pLeft pRight cLeft cRight : Raw.State) (parentPhis childPhis : List QuantumPhi)
    (choice : Bool) (selected : childPhis ⊆ parentPhis)
    (parentValid : phiValid pLeft pRight parentPhis = true)
    (childValid : phiValid cLeft cRight childPhis = true)
    (pArmValid : Raw.stateValid (if choice then pLeft else pRight) = true)
    (cArmValid : Raw.stateValid (if choice then cLeft else cRight) = true)
    (parentDistinct : (phiInterface parentPhis).frame.Nodup)
    {spectators : List Port}
    (partition : Partition (if choice then pLeft else pRight).reference
      (if choice then cLeft else cRight).reference spectators) :
    let pArm := (if choice then pLeft else pRight).reference
    let cArm := (if choice then cLeft else cRight).reference
    List.Forall₂ (fun full localAxis => ∃ old,
      (axes pArm (phiWires pArm parentPhis choice))[full]? = some old ∧
        (axes pArm cArm.frame)[localAxis]? = some old)
      (axes (phiInterface parentPhis) (phiInterface childPhis).frame)
      (axes cArm (phiWires cArm childPhis choice)) := by
  intro pArm cArm
  have sameInput (phi : QuantumPhi) (member : phi ∈ childPhis) :
      incomingWires pArm choice phi = incomingWires cArm choice phi := by
    obtain ⟨port,localRead,_⟩ := incoming_port cLeft cRight childPhis choice childValid phi member
    let token := if choice then phi.thenToken else phi.elseToken
    have childRead : cArm.live.find? (fun p => p.token == token) = some port := localRead
    have key : port.token = token :=
      beq_iff_eq.mp (List.find?_some (p := fun p : Port => p.token == token) childRead)
    have held := partition.live.mem_iff.mpr (List.mem_append_left _ (List.mem_of_find?_eq_some childRead))
    have found := RuntimeNamedFrameAxes.tokenLookup pArm.live port
      (Raw.Ownership.valid _ pArmValid).owners held
    change pArm.live.find? (fun p => p.token == port.token) = some port at found
    rw [key] at found
    simp only [incomingWires,show (if choice then phi.thenToken else phi.elseToken) = token from rfl,found,childRead]
  have maps := wirePairs_maps cArm choice childPhis (incoming_width cLeft cRight childPhis choice childValid cArmValid)
  rw [← maps.1,← maps.2]
  simp only [axes,List.map_map,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same,Function.comp_def]
  intro pair member
  refine ⟨pArm.frame.idxOf pair.2,?_,?_⟩
  · obtain ⟨phi,inside,paired⟩ := List.mem_flatMap.mp member
    exact raw_phi_axis pLeft pRight parentPhis choice parentValid pArmValid parentDistinct phi (selected inside) pair
      (by rwa [sameInput phi inside])
  · have inWires : pair.2 ∈ phiWires cArm childPhis choice := maps.2 ▸ List.mem_map_of_mem member
    have inside : pair.2 ∈ cArm.frame :=
      (phi_arm_geometry cLeft cRight childPhis childValid choice cArmValid).1.subset inWires
    rw [List.getElem?_map,RuntimeNamedFrameAxes.wireLookup _ inside]
    rfl

#print axioms raw_phi_axis
#print axioms selected_phi_slots
end Qleisli.RuntimeCallHistory
