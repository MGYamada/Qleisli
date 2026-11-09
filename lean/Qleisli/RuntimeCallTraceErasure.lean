import Qleisli.RuntimeCallTraceFrames
import Qleisli.RuntimeOriginalObservation

/-! Erasure through an original named-call frame preserves the complete
spectator coordinate. This pointwise comparison applies to each possible
outcome and arbitrary correlated input amplitudes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallTraceErasure
open QleisliKernel
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes take)
open Semantics.Observation (remaining)
open Semantics.Finite (gather)
open Qleisli.RuntimeCallTraceFrames (Partition WireOrder taken_member)
open Qleisli.RuntimeOriginalObservation (erase_at erasure_frame_geometry gather_retained)
open Qleisli.RuntimeNamedThreePackedOutput (gather_bijective)
open Qleisli.RuntimeForestProduct (gather_append gather_bound)
open Qleisli.Semantics.ObservingAction (erase)

/-- A parent erasure outcome and its exact local counterpart apply the same
projection to the selected coordinates. Every spectator bit is taken from the
real compressed parent row, with no product-state assumption. -/
theorem erase_correlated (parent child : Raw.State) (spectators : List Port)
    (partition : Partition parent.reference child.reference spectators)
    (parentValid : Raw.stateValid parent = true) (childValid : Raw.stateValid child = true)
    {token : Nat} {port : Port} {taken : Interface}
    (childTake : take child.reference token = some (port,taken))
    (joint : Nat → Nat → ℂ) (outcome row : Nat) (outcomeBound : outcome < 2^port.wires.length)
    (rowBound : row < 2^(remaining parent.reference port.wires).length) :
    erase parent.frame.length (axes parent.reference port.wires) outcome
      (fun input => joint (gather input (child.frame.map parent.frame.idxOf))
        (gather input ((WireOrder spectators).map parent.frame.idxOf))) row =
    erase child.frame.length (axes child.reference port.wires) outcome
      (fun input => joint input
        (gather row ((WireOrder spectators).map (remaining parent.reference port.wires).idxOf)))
      (gather row ((remaining child.reference port.wires).map (remaining parent.reference port.wires).idxOf)) := by
  let pFrame := parent.frame
  let cFrame := child.frame
  let other := WireOrder spectators
  let pAfter := remaining parent.reference port.wires
  let cAfter := remaining child.reference port.wires
  let pAxes := axes parent.reference port.wires
  let cAxes := axes child.reference port.wires
  let pKept := pAfter.map pFrame.idxOf
  let cKept := cAfter.map cFrame.idxOf
  let localRow := gather row (cAfter.map pAfter.idxOf)
  let environment := gather row (other.map pAfter.idxOf)
  have parentFacts := Raw.Ownership.valid parent parentValid
  have childFacts := Raw.Ownership.valid child childValid
  have member := taken_member childTake
  have wireUnique : port.wires.Nodup := (List.nodup_flatMap.mp childFacts.exclusive).1 port member
  have inChild : port.wires ⊆ cFrame := fun wire inside =>
    childFacts.covered wire (List.mem_flatMap.mpr ⟨port,member,inside⟩)
  have cInside : cFrame ⊆ pFrame := fun _ inside =>
    partition.frame.mem_iff.mpr (List.mem_append_left _ inside)
  have cAfterInside : cAfter ⊆ cFrame := fun _ inside => (List.mem_filter.mp inside).1
  have cInAfter : cAfter ⊆ pAfter := by
    intro wire inside
    obtain ⟨present,kept⟩ := List.mem_filter.mp inside
    exact List.mem_filter.mpr ⟨cInside present,kept⟩
  have inParent : port.wires ⊆ pFrame := fun _ inside => cInside (inChild inside)
  have disjoint := (List.nodup_append.mp (partition.frame.nodup_iff.mp parentFacts.frame)).2.2
  have otherInAfter : other ⊆ pAfter := by
    intro wire present
    apply List.mem_filter.mpr
    refine ⟨partition.frame.mem_iff.mpr (List.mem_append_right _ present),?_⟩
    have absent : wire ∉ port.wires := fun bad => disjoint wire (inChild bad) wire present rfl
    simp [absent]
  have pGeometry : pKept = (List.range pFrame.length).filter (fun axis => !pAxes.contains axis) ∧
      (pAxes++pKept).Perm (List.range pFrame.length) :=
    erasure_frame_geometry pFrame port.wires parentFacts.frame wireUnique inParent
  have cGeometry : cKept = (List.range cFrame.length).filter (fun axis => !cAxes.contains axis) ∧
      (cAxes++cKept).Perm (List.range cFrame.length) :=
    erasure_frame_geometry cFrame port.wires childFacts.frame wireUnique inChild
  have localBound : localRow < 2^cAfter.length := by
    simpa only [localRow,List.length_map] using gather_bound row (cAfter.map pAfter.idxOf)
  obtain ⟨pInput,pHit,pKeep,pValue⟩ := erase_at pFrame.length pAxes outcome row
    (fun input => joint (gather input (cFrame.map pFrame.idxOf)) (gather input (other.map pFrame.idxOf)))
    (by rw [← pGeometry.1]; exact pGeometry.2)
    (by simpa only [pAxes,axes,List.length_map] using outcomeBound)
    (by rw [← pGeometry.1]; simpa only [pKept,List.length_map] using rowBound)
  obtain ⟨cInput,cHit,cKeep,cValue⟩ := erase_at cFrame.length cAxes outcome localRow
    (fun input => joint input environment)
    (by rw [← cGeometry.1]; exact cGeometry.2)
    (by simpa only [cAxes,axes,List.length_map] using outcomeBound)
    (by rw [← cGeometry.1]; simpa only [cKept,List.length_map] using localBound)
  rw [← pGeometry.1] at pKeep
  rw [← cGeometry.1] at cKeep
  let projected := gather pInput.val (cFrame.map pFrame.idxOf)
  have projectedBound : projected < 2^cFrame.length := by
    simpa only [projected,List.length_map] using gather_bound pInput.val (cFrame.map pFrame.idxOf)
  have projectedHit : gather projected cAxes = outcome :=
    (gather_retained pFrame cFrame port.wires _ rfl inChild pInput.val).trans pHit
  have projectedKeep : gather projected cKept = localRow := by
    calc
      _ = gather pInput.val (cAfter.map pFrame.idxOf) :=
        gather_retained pFrame cFrame cAfter _ rfl cAfterInside pInput.val
      _ = gather (gather pInput.val pKept) (cAfter.map pAfter.idxOf) :=
        (gather_retained pFrame pAfter cAfter _ rfl cInAfter pInput.val).symm
      _ = localRow := by rw [pKeep]
  have unchanged : gather pInput.val (other.map pFrame.idxOf) = environment := by
    rw [← gather_retained pFrame pAfter other _ rfl otherInAfter pInput.val,pKeep]
  have projectedEq : projected = cInput.val := by
    obtain ⟨project,bij,equation⟩ := gather_bijective cFrame.length (cAxes++cKept) cGeometry.2
    let index : Fin (2^cFrame.length) := ⟨projected,projectedBound⟩
    have same : gather index.val (cAxes++cKept) = gather cInput.val (cAxes++cKept) := by
      change gather projected (cAxes++cKept) = _
      simp only [gather_append,projectedHit,cHit,projectedKeep,cKeep]
    exact congrArg Fin.val (bij.1 (Fin.ext ((equation index).trans (same.trans (equation cInput).symm))))
  change erase pFrame.length pAxes outcome _ row = erase cFrame.length cAxes outcome _ localRow
  rw [pValue,cValue]
  exact congrArg₂ joint projectedEq unchanged

#print axioms erase_correlated
end Qleisli.RuntimeCallTraceErasure
