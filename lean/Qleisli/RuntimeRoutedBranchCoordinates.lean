import Qleisli.RuntimeCallHistoryPhi

/-! Transport arbitrary caller/spectator components through the two actual
literal branch reorders. The parent and local programs use different wire
numbers after their phis, and each paired axis follows its own old wire.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Finite (Dependency bit gather)
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes)
open RuntimeCallTraceFrames (WireOrder)
open Qleisli.Semantics.ObservingAction (History)
open Qleisli.RuntimeForestProduct (gather_append gather_bound)
open Qleisli.RuntimeNamedThreePackedOutput (gather_bijective reorder_gather)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory)

private theorem gather_cons (row first : Nat) (remaining : List Nat) :
    gather row (first::remaining) = bit row first+2*gather row remaining := by
  simpa only [List.singleton_append,List.length_singleton,
    RuntimeTargetScatter.gather_one,Nat.pow_one] using gather_append row [first] remaining

private theorem bit_along {row axis original : Nat} {permutation : List Nat}
    (found : permutation[axis]? = some original) :
    bit (gather row permutation) axis = bit row original := by
  obtain ⟨inside,exactAxis⟩ := List.getElem?_eq_some_iff.mp found
  rw [QleisliKernel.Qirf.RuntimeScatterTransport.gather_at _ _ _ inside,exactAxis]

/-- For each spectator slot, the new slot reads its own old axis. The
token and the physical wire names on opposite sides need not be equal. -/
theorem gather_spectator_phi {permutation current original : List Nat}
    (slots : List.Forall₂ (fun new old => permutation[new]? = some old) current original)
    (row : Nat) : gather (gather row permutation) current = gather row original := by
  induction slots with
  | nil => rfl
  | @cons new old _ _ here _ rest =>
    rw [gather_cons,gather_cons,bit_along here,rest]

/-- The same selected arm axis is found through the full parent permutation
and through the selected projection's own permutation. -/
theorem gather_selected_phi {full selection current projected : List Nat}
    (slots : List.Forall₂ (fun new childAxis => ∃ old, full[new]? = some old ∧ selection[childAxis]? = some old)
      current projected)
    (row : Nat) :
    gather (gather row full) current = gather (gather row selection) projected := by
  induction slots with
  | nil => rfl
  | @cons new childAxis _ _ here _ rest =>
    obtain ⟨_,left,right⟩ := here
    rw [gather_cons,gather_cons,bit_along left,bit_along right,rest]

/-- A join can replace the parked ports and their wire identifiers while
preserving every spectator coordinate. The arbitrary reference column is
shared by the actual caller operator and the selected-child operator. -/
theorem reorder_join_with_spectator_phis (dependencies : List Dependency)
    {parent child parentAfter childAfter : Interface} {beforeSpectators afterSpectators : List Port}
    (parentAxes childAxes : List Nat)
    (parentOrder : parentAxes.Perm (List.range parent.frame.length))
    (childOrder : childAxes.Perm (List.range child.frame.length))
    (parentWidth : parentAfter.frame.length = parent.frame.length)
    (childWidth : childAfter.frame.length = child.frame.length)
    (spectatorSlots : List.Forall₂ (fun new old => parentAxes[new]? = some old)
      (axes parentAfter (WireOrder afterSpectators)) (axes parent (WireOrder beforeSpectators)))
    (childSlots : List.Forall₂ (fun new childAxis => ∃ old, parentAxes[new]? = some old ∧
      (axes parent child.frame)[childAxis]? = some old) (axes parentAfter childAfter.frame) childAxes)
    {actual : History} {localHistory : Nat → History}
    (agrees : Agrees parent child beforeSpectators actual localHistory) :
    Agrees parentAfter childAfter afterSpectators
      (pureHistory dependencies [.reorder parent.frame.length parentAxes] actual)
      (fun high => pureHistory dependencies [.reorder child.frame.length childAxes] (localHistory high)) := by
  refine ⟨agrees.values,agrees.hidden,?_⟩
  intro row col bounded
  let high := project parentAfter (WireOrder afterSpectators) row
  let low := project parentAfter childAfter.frame row
  let event := Qleisli.Semantics.RawAction.event dependencies
  change event (.reorder parent.frame.length parentAxes) (fun r => actual.operator r col) row =
    event (.reorder child.frame.length childAxes) (fun r => (localHistory high).operator r col) low
  have lowBound : low < 2^child.frame.length := by
    rw [← childWidth]
    simpa only [low,project,axes,List.length_map] using gather_bound row (axes parentAfter childAfter.frame)
  obtain ⟨parentInput,parentBound,parentAt,parentAct⟩ :=
    reorder_gather dependencies _ _ parentOrder (fun r => actual.operator r col) row (parentWidth ▸ bounded)
  obtain ⟨childInput,childBound,childAt,childAct⟩ :=
    reorder_gather dependencies _ _ childOrder (fun r => (localHistory high).operator r col) low lowBound
  dsimp only [event]
  rw [parentAct,childAct,agrees.operator parentInput col parentBound]
  have highSame : project parent (WireOrder beforeSpectators) parentInput = high := by
    unfold high project
    rw [← parentAt,gather_spectator_phi spectatorSlots]
  rw [highSame]
  have lowSame : gather (project parent child.frame parentInput) childAxes = low := by
    unfold low project
    rw [← parentAt,gather_selected_phi childSlots]
  have projectedBound : project parent child.frame parentInput < 2^child.frame.length := by
    simpa only [project,axes,List.length_map] using gather_bound parentInput (axes parent child.frame)
  obtain ⟨projection,bijective,coordinates⟩ := gather_bijective child.frame.length childAxes childOrder
  let selected : Fin (2^child.frame.length) := ⟨project parent child.frame parentInput,projectedBound⟩
  let returned : Fin (2^child.frame.length) := ⟨childInput,childBound⟩
  have same : selected = returned := bijective.1 (Fin.ext
    ((coordinates selected).trans (lowSame.trans (childAt.symm.trans (coordinates returned).symm))))
  exact congrArg (fun r : Fin (2^child.frame.length) => (localHistory high).operator r.val col) same

#print axioms reorder_join_with_spectator_phis
end Qleisli.RuntimeCallHistory
