import Qleisli.RuntimeCallHistoryPure
import Qleisli.RuntimeCallTraceProjection

/-! The two actual branch arms reorder their physical rows into the same
written output frame, then apply the same simultaneous classical phis.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Finite (Dependency gather)
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface axes)
open Semantics.Observation (ClassicalPhi)
open Qleisli.Semantics.ObservingAction (History merge)
open Qleisli.RuntimeNamedThreePackedOutput (gather_bijective reorder_gather)
open Qleisli.RuntimeForestProduct (gather_bound)
open Qleisli.RuntimeOriginalObservation (gather_retained)

private theorem merge_pair {parent child : Interface} {spectators : List Port}
    (choice : Bool) (phis : List ClassicalPhi) {actual next : History} {localHistory : Nat → History}
    (agrees : Agrees parent child spectators actual localHistory)
    (executed : merge choice phis actual = some next) :
    ∃ localNext, (∀ high, merge choice phis (localHistory high) = some (localNext high)) ∧
      Agrees parent child spectators next localNext := by
  unfold merge at executed
  obtain ⟨writes,found,done⟩ := Option.bind_eq_some_iff.mp executed
  have same : {actual with values := actual.values++writes} = next := Option.some.inj done
  subst next
  let localNext := fun high => {localHistory high with values := (localHistory high).values++writes}
  refine ⟨localNext,?_,⟨?_,agrees.hidden,agrees.operator⟩⟩
  · intro high
    unfold merge
    rw [← agrees.values high,found]
    dsimp only [localNext,bind,pure,Option.bind]
    rw [agrees.values high]
  · intro high
    exact congrArg (fun values => values++writes) (agrees.values high)

/-- Run the written simultaneous phi merge over every history in order. The
child uses the same already computed ordinary values for every phi input. -/
theorem merge_family {parent child : Interface} {spectators : List Port}
    (choice : Bool) (phis : List ClassicalPhi) {parents merged : List History} {children : List (Nat → History)}
    (paired : List.Forall₂ (Agrees parent child spectators) parents children)
    (executed : parents.mapM (merge choice phis) = some merged) :
    ∃ localMerged, (∀ high, (children.map (fun history => history high)).mapM (merge choice phis) =
      some (localMerged.map (fun history => history high))) ∧
      List.Forall₂ (Agrees parent child spectators) merged localMerged := by
  induction paired generalizing merged with
  | nil =>
    have same : [] = merged := Option.some.inj executed
    subst merged
    exact ⟨[],fun _ => rfl,.nil⟩
  | @cons actual localHistory parents children agrees _ ih =>
    simp only [List.mapM_cons] at executed
    obtain ⟨first,read,rest⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨tail,tailRead,done⟩ := Option.bind_eq_some_iff.mp rest
    have same : first::tail = merged := Option.some.inj done
    subst merged
    obtain ⟨localFirst,firstRuns,firstAgrees⟩ := merge_pair choice phis agrees read
    obtain ⟨localTail,tailRuns,tailAgrees⟩ := ih tailRead
    refine ⟨localFirst::localTail,?_,.cons firstAgrees tailAgrees⟩
    intro high
    rw [List.map_cons,List.mapM_cons,firstRuns high,tailRuns high,List.map_cons]
    rfl

/-- At a complete branch join the same written output wires cover both arm
frames. The two actual permutations then select corresponding input rows. -/
theorem reorder_join (dependencies : List Dependency) (parent child final : Interface)
    (ordered : List Nat) (inside : ordered ⊆ child.frame) (unique : final.frame.Nodup)
    (sameWidth : final.frame.length = ordered.length)
    (parentAxes : (axes parent ordered).Perm (List.range parent.frame.length))
    (childAxes : (axes child ordered).Perm (List.range child.frame.length))
    {actual : History} {localHistory : Nat → History}
    (agrees : Agrees parent child [] actual localHistory) :
    Agrees final final []
      (Qleisli.RuntimeNamedThreePackedInstrument.pureHistory dependencies
        [.reorder parent.frame.length (axes parent ordered)] actual)
      (fun high => Qleisli.RuntimeNamedThreePackedInstrument.pureHistory dependencies
        [.reorder child.frame.length (axes child ordered)] (localHistory high)) := by
  refine ⟨agrees.values,agrees.hidden,?_⟩
  intro row col bounded
  have parentWidth : final.frame.length = parent.frame.length := by
    exact sameWidth.trans (by simpa only [axes,List.length_map,List.length_range] using parentAxes.length_eq)
  have childWidth : final.frame.length = child.frame.length := by
    exact sameWidth.trans (by simpa only [axes,List.length_map,List.length_range] using childAxes.length_eq)
  have rowIdentity : project final final.frame row = row := by
    unfold project axes
    rw [RuntimeNamedCallerAction.self_indices _ unique]
    exact Raw.Sector.gather_identity _ _ bounded
  let event := Qleisli.Semantics.RawAction.event dependencies
  change event (.reorder parent.frame.length (axes parent ordered)) (fun r => actual.operator r col) row =
    event (.reorder child.frame.length (axes child ordered)) (fun r => (localHistory 0).operator r col)
      (project final final.frame row)
  rw [rowIdentity]
  obtain ⟨pInput,pBound,pAt,pAct⟩ := reorder_gather dependencies _ _ parentAxes
    (fun r => actual.operator r col) row (parentWidth ▸ bounded)
  obtain ⟨cInput,cBound,cAt,cAct⟩ := reorder_gather dependencies _ _ childAxes
    (fun r => (localHistory 0).operator r col) row (childWidth ▸ bounded)
  dsimp only [event]
  rw [pAct,cAct]
  have projected : project parent child.frame pInput < 2^child.frame.length := by
    simpa only [project,axes,List.length_map] using gather_bound pInput (axes parent child.frame)
  have selected : gather (project parent child.frame pInput) (axes child ordered) = row :=
    (gather_retained parent.frame child.frame ordered _ rfl inside pInput).trans pAt
  obtain ⟨reindex,bij,equation⟩ := gather_bijective child.frame.length (axes child ordered) childAxes
  let p : Fin (2^child.frame.length) := ⟨project parent child.frame pInput,projected⟩
  let c : Fin (2^child.frame.length) := ⟨cInput,cBound⟩
  have same := congrArg Fin.val (bij.1 (Fin.ext ((equation p).trans (selected.trans (cAt.symm.trans (equation c).symm)))))
  exact (agrees.operator pInput col pBound).trans
    (congrArg (fun r => (localHistory 0).operator r col) same)

#print axioms merge_family
#print axioms reorder_join
end Qleisli.RuntimeCallHistory
