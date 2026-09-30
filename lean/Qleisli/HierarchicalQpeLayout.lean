import Qleisli.HierarchicalQpeCoordinates
import QleisliKernel.Hierarchical.QpeSchedule

/-! Physical coordinate and exact-event consequences of the actual QPE layout
check. The request's ordered phase/target arrays determine the canonical input
permutation; the separately checked output route is retained verbatim.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.HierarchicalQpeLayout
open QleisliKernel.Hierarchical
open HierarchicalQpeCoordinates

theorem layout_fields (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true) :
    (request.phase ++ request.target).toList.Perm (List.range (request.phase.size+request.target.size)) ∧
    request.route.toList.Perm (List.range (request.phase.size+request.target.size)) := by
  simp only [QpeSchedule.layout,Bool.and_eq_true,decide_eq_true_eq] at valid
  exact ⟨valid.1.2,valid.2⟩

noncomputable def inputRoute (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true) :
    Equiv.Perm (Fin (request.phase.size+request.target.size)) :=
  HierarchicalCircuitTrace.permutation _ (request.phase ++ request.target).toList (layout_fields request valid).1

noncomputable def outputRoute (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true) :
    Equiv.Perm (Fin (request.phase.size+request.target.size)) :=
  HierarchicalCircuitTrace.permutation _ request.route.toList (layout_fields request valid).2

theorem inputRoute_phase (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true)
    (i : Fin request.phase.size) :
    (inputRoute request valid (i.castAdd request.target.size)).val = request.phase[i] := by
  rw [inputRoute,HierarchicalCircuitTrace.permutation_val]
  simp [QleisliKernel.Layout.indexAt,Array.toList_append,List.getElem?_append,i.isLt]

theorem inputRoute_target (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true)
    (i : Fin request.target.size) :
    (inputRoute request valid (i.natAdd request.phase.size)).val = request.target[i] := by
  rw [inputRoute,HierarchicalCircuitTrace.permutation_val]
  simp [QleisliKernel.Layout.indexAt,Array.toList_append,i.isLt]

theorem inputRoute_phase_list (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true) :
    List.ofFn (fun i : Fin request.phase.size =>
      (inputRoute request valid (i.castAdd request.target.size)).val) = request.phase.toList := by
  simp only [inputRoute_phase]
  exact List.ofFn_getElem

theorem inputRoute_control_list (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true)
    (axis : Fin request.phase.size) :
    List.ofFn (fun i : Fin (request.target.size+1) =>
      (inputRoute request valid (controlPositions request.phase.size request.target.size axis i)).val) =
      request.phase[axis] :: request.target.toList := by
  rw [List.ofFn_succ]
  simp only [controlPositions,Fin.cons_zero,Fin.cons_succ,inputRoute_phase,inputRoute_target]
  congr 1
  exact List.ofFn_getElem

/-- Actual candidate indices, transported only across the checked array length. -/
def indices (width : Nat) (atoms : Array CircuitTrace.Atom) (size : atoms.size = width) : Fin width → Nat :=
  fun axis => (atoms[axis.val]'(by omega)).index

theorem hadamard_events (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true)
    (atoms : Array CircuitTrace.Atom) (size : atoms.size = request.phase.size) :
    (atoms.mapIdx (fun k atom => (⟨atom.index,[request.phase[k]!]⟩ : CircuitTrace.Event))).toList =
      List.ofFn (fun axis : Fin request.phase.size =>
        (⟨indices request.phase.size atoms size axis,
          List.ofFn (fun _ : Fin 1 => (inputRoute request valid (axis.castAdd request.target.size)).val)⟩ : CircuitTrace.Event)) := by
  apply List.ext_getElem
  · simp [size]
  · intro i left right
    have bound : i < request.phase.size := by simpa using right
    simp [indices,inputRoute_phase,bound]

theorem power_events (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true)
    (atoms : Array CircuitTrace.Atom) (size : atoms.size = request.phase.size) :
    (atoms.mapIdx (fun k atom => (⟨atom.index,request.phase[k]!::request.target.toList⟩ : CircuitTrace.Event))).toList =
      List.ofFn (fun axis : Fin request.phase.size =>
        (⟨indices request.phase.size atoms size axis,
          List.ofFn (fun i : Fin (request.target.size+1) =>
            (inputRoute request valid (controlPositions request.phase.size request.target.size axis i)).val)⟩ : CircuitTrace.Event)) := by
  apply List.ext_getElem
  · simp [size]
  · intro i left right
    have bound : i < request.phase.size := by simpa using right
    simp only [Array.getElem_toList,Array.getElem_mapIdx,List.getElem_ofFn]
    rw [inputRoute_control_list]
    simp [indices,bound]

/-- The executable checker's expected trace is exactly the mathematical
coordinate schedule. No independently supplied event trace is assumed. -/
theorem expected_eq (request : QpeSchedule.Request) (valid : QpeSchedule.layout request = true)
    (candidate : QpeSchedule.Candidate)
    (hs : candidate.hadamards.size = request.phase.size)
    (ps : candidate.powers.size = request.phase.size) :
    QpeSchedule.expected request candidate =
      expectedTrace request.phase.size request.target.size (inputRoute request valid) (outputRoute request valid)
        (indices request.phase.size candidate.hadamards hs) (indices request.phase.size candidate.powers ps)
        candidate.inverseFourier.index := by
  have route : List.ofFn (fun i => (outputRoute request valid i).val) = request.route.toList :=
    HierarchicalCircuitTrace.permutation_list _ _ _
  unfold QpeSchedule.expected expectedTrace
  rw [route]
  congr 1
  apply Array.toList_inj.mp
  simp only [expectedEvents,Array.toList_append]
  rw [hadamard_events request valid candidate.hadamards hs,power_events request valid candidate.powers ps,
    inputRoute_phase_list]

end Qleisli.HierarchicalQpeLayout
