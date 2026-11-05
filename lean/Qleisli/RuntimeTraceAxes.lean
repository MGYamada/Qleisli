import Init.Data.List.Find
import QleisliKernel.Semantics.RawTrace
import QleisliKernel.Finite

/-! Original wire indices and exact composition of Raw step localization.
Wire membership supplies the actual inner index. Every original control and
operation target must be inside the inner axis list: default-zero lookup does
not compose at an out-of-range original index. Whole Step equality preserves
polarity, action kind, tables, phases, dependency index and adjoint fields.
These are proof lemmas, not runtime gates or complete per-operation locality.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeTraceAxes
open QleisliKernel QleisliKernel.Semantics.Finite

/-- Membership suffices even without a distinctness assumption: idxOf returns
an actual occurrence of this same wire, never an equal-width substitute. -/
theorem wire_axis (callerFrame selectedFrame : List Nat) (wire : Nat) (member : wire ∈ selectedFrame) :
    (selectedFrame.map callerFrame.idxOf)[selectedFrame.idxOf wire]?.getD 0 = callerFrame.idxOf wire := by
  induction selectedFrame with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : first = wire
    · subst first
      simp
    · have remaining : wire ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      have skipped : (first == wire) = false :=
        Bool.eq_false_iff.mpr (fun equal => same (beq_iff_eq.mp equal))
      simpa [List.idxOf_cons,skipped] using ih remaining

/-- The actual ordered wires are read through the fixed original local and
caller frames. Empty wire lists remain empty; no contiguity is assumed. -/
theorem wire_axes (callerFrame selectedFrame wires : List Nat)
    (covered : ∀ wire ∈ wires, wire ∈ selectedFrame) :
    (wires.map selectedFrame.idxOf).map
        (fun index => (selectedFrame.map callerFrame.idxOf)[index]?.getD 0) = wires.map callerFrame.idxOf := by
  rw [List.map_map]
  apply List.map_congr_left
  intro wire member
  exact wire_axis callerFrame selectedFrame wire (covered wire member)

private theorem lookup_comp (outer inner : List Nat) (index : Nat) (bound : index < inner.length) :
    outer[inner[index]?.getD 0]?.getD 0 = (inner.map (fun axis => outer[axis]?.getD 0))[index]?.getD 0 := by
  simp only [List.getElem?_map,List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some]

/-- Both maps keep the original axis order. The explicit original-index bound
is necessary because getD 0 at a missing inner index otherwise changes meaning. -/
theorem map_lookup_comp (outer inner indices : List Nat) (bounded : ∀ index ∈ indices, index < inner.length) :
    (indices.map (fun index => inner[index]?.getD 0)).map (fun index => outer[index]?.getD 0) =
      indices.map (fun index => (inner.map (fun axis => outer[axis]?.getD 0))[index]?.getD 0) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro index member
  exact lookup_comp outer inner index (bounded index member)

/-- Exact equality of the SAME original Step after nested localization. Bounds
refer to the original controls and targets in the INNER axis list, including
contract targets. No control polarity or non-axis action field is rewritten. -/
theorem localize_comp (outer inner : List Nat) (original : Step)
    (controls : ∀ control ∈ original.controls, control.index < inner.length)
    (targets : ∀ axis ∈ Finite.targets original.action, axis < inner.length) :
    Semantics.RawTrace.localize outer (Semantics.RawTrace.localize inner original) =
      Semantics.RawTrace.localize (inner.map (fun axis => outer[axis]?.getD 0)) original := by
  rcases original with ⟨written,action⟩
  have controlMap :
      (written.map (fun control => (⟨inner[control.index]?.getD 0,control.whenOne⟩ : Control))).map
          (fun control => (⟨outer[control.index]?.getD 0,control.whenOne⟩ : Control)) =
        written.map (fun control => (⟨(inner.map (fun axis => outer[axis]?.getD 0))[control.index]?.getD 0,
          control.whenOne⟩ : Control)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro control member
    exact congrArg (fun index => (⟨index,control.whenOne⟩ : Control))
      (lookup_comp outer inner control.index (controls control member))
  cases action with
  | hadamard axis =>
    have bound := targets axis (List.mem_singleton_self axis)
    simp only [Semantics.RawTrace.localize]
    rw [controlMap,lookup_comp outer inner axis bound]
  | monomial axes permutation phases =>
    have targetMap := map_lookup_comp outer inner axes targets
    simp only [Semantics.RawTrace.localize]
    rw [controlMap,targetMap]
  | contract axes dependency adjoint =>
    have targetMap := map_lookup_comp outer inner axes targets
    simp only [Semantics.RawTrace.localize]
    rw [controlMap,targetMap]

#print axioms wire_axis
#print axioms wire_axes
#print axioms map_lookup_comp
#print axioms localize_comp

end Qleisli.RuntimeTraceAxes
