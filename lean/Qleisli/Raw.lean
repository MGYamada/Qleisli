import QleisliKernel.Raw.Finite
import Qleisli.Finite

/-! Actual VM-25 raw reconstruction and structured cleanup to complex action.
There is no Rust-verifier/extractor premise. Native decoding, original source
preservation and production authority remain separate migration gates.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open QleisliKernel.Raw QleisliKernel.Finite Qleisli.Semantics.Exact

/-- Literal injective maps retain every amplitude, rather than a probability
distribution or equality modulo phase. This includes init0 and output reorder. -/
theorem mapping_meaning (inputBits outputBits : Nat) (labels : List Nat) (actual : Matrix)
    (work left : Nat) (ok : (mapping inputBits outputBits labels).run work = (.ok actual,left))
    (row col : Nat) (hr : row < 2^outputBits) (hc : col < 2^inputBits) :
    entry actual row col = if labels[col]? == some row then 1 else 0 := by
  have record := mapping_value _ _ _ _ _ _ ok
  subst actual
  have meaning : (((List.range (2^outputBits * 2^inputBits)).map fun index =>
      if labels[index % 2^inputBits]? == some (index / 2^inputBits) then Scalar.one else Scalar.zero)).map scalar =
      (List.range (2^outputBits * 2^inputBits)).map (fun index =>
        if labels[index % 2^inputBits]? == some (index / 2^inputBits) then (1 : ℂ) else 0) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro index _
    simp only [Function.comp_apply,beq_iff_eq]
    split
    · exact Exact.scalar_one_meaning
    · exact Exact.scalar_zero_meaning
  have result := Exact.matrix_entry_of_meanings _ _ _ _ row col hr hc meaning
  have positive : 0 < 2^inputBits := Nat.two_pow_pos _
  have div : (row * 2^inputBits + col) / 2^inputBits = row := by
    rw [Nat.add_comm,Nat.add_mul_div_right col row positive,Nat.div_eq_of_lt hc,Nat.zero_add]
  simpa only [div,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hc] using result

/-- Literal embedding of a local operator preserves ordered axes and every
spectator coordinate. Empty axes retain the operator's scalar phase. -/
theorem promote_meaning (bits : Nat) (axes : List Nat) (logical actual : Matrix)
    (work left : Nat) (ok : (promote bits axes logical).run work = (.ok actual,left))
    (row col : Nat) (hr : row < 2^bits) (hc : col < 2^bits) :
    entry actual row col = if scatter col axes (gather row axes) == row then
      entry logical (gather row axes) (gather col axes) else 0 := by
  have record := promote_value _ _ _ _ _ _ ok
  subst actual
  have meaning : (((List.range (2^bits * 2^bits)).map fun index =>
      if scatter (index % 2^bits) axes (gather (index / 2^bits) axes) == index / 2^bits then
        logical.entry (gather (index / 2^bits) axes) (gather (index % 2^bits) axes)
      else Scalar.zero)).map scalar =
      (List.range (2^bits * 2^bits)).map (fun index =>
        if scatter (index % 2^bits) axes (gather (index / 2^bits) axes) == index / 2^bits then
          entry logical (gather (index / 2^bits) axes) (gather (index % 2^bits) axes) else 0) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro index _
    simp only [Function.comp_apply]
    split
    · rfl
    · exact Exact.scalar_zero_meaning
  have result := Exact.matrix_entry_of_meanings _ _ _ _ row col hr hc meaning
  have positive : 0 < 2^bits := Nat.two_pow_pos _
  have div : (row * 2^bits + col) / 2^bits = row := by
    rw [Nat.add_comm,Nat.add_mul_div_right col row positive,Nat.div_eq_of_lt hc,Nat.zero_add]
  simpa only [div,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hc] using result

/-- The concrete zero encoding, reconstructed by the kernel, has no dirty rows.
No caller assumption about a Clean name or a lifetime is used. -/
theorem zeroEncoding_dirty (dataBits ancillaBits : Nat) (encoding : Encoding) (work left : Nat)
    (ok : (zeroEncoding dataBits ancillaBits).run work = (.ok encoding,left))
    (row col : Nat) (dirty : 2^dataBits ≤ row) (hr : row < encoding.map.rows) (hc : col < encoding.map.cols) :
    entry encoding.map row col = 0 := by
  rcases zeroEncoding_value _ _ _ _ _ ok with ⟨_,_,before,after,hm⟩
  have shape := mapping_value _ _ _ _ _ _ hm
  have rows : encoding.map.rows = 2^(dataBits+ancillaBits) := congrArg Matrix.rows shape
  have cols : encoding.map.cols = 2^dataBits := congrArg Matrix.cols shape
  rw [rows] at hr
  rw [cols] at hc
  rw [mapping_meaning _ _ _ _ _ _ hm row col hr hc]
  simp [hc,show col ≠ row by omega]

/-- Every accepted scoped body factors as its actual logical map tensored with
clean auxiliary zero, on arbitrary reference-entangled inputs. The witness is
the full original compute/use/inverse-compute circuit reconstructed by clean. -/
theorem clean_reference {R : Type} (dependencies : List Dependency) (sourceBits dataBits ancillaBits : Nat)
    (function : List Nat) (useSteps logicalSteps : List Step) (logical : Matrix) (work left : Nat)
    (ok : (clean dependencies sourceBits dataBits ancillaBits function useSteps logicalSteps).run work = (.ok logical,left)) :
    ∃ (encoding : Encoding) (physical : Matrix),
      Qleisli.Semantics.Finite.Encoded physical ⟨encoding,encoding,logical⟩ ∧
      (∀ (joint : Nat → R → ℂ) row reference, row < physical.rows →
        action physical (fun index r => action encoding.map joint index r) row reference =
          action encoding.map (fun index r => action logical joint index r) row reference) ∧
      (∀ (joint : Nat → R → ℂ) row reference, 2^dataBits ≤ row → row < physical.rows →
        action physical (fun index r => action encoding.map joint index r) row reference = 0) := by
  rcases clean_conditions _ _ _ _ _ _ _ _ _ _ ok with ⟨encoding,physical,w₁,w₂,w₃,w₄,w₅,w₆,_,he,hp⟩
  have encoded := (Finite.check_encoded _ _ _ _ _ _ _ hp).2
  refine ⟨encoding,physical,encoded,?_,?_⟩
  · intro joint row reference bound
    exact Finite.check_reference _ _ _ _ _ _ _ hp joint row reference bound
  · intro joint row reference dirty bound
    apply Finite.check_clean_return _ _ _ _ _ _ _ hp joint row reference bound
    intro col hc
    have rows := encoded.2.2.1
    exact zeroEncoding_dirty _ _ _ _ _ he row col dirty (by rw [← rows]; exact bound) hc

/-- Actual accepted raw reconstruction preserves joint norms for arbitrary
untouched references. The hypothesis is Lean's executable reconstruct, not a
Rust receipt, a source-check success or a producer-computed matrix. -/
theorem reconstruct_reference_norm {R : Type} (dependencies : List Dependency) (program : Program)
    (actual : Matrix) (work left : Nat)
    (ok : (reconstruct dependencies program).run work = (.ok actual,left))
    (joint : Nat → R → ℂ) (references : List R) :
    (references.map (fun r => ((List.range actual.rows).map
      (fun row => Complex.normSq (action actual joint row r))).sum)).sum =
    (references.map (fun r => ((List.range actual.cols).map
      (fun col => Complex.normSq (joint col r))).sum)).sum := by
  rcases reconstruct_conditions _ _ _ _ _ ok with ⟨_,_,_,_,before,after,_,_,_,iso⟩
  exact Exact.isometry_joint_norm _ _ _ iso joint references

/-- Each actual extracted event composes complete amplitudes on arbitrary
references. The local map is freshly reconstructed from that event's data. -/
theorem evolve_reference {R : Type} (dependencies : List Dependency) (input output : Matrix)
    (event : Event) (work left : Nat)
    (ok : (evolve dependencies input event).run work = (.ok output,left)) :
    ∃ (actual : Matrix) (middle : Nat),
      (eventMatrix dependencies event).run work = (.ok actual,middle) ∧
      ∀ (joint : Nat → R → ℂ) row reference, row < actual.rows →
        action output joint row reference =
          action actual (fun index r => action input joint index r) row reference := by
  rcases evolve_conditions _ _ _ _ _ _ ok with ⟨actual,middle,ha,hc⟩
  exact ⟨actual,middle,ha,fun joint row reference bound => Exact.compose_action _ _ _ _ _ hc joint row reference bound⟩

/-- The actual matrix and reference-system norm law belong to the complete
independent trace of the original raw input, including final output order.
General literal complex interpretation of every event remains a separate gate. -/
theorem original_trace_reference_norm {R : Type} (dependencies : List Dependency) (program : Program)
    (actual : Matrix) (work left : Nat)
    (ok : (reconstruct dependencies program).run work = (.ok actual,left)) :
    ∃ (trace : QleisliKernel.Semantics.RawTrace.Prepared) (initial : Matrix) (before after : Nat),
      QleisliKernel.Semantics.RawTrace.run program = some trace ∧
      (trace.events.foldlM (evolve dependencies) initial).run before = (.ok actual,after) ∧
      ∀ (joint : Nat → R → ℂ) (references : List R),
        (references.map (fun r => ((List.range actual.rows).map
          (fun row => Complex.normSq (action actual joint row r))).sum)).sum =
        (references.map (fun r => ((List.range actual.cols).map
          (fun col => Complex.normSq (joint col r))).sum)).sum := by
  rcases reconstruct_original _ _ _ _ _ ok with ⟨trace,initial,w₁,w₂,w₃,w₄,hr,_,he,hs⟩
  exact ⟨trace,initial,w₁,w₂,hr,he,fun joint references => Exact.isometry_joint_norm _ _ _ hs joint references⟩

/-- The separately supplied requirement includes the complete scalar phase. -/
theorem inspect_reference {R : Type} (evidence : List QleisliKernel.Semantics.Raw.Evidence)
    (program : Program) (required actual : Matrix) (work left : Nat)
    (ok : (inspect evidence program required).run work = (.ok actual,left))
    (joint : Nat → R → ℂ) (row : Nat) (reference : R) :
    action actual joint row reference = action required joint row reference := by
  rw [(inspect_conditions _ _ _ _ _ _ ok).1]

end Qleisli.Raw
