import Qleisli.RuntimeFiniteTargetFibre

/-! The actual finite target slice of a complete original caller encoding.
Arbitrary ordered Raw axes use the same retained owner map; all other owners,
including zero-width owners and nominal padding, keep their own coefficients.
The resulting rectangular-code action is a total-complex equation, without a
bounded availability claim or an assumed local intertwiner.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeFiniteTargetScatter
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open RuntimeOwnerMap (Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.RuntimeForestRegroup Qleisli.RuntimeFiniteTargetFibre

private theorem bit_zero (label bits axis : Nat) (bound : label < 2^bits)
    (outside : bits ≤ axis) : bit label axis = 0 := by
  have power : 2^bits ≤ 2^axis := by gcongr; norm_num
  simp [bit,Nat.div_eq_of_lt (Nat.lt_of_lt_of_le bound power)]

/-- Gather the same exact ordered axes after their literal overwrite. This
includes the empty list, whose sole supported coordinate is zero. -/
theorem gather_scatter (physical value : Nat) (axes : List Nat)
    (unique : axes.Nodup) (bound : value < 2^axes.length) :
    gather (scatter physical axes value) axes = value := by
  apply Nat.eq_of_testBit_eq
  intro axis
  have same : bit (gather (scatter physical axes value) axes) axis = bit value axis := by
    by_cases before : axis < axes.length
    · rw [RuntimeScatterTransport.gather_at _ axes axis before,
        RuntimeScatterTransport.scatter_at _ _ axes unique axis before]
    · rw [bit_zero _ axes.length axis (gather_bound _ axes) (by omega),
        bit_zero value axes.length axis bound (by omega)]
  simp only [bit] at same
  rw [← Nat.toNat_testBit _ axis,← Nat.toNat_testBit value axis] at same
  cases leftBit : (gather (scatter physical axes value) axes).testBit axis <;>
    cases rightBit : value.testBit axis <;> simp_all

/-- Replacing this target's physical coordinate leaves every other original
owner factor unchanged. Disjointness follows from the same actual Raw frame. -/
theorem spectator_scatter
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (output : Frame source.transport.after)
    (target : Binding) (member : target ∈ source.transport.after.bindings)
    (physical replacement logical : Nat) :
    spectatorCoefficient output target
        (scatter physical (target.port.wires.map frame.interval.after.quantum.frame.idxOf) replacement) logical =
      spectatorCoefficient output target physical logical := by
  have unique : source.transport.after.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      source.transport.after.tokensDistinct
  unfold spectatorCoefficient
  apply congrArg List.prod
  apply List.map_congr_left
  intro binding present
  have retained := unique.mem_erase_iff.mp present
  obtain ⟨actual,_read⟩ := lookup_exists output.owners binding retained.2
  have disjoint := Qleisli.RuntimeTargetScatter.output_owner_axes_disjoint frame source
    binding target retained.2 member retained.1
  rw [factorAt_eq _ _ _ _ retained.2 actual,factorAt_eq _ _ _ _ retained.2 actual,
    Qleisli.RuntimeTargetScatter.gather_disjoint physical replacement _ _ disjoint]

/-- The logical fibre contains arbitrary correlations with all other owners
and references. Its coefficients do not depend on the overwritten target row. -/
theorem fibre_scatter {Reference : Type}
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (output : Frame source.transport.after)
    (target : Binding) (member : target ∈ source.transport.after.bindings)
    (joint : Nat → Reference → ℂ) (physical replacement digit : Nat) (reference : Reference) :
    targetFibre output target
        (scatter physical (target.port.wires.map frame.interval.after.quantum.frame.idxOf) replacement)
        joint digit reference =
      targetFibre output target physical joint digit reference := by
  unfold targetFibre
  apply Qleisli.Exact.sum_map_congr
  intro logical _present
  rw [spectator_scatter frame source output target member physical replacement logical]

/-- Every physical target row, including padding, is the action of the actual
rectangular target code on the same complete original logical fibre. This is
the finite-target replacement for the Bit-only set-digit identity. -/
theorem target_slice_code_action {Reference : Type}
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (output : Frame source.transport.after)
    (target : Binding) (member : target ∈ source.transport.after.bindings) (actual : OwnerCode target)
    (joint : Nat → Reference → ℂ) (physical row : Nat) (reference : Reference)
    (bound : row < 2^actual.layout.bits) :
    referenceAction output joint
        (scatter physical (target.port.wires.map frame.interval.after.quantum.frame.idxOf) row) reference =
      action (Semantics.FiniteCarrier.encoding actual.layout) (targetFibre output target physical joint)
        row reference := by
  let axes := target.port.wires.map frame.interval.after.quantum.frame.idxOf
  have allUnique : (source.transport.after.bindings.flatMap fun binding =>
      binding.port.wires.map frame.interval.after.quantum.frame.idxOf).Nodup := by
    simpa only [forestAxes,List.map_flatMap] using
      Qleisli.RuntimeTargetScatter.output_axes_unique frame source
  have unique : axes.Nodup := (List.nodup_flatMap.mp allUnique).1 target member
  have small : row < 2^axes.length := by
    simpa only [axes,List.length_map,actual.reference.2.2] using bound
  have same : targetFibre output target (scatter physical axes row) joint =
      targetFibre output target physical joint := by
    funext digit ref
    exact fibre_scatter frame source output target member joint physical row digit ref
  rw [fibre_code_action output target member actual joint _ reference,same,
    gather_scatter physical row axes unique small]

#print axioms spectator_scatter
#print axioms target_slice_code_action

end Qleisli.RuntimeFiniteTargetScatter
