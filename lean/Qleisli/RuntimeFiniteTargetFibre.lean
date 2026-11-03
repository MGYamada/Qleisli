import Qleisli.RuntimeFiniteTargetCode

/-! Fibres of an actual finite target inside the complete original owner code.
The target encoding remains rectangular. Its logical digits are independent of
physical code labels, so padded rows and zero-width owners are retained. The
other owners contribute encoding coefficients, not a separability assumption
on the arbitrary joint logical/reference amplitudes. No joined matrix or
bounded arithmetic equivalence is constructed here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeFiniteTargetFibre
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open RuntimeOwnerMap (Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.MixedRadix Qleisli.RuntimeForestRegroup Qleisli.RuntimeForestOrderedProduct

/-- Delete exactly this original target binding. All remaining owners keep
their original order, including distinct Unit and nominal singleton owners. -/
noncomputable def spectatorCoefficient {roles state checked} (output : @Frame roles state checked)
    (target : Binding) (physical logical : Nat) : ℂ :=
  ((checked.bindings.erase target).map fun binding =>
    factorAt state.quantum.frame output.owners physical binding
      (decode checked.bindings (dimensionAt output.owners) logical binding)).prod

/-- The target's ordinary logical digit indexes this fibre. Physical padding
is handled by the actual target encoding, never by a fabricated logical arm. -/
noncomputable def targetFibre {Reference : Type} {roles state checked}
    (output : @Frame roles state checked) (target : Binding) (physical : Nat)
    (joint : Nat → Reference → ℂ) (digit : Nat) (reference : Reference) : ℂ :=
  ((List.range output.code.dimension).map fun logical =>
    if decode checked.bindings (dimensionAt output.owners) logical target = digit then
      spectatorCoefficient output target physical logical * joint logical reference
    else 0).sum

/-- Factor the actual complete sparse encoding at this exact original owner.
The factor is the independent encoding of its retained carrier read. -/
theorem owner_factor {roles state checked} (output : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (actual : OwnerCode target)
    (physical logical : Nat) (bound : logical < output.code.dimension) :
    scalar (output.embedding physical logical) =
      entry (Semantics.FiniteCarrier.encoding actual.layout)
        (gather physical (target.port.wires.map state.quantum.frame.idxOf))
        (decode checked.bindings (dimensionAt output.owners) logical target) *
      spectatorCoefficient output target physical logical := by
  have unique : checked.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      checked.tokensDistinct
  have logicalBound : logical < volume checked.bindings (dimensionAt output.owners) := by
    rw [frame_volume output]
    exact bound
  let factor := fun binding => factorAt state.quantum.frame output.owners physical binding
    (decode checked.bindings (dimensionAt output.owners) logical binding)
  calc
    _ = coefficients state.quantum.frame output.owners physical logical :=
      ordered_product_entry output physical logical bound
    _ = (checked.bindings.map factor).prod :=
      coefficients_factors output.owners state.quantum.frame output.owners physical logical
        (fun {_} present => present) unique logicalBound
    _ = factor target * ((checked.bindings.erase target).map factor).prod :=
      (List.prod_map_erase factor member).symm
    _ = _ := by
      dsimp only [factor]
      rw [factorAt_eq state.quantum.frame output.owners physical target member actual]
      rfl

/-- A finite target fibre reconstructs the actual complete caller encoding
at every physical coordinate. The joint/reference family remains arbitrary;
this is a total-complex identity and promises no bounded evaluation. -/
theorem fibre_code_action {Reference : Type} {roles state checked}
    (output : @Frame roles state checked) (target : Binding) (member : target ∈ checked.bindings)
    (actual : OwnerCode target) (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction output joint physical reference =
      action (Semantics.FiniteCarrier.encoding actual.layout)
        (targetFibre output target physical joint)
        (gather physical (target.port.wires.map state.quantum.frame.idxOf)) reference := by
  let digit := fun logical => decode checked.bindings (dimensionAt output.owners) logical target
  let coordinate := gather physical (target.port.wires.map state.quantum.frame.idxOf)
  let encoding := Semantics.FiniteCarrier.encoding actual.layout
  let term := fun logical => spectatorCoefficient output target physical logical * joint logical reference
  have small (logical : Nat) (bound : logical < output.code.dimension) : digit logical < encoding.cols := by
    change digit logical < actual.layout.labels.length
    rw [← dimensionAt_eq output.owners target member actual]
    have fullBound : logical < volume checked.bindings (dimensionAt output.owners) := by
      rw [frame_volume output]
      exact bound
    exact decode_bound checked.bindings (dimensionAt output.owners) logical (cards_positive output.owners)
      fullBound target member
  have one (logical : Nat) (bound : logical < output.code.dimension) :
      ((List.range encoding.cols).map fun value =>
        entry encoding coordinate value * (if digit logical = value then term logical else 0)).sum =
          entry encoding coordinate (digit logical) * term logical := by
    have terms (value : Nat) :
        entry encoding coordinate value * (if digit logical = value then term logical else 0) =
          if digit logical = value then entry encoding coordinate value * term logical else 0 := by
      by_cases same : digit logical = value
      · rw [if_pos same,if_pos same]
      · rw [if_neg same,if_neg same,mul_zero]
    simp only [terms]
    exact Qleisli.Exact.range_delta_sum encoding.cols (digit logical)
      (fun value => entry encoding coordinate value * term logical) (small logical bound)
  calc
    referenceAction output joint physical reference =
        ((List.range output.code.dimension).map fun logical =>
          entry encoding coordinate (digit logical) * term logical).sum := by
      unfold referenceAction
      apply Qleisli.Exact.sum_map_congr
      intro logical present
      rw [owner_factor output target member actual physical logical (List.mem_range.mp present)]
      exact mul_assoc _ _ _
    _ = ((List.range output.code.dimension).map fun logical =>
        ((List.range encoding.cols).map fun value =>
          entry encoding coordinate value * (if digit logical = value then term logical else 0)).sum).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro logical present
      exact (one logical (List.mem_range.mp present)).symm
    _ = ((List.range encoding.cols).map fun value =>
        ((List.range output.code.dimension).map fun logical =>
          entry encoding coordinate value * (if digit logical = value then term logical else 0)).sum).sum :=
      Qleisli.Exact.sum_swap _ _ _
    _ = _ := by
      simp only [List.sum_map_mul_left]
      rfl

#print axioms owner_factor
#print axioms fibre_code_action

end Qleisli.RuntimeFiniteTargetFibre
