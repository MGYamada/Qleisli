import Qleisli.RuntimeForestRegroup

/-! Support of actual finite owner codes in a complete original runtime forest.
Logical digits use retained cardinalities; physical labels use the independent
carrier's label table and the owner's real ordered Raw axes. Nominal padding,
records, nested products and distinct empty owners are not identified by width.
These are total-complex coefficient implications, not bounded availability,
Gram, source-lowering, capability or acceptance theorems.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNominalSupport
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.MixedRadix Qleisli.RuntimeForestRegroup Qleisli.RuntimeForestOrderedProduct

/-- A nonzero complete forest coefficient fixes this exact original owner's
physical code label. The dense logical digit need not equal that label. Both
come from the same full Basis and retained code read, not a matching width. -/
theorem owner_code_support {roles state checked} (output : @Frame roles state checked)
    (binding : Binding) (member : binding ∈ checked.bindings) (actual : OwnerCode binding)
    (physical logical : Nat) (bound : logical < output.code.dimension)
    (nonzero : scalar (output.embedding physical logical) ≠ 0) :
    let digit := decode checked.bindings (dimensionAt output.owners) logical binding
    digit < actual.layout.labels.length ∧
      actual.layout.labels[digit]? = some (gather physical (binding.port.wires.map state.quantum.frame.idxOf)) := by
  let order := checked.bindings
  let cards := dimensionAt output.owners
  let digit := decode order cards logical binding
  let coordinate := gather physical (binding.port.wires.map state.quantum.frame.idxOf)
  have unique : order.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      checked.tokensDistinct
  have logicalBound : logical < volume order cards := by rw [frame_volume output]; exact bound
  have digitBound : digit < actual.layout.labels.length := by
    rw [← dimensionAt_eq output.owners binding member actual]
    exact decode_bound order cards logical (cards_positive output.owners) logicalBound binding member
  have coordinateBound : coordinate < 2^actual.layout.bits := by
    simpa only [List.length_map,actual.reference.2.2] using
      gather_bound physical (binding.port.wires.map state.quantum.frame.idxOf)
  have factorNonzero : factorAt state.quantum.frame output.owners physical binding digit ≠ 0 := by
    intro zero
    apply nonzero
    rw [ordered_product_entry output physical logical bound,
      coefficients_factors output.owners state.quantum.frame output.owners physical logical
        (fun {_} present => present) unique logicalBound]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨binding,member,zero⟩)
  change digit < actual.layout.labels.length ∧ actual.layout.labels[digit]? = some coordinate
  refine ⟨digitBound,?_⟩
  by_contra missing
  apply factorNonzero
  rw [factorAt_eq state.quantum.frame output.owners physical binding member actual digit]
  change entry (Semantics.FiniteCarrier.encoding actual.layout) coordinate digit = 0
  rw [← encoding_coefficient actual.layout coordinate digit coordinateBound digitBound]
  have different : ¬ (actual.layout.labels[digit]? == some coordinate) = true :=
    fun equal => missing (beq_iff_eq.mp equal)
  change scalar (if actual.layout.labels[digit]? == some coordinate then Scalar.one else Scalar.zero) = 0
  rw [if_neg different]
  exact Qleisli.Exact.scalar_zero_meaning

/-- Physical padding for any one actual owner has zero support in the full
caller forest, for every original logical input and arbitrary spectators. -/
theorem owner_padding_zero {roles state checked} (output : @Frame roles state checked)
    (binding : Binding) (member : binding ∈ checked.bindings) (actual : OwnerCode binding)
    (physical logical : Nat) (bound : logical < output.code.dimension)
    (padding : gather physical (binding.port.wires.map state.quantum.frame.idxOf) ∉ actual.layout.labels) :
    scalar (output.embedding physical logical) = 0 := by
  by_contra nonzero
  have support := owner_code_support output binding member actual physical logical bound nonzero
  exact padding (List.mem_of_getElem? support.2)

/-- Instantiate the support law at the actual original returned selector.
The enclosing source lookup, complete owner map and literal interval are the
same ones used by the sector action; no selector ordinal is a physical label. -/
theorem returned_selector_support
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after)
    (actual : OwnerCode source.returned.first) (physical logical : Nat)
    (bound : logical < literal.outputCode.code.dimension)
    (nonzero : scalar (literal.outputCode.embedding physical logical) ≠ 0) :
    let digit := decode source.transport.after.bindings (dimensionAt literal.outputCode.owners) logical source.returned.first
    digit < actual.layout.labels.length ∧
      actual.layout.labels[digit]? = some
        (gather physical (source.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf)) := by
  have selected := RuntimeSelectionPartition.order_values _ _ _ source.returned.ordered
  have member : source.returned.first ∈ source.transport.after.bindings := selected.1 (by simp)
  exact owner_code_support literal.outputCode source.returned.first member actual physical logical bound nonzero

#print axioms owner_code_support
#print axioms owner_padding_zero
#print axioms returned_selector_support

end Qleisli.RuntimeNominalSupport
