import QleisliKernel.Qirf.RuntimeForestCode

/-! Actual lazy coefficient transport for a contiguous placement of local
axes in an authentic caller frame. Both lower and upper spectators and an
arbitrary reference-indexed joint amplitude remain unrestricted. Local sums,
dependency reads, exact arithmetic, first errors and work are unchanged.
This is not arbitrary-axis permutation covariance, a matrix/circuit linearity
theorem, code/action reassociation or a new accepted-handle path.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeCoefficientTransport
open QleisliKernel Finite Semantics.Finite Semantics.Exact
open FiniteRestriction (pack)

def shiftAxes (offset : Nat) (axes : List Nat) : List Nat := axes.map (offset+·)

def shiftControls (offset : Nat) (controls : List Control) : List Control :=
  controls.map fun control => ⟨offset+control.index,control.whenOne⟩

def shiftStep (offset : Nat) (step : Step) : Step :=
  ⟨shiftControls offset step.controls,match step.action with
    | .hadamard axis => .hadamard (offset+axis)
    | .monomial axes permutation phases => .monomial (shiftAxes offset axes) permutation phases
    | .contract axes dependency adjoint => .contract (shiftAxes offset axes) dependency adjoint⟩

/-- Restrict only the low spectator label; all remaining coordinates, including
upper spectators, remain arguments of the same original lazy state. -/
def slice (offset low : Nat) (values : Raw.Coefficient.State) : Raw.Coefficient.State :=
  fun high => values (pack offset low high)

theorem enabled_shift (offset low high : Nat) (bound : low < 2^offset) (controls : List Control) :
    enabled (shiftControls offset controls) (pack offset low high) = enabled controls high := by
  induction controls with
  | nil => rfl
  | cons control rest ih =>
    change (((bit (pack offset low high) (offset+control.index) == 1) == control.whenOne) &&
      enabled (shiftControls offset rest) (pack offset low high)) =
      (((bit high control.index == 1) == control.whenOne) && enabled rest high)
    rw [FiniteRestriction.bit_target offset low high control.index bound,ih]

theorem gather_shift (offset low high : Nat) (bound : low < 2^offset) (axes : List Nat) :
    gather (pack offset low high) (shiftAxes offset axes) = gather high axes := by
  have after : ∀ axis ∈ shiftAxes offset axes,offset ≤ axis := by
    intro axis member
    obtain ⟨original,_present,rfl⟩ := List.mem_map.mp member
    omega
  simpa [shiftAxes,List.map_map] using
    FiniteRestriction.gather_pack offset low high bound (shiftAxes offset axes) after

theorem scatter_shift (offset low high value : Nat) (bound : low < 2^offset) (axes : List Nat) :
    scatter (pack offset low high) (shiftAxes offset axes) value =
      pack offset low (scatter high axes value) := by
  have after : ∀ axis ∈ shiftAxes offset axes,offset ≤ axis := by
    intro axis member
    obtain ⟨original,_present,rfl⟩ := List.mem_map.mp member
    omega
  simpa [shiftAxes,List.map_map] using
    FiniteRestriction.scatter_pack offset low high value bound (shiftAxes offset axes) after

private theorem clear_pack (offset low high axis : Nat) (bound : low < 2^offset) :
    pack offset low high - bit high axis * 2^(offset+axis) =
      pack offset low (high-bit high axis*2^axis) := by
  have changed := FiniteRestriction.update_pack offset low high axis 0 0 bound
  simpa only [FiniteRestriction.bit_target offset low high axis bound,bit,Nat.zero_div,Nat.zero_mod,
    Nat.zero_mul,Nat.add_zero] using changed

private theorem high_pack (offset low high : Nat) (axis : Nat) :
    pack offset low high + 2^(offset+axis) = pack offset low (high+2^axis) := by
  simp only [pack,Nat.pow_add,Nat.mul_add]
  ac_rfl

/-- The two H input queries retain their low/high order and exact original
coefficient computations. No arithmetic associativity or phase quotient is used. -/
theorem hadamard_shift (offset low high axis : Nat) (bound : low < 2^offset)
    (values : Raw.Coefficient.State) :
    Raw.ProtectedEvaluation.gate .h (offset+axis) values (pack offset low high) =
      Raw.ProtectedEvaluation.gate .h axis (slice offset low values) high := by
  simp only [Raw.ProtectedEvaluation.gate,FiniteRestriction.bit_target offset low high axis bound]
  rw [clear_pack offset low high axis bound,high_pack]
  rfl

/-- The actual lazy dispatch commutes with shifted coordinates, including the
complete WorkM result and remaining work. Every local summation index is kept
in the same order; even unrelated reference amplitudes need no factorization. -/
theorem step_shift (dependencies : List Dependency) (offset low high : Nat)
    (bound : low < 2^offset) (step : Step) (values : Raw.Coefficient.State) :
    Raw.Coefficient.step dependencies (shiftStep offset step) values (pack offset low high) =
      Raw.Coefficient.step dependencies step (slice offset low values) high := by
  rcases step with ⟨controls,action⟩
  cases action with
  | hadamard axis =>
    simp only [Raw.Coefficient.step,shiftStep,enabled_shift offset low high bound controls,
      hadamard_shift offset low high axis bound values,slice]
  | monomial axes permutation phases =>
    simp only [Raw.Coefficient.step,shiftStep,enabled_shift offset low high bound controls,
      gather_shift offset low high bound axes,scatter_shift offset low high _ bound axes,slice]
  | contract axes dependency adjoint =>
    simp only [Raw.Coefficient.step,shiftStep,enabled_shift offset low high bound controls,
      gather_shift offset low high bound axes,scatter_shift offset low high _ bound axes,slice]

theorem circuit_shift (dependencies : List Dependency) (offset low : Nat) (bound : low < 2^offset)
    (steps : List Step) (values : Raw.Coefficient.State) :
    slice offset low (Raw.Coefficient.circuit dependencies (steps.map (shiftStep offset)) values) =
      Raw.Coefficient.circuit dependencies steps (slice offset low values) := by
  induction steps generalizing values with
  | nil => rfl
  | cons first rest ih =>
    change slice offset low (Raw.Coefficient.circuit dependencies (rest.map (shiftStep offset))
      (Raw.Coefficient.step dependencies (shiftStep offset first) values)) =
      Raw.Coefficient.circuit dependencies rest (Raw.Coefficient.step dependencies first (slice offset low values))
    rw [ih]
    have head : slice offset low (Raw.Coefficient.step dependencies (shiftStep offset first) values) =
        Raw.Coefficient.step dependencies first (slice offset low values) := by
      funext high
      exact step_shift dependencies offset low high bound first values
    rw [head]

private theorem shifted_index (offset width index : Nat) (bound : index < width) :
    (((List.range width).map (offset+·))[index]?).getD 0 = offset+index := by
  simp only [List.getElem?_map,List.getElem?_range bound,Option.map_some,Option.getD_some]

/-- Actual Raw localize, with every referenced local axis in the retained
selected wire list. No default/out-of-range axis can satisfy this theorem. -/
theorem localize_shift (offset width : Nat) (step : Step)
    (controls : ∀ control ∈ step.controls,control.index < width)
    (targets : ∀ axis ∈ Finite.targets step.action,axis < width) :
    Semantics.RawTrace.localize ((List.range width).map (offset+·)) step = shiftStep offset step := by
  rcases step with ⟨controlList,action⟩
  have sameControls : controlList.map (fun control =>
      (⟨((((List.range width).map (offset+·))[control.index]?).getD 0),control.whenOne⟩ : Control)) =
      shiftControls offset controlList := by
    apply List.map_congr_left
    intro control member
    rw [shifted_index offset width control.index (controls control member)]
  cases action with
  | hadamard axis =>
    have bound := targets axis (List.mem_singleton_self axis)
    simp only [Semantics.RawTrace.localize,shiftStep,sameControls,shifted_index offset width axis bound]
  | monomial axes permutation phases =>
    have sameAxes : axes.map (fun axis => (((List.range width).map (offset+·))[axis]?).getD 0) =
        shiftAxes offset axes := by
      apply List.map_congr_left
      intro axis member
      exact shifted_index offset width axis (targets axis member)
    simp only [Semantics.RawTrace.localize,shiftStep,sameControls,sameAxes]
  | contract axes dependency adjoint =>
    have sameAxes : axes.map (fun axis => (((List.range width).map (offset+·))[axis]?).getD 0) =
        shiftAxes offset axes := by
      apply List.map_congr_left
      intro axis member
      exact shifted_index offset width axis (targets axis member)
    simp only [Semantics.RawTrace.localize,shiftStep,sameControls,sameAxes]

/-- A selected forest obtained from the same complete source-owner map.
Placement is an exact equality of actual port-wire/caller-frame coordinates,
not an equality of widths or an assumed semantic commutation property. -/
structure Placement {roles state} (complete : RuntimeOwnerMap.Checked roles state) where
  selectedRoles : List Semantics.SourceOwners.Owner
  selected : RuntimeOwnerMap.Map
  selectedRead : RuntimeInterval.Computed (RuntimeOwnerMap.order selectedRoles complete.bindings) selected
  offset : Nat
  width : Nat
  coordinates : RuntimeForestCode.forestAxes state.quantum.frame selected =
    (List.range width).map (offset+·)

/-- This consumes the selected bindings' authentic wire order and the complete
caller frame. All spectators and reference coordinates remain in `values`. -/
theorem Placement.stepReferences {Reference : Type} {roles state complete}
    (placement : @Placement roles state complete) (dependencies : List Dependency) (step : Step)
    (controls : ∀ control ∈ step.controls,control.index < placement.width)
    (targets : ∀ axis ∈ Finite.targets step.action,axis < placement.width)
    (low : Nat) (bound : low < 2^placement.offset) (values : Reference → Raw.Coefficient.State) :
    (fun reference high => Raw.Coefficient.step dependencies
      (Semantics.RawTrace.localize (RuntimeForestCode.forestAxes state.quantum.frame placement.selected) step)
      (values reference) (pack placement.offset low high)) =
    (fun reference high => Raw.Coefficient.step dependencies step
      (slice placement.offset low (values reference)) high) := by
  rw [placement.coordinates,localize_shift placement.offset placement.width step controls targets]
  funext reference high
  exact step_shift dependencies placement.offset low high bound step (values reference)

theorem Placement.circuitReferences {Reference : Type} {roles state complete}
    (placement : @Placement roles state complete) (dependencies : List Dependency) (steps : List Step)
    (controls : ∀ step ∈ steps,∀ control ∈ step.controls,control.index < placement.width)
    (targets : ∀ step ∈ steps,∀ axis ∈ Finite.targets step.action,axis < placement.width)
    (low : Nat) (bound : low < 2^placement.offset) (values : Reference → Raw.Coefficient.State) :
    (fun reference => slice placement.offset low (Raw.Coefficient.circuit dependencies
      (steps.map (Semantics.RawTrace.localize (RuntimeForestCode.forestAxes state.quantum.frame placement.selected)))
      (values reference))) =
    (fun reference => Raw.Coefficient.circuit dependencies steps (slice placement.offset low (values reference))) := by
  have localized : steps.map (Semantics.RawTrace.localize
      (RuntimeForestCode.forestAxes state.quantum.frame placement.selected)) = steps.map (shiftStep placement.offset) := by
    apply List.map_congr_left
    intro step present
    rw [placement.coordinates]
    exact localize_shift placement.offset placement.width step (controls step present) (targets step present)
  rw [localized]
  funext reference
  exact circuit_shift dependencies placement.offset low bound steps (values reference)

/-- The source of the localized circuit is the actual original Raw operation
and actual selected port, not a detached producer circuit or a width guess. -/
theorem applyUnitary_event (state next : Semantics.RawTrace.Interface) (input output : Nat)
    (port : Semantics.Raw.Port) (steps : List Step)
    (taken : Semantics.RawTrace.take state input = some (port,next)) :
    Semantics.RawTrace.step state (.applyUnitary input output steps) =
      some (Semantics.RawTrace.insert next output port.wires,
        [.circuit state.frame.length (steps.map (Semantics.RawTrace.localize
          (Semantics.RawTrace.axes state port.wires)))]) := by
  simp only [Semantics.RawTrace.step,taken,bind,Option.bind]
  rfl

end QleisliKernel.Qirf.RuntimeCoefficientTransport
