import Qleisli.RuntimeTargetScatter
import Qleisli.RuntimeNamedHeadCoefficients
import Qleisli.RuntimeNamedSelectionFrames
import Qleisli.RuntimeNamedCallerAction

/-! Exact sparse input encoding under original source carrier aliases.
Full ordered port/basis correspondence and actual Raw frame geometry remain
separate premises. No width inference, joined matrix or acceptance is introduced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedCarrierEncoding
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Finite (gather)
open RuntimeOwnerMap (Map Binding)
open RuntimeForestCode
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.RuntimeForestOrderedProduct

theorem carrier_layouts {left right : Map} (first : OwnerCodes left) (second : OwnerCodes right)
    (same : carrierOwners right = carrierOwners left) : layouts second = layouts first := by
  induction first generalizing right with
  | nil =>
    cases second with
    | nil => rfl
    | cons _ _ => simp [carrierOwners] at same
  | @cons original rest first remaining ih =>
    cases second with
    | nil => simp [carrierOwners] at same
    | @cons current tail second tailCodes =>
      have parts := List.cons.inj same
      have basis : current.owner.basis = original.owner.basis :=
        congrArg Semantics.CarrierInterface.Owner.basis parts.1
      have actual := second.reference.1
      rw [basis] at actual
      have equal : second.layout = first.layout := Option.some.inj (actual.symm.trans first.reference.1)
      simp only [layouts,equal,ih tailCodes parts.2]

theorem carrier_wires {left right : Map} (same : carrierOwners right = carrierOwners left) :
    right.flatMap (fun binding => binding.port.wires) = left.flatMap (fun binding => binding.port.wires) := by
  have actual := congrArg (List.flatMap fun owner : Semantics.CarrierInterface.Owner => owner.port.wires) same
  simpa only [carrierOwners,List.flatMap_map,Function.comp_def] using actual

/-- Independent full forest codes agree because their complete original
carrier lists agree in order. Matching physical widths is not sufficient. -/
theorem frame_entries {roles state checked selected}
    (child : @Frame roles state checked) (codes : OwnerCodes selected)
    (same : carrierOwners checked.bindings = carrierOwners selected) :
    child.code.dimension = (sparseProduct codes).dimension ∧
      ∀ physical logical,sparseEntry child.code physical logical =
        sparseEntry (.ofLayout (layoutProduct codes)) physical logical := by
  have actual := frame_product_agrees child
  have equal : layoutProduct child.owners = layoutProduct codes := by
    unfold layoutProduct
    rw [carrier_layouts codes child.owners same]
  rw [equal] at actual
  refine ⟨actual.dimension.trans (product_agrees codes).dimension.symm,?_⟩
  intro physical logical
  unfold sparseEntry
  rw [actual.labels logical]
  rfl

/-- Convert this exact child sparse coefficient to the original caller's
selected-owner product. The Raw frame is its real ordered input wire list. -/
theorem input_coefficient {roles state checked selected}
    (child : @Frame roles state checked) (codes : OwnerCodes selected)
    (same : carrierOwners checked.bindings = carrierOwners selected)
    (localFrame : state.quantum.frame = selected.flatMap (fun binding => binding.port.wires))
    (unique : state.quantum.frame.Nodup) (parentFrame : List Nat) (physical logical : Nat)
    (bound : logical < child.code.dimension) :
    scalar (child.embedding (gather physical (forestAxes parentFrame selected)) logical) =
      coefficients parentFrame codes physical logical := by
  have wires := carrier_wires same
  have axes : forestAxes state.quantum.frame checked.bindings = List.range state.quantum.frame.length := by
    unfold forestAxes
    rw [wires,← localFrame]
    exact RuntimeNamedCallerAction.self_indices _ unique
  have small : gather physical (forestAxes parentFrame selected) < 2^state.quantum.frame.length := by
    have actual := gather_bound physical (forestAxes parentFrame selected)
    simpa only [forestAxes,List.length_map,localFrame] using actual
  obtain ⟨dimension,entries⟩ := frame_entries child codes same
  change scalar (sparseEntry child.code
    (gather (gather physical (forestAxes parentFrame selected))
      (forestAxes state.quantum.frame checked.bindings)) logical) = _
  rw [axes,RuntimeNamedCallerAction.gather_range,Nat.mod_eq_of_lt small,entries]
  exact product_coefficient parentFrame codes physical logical (by rwa [← dimension])

#print axioms carrier_layouts
#print axioms frame_entries
#print axioms input_coefficient
/-- The original child starts with the exact selected physical frame, in
the caller's ordered input wires. -/
theorem original_selection_input_geometry
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {first size localInputs outputs selector target}
    (selected : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    (starts : first = 0) :
    forestAxes scope.interval.before.quantum.frame boundary.input.ordered = RuntimeNamedFrameAxes.mixedAxes scope ∧
    selected.interval.before.quantum.frame = boundary.input.ordered.flatMap (·.port.wires) ∧
    selected.interval.before.quantum.frame.Nodup := by
  have axes : forestAxes scope.interval.before.quantum.frame boundary.input.ordered =
      RuntimeNamedFrameAxes.mixedAxes scope := by
    unfold RuntimeNamedFrameAxes.mixedAxes RuntimeForestCode.portAxes
    rw [RuntimeNamedFrameAxes.mixed_bound_ports scope boundary]
    simp only [forestAxes,List.flatMap_map]
  have native := RuntimeNamedFrameAxes.mixedAxes_input scope
  have entry : selected.interval.before.quantum.reference = scope.localEntry.quantum.reference :=
    (RuntimeNamedSelectionParent.at_zero selected.interval starts).trans
      (native.2.2.1.trans native.2.1.symm)
  have localState := congrArg Semantics.RawTrace.Interface.frame native.2.1
  change scope.localEntry.quantum.frame = scope.selected.flatMap (·.wires) at localState
  rw [RuntimeNamedFrameAxes.mixed_bound_ports scope boundary,List.flatMap_map] at localState
  have localFrame : selected.interval.before.quantum.frame =
      boundary.input.ordered.flatMap (fun binding => binding.port.wires) :=
    (congrArg Semantics.RawTrace.Interface.frame entry).trans localState
  have mappedUnique : (forestAxes scope.interval.before.quantum.frame boundary.input.ordered).Nodup := by
    rw [axes]
    exact (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1
  have wiresUnique : (boundary.input.ordered.flatMap (fun binding => binding.port.wires)).Nodup :=
    List.Pairwise.of_map scope.interval.before.quantum.frame.idxOf
      (fun _ _ different equal => different (congrArg scope.interval.before.quantum.frame.idxOf equal)) mappedUnique
  have unique : selected.interval.before.quantum.frame.Nodup := by
    rw [localFrame]
    exact wiresUnique
  exact ⟨axes,localFrame,unique⟩

/-- Derive the local Raw frame and selected parent axes from the actual
named scope. Only the original full-carrier source fact and start-at-zero
coverage are consumed; frame geometry is not supplied by the caller. -/
theorem original_selection_input_coefficient
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {first size localInputs outputs selector target}
    (selected : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    (source : RuntimeOwnerTransition.Selection selected.interval localInputs outputs [selector,target])
    (starts : first = 0)
    (same : carrierOwners source.before.bindings = carrierOwners boundary.input.ordered)
    (child : Frame source.before) (codes : OwnerCodes boundary.input.ordered)
    (physical logical : Nat) (bound : logical < child.code.dimension) :
    scalar (child.embedding (gather physical (RuntimeNamedFrameAxes.mixedAxes scope)) logical) =
      coefficients scope.interval.before.quantum.frame codes physical logical := by
  obtain ⟨axes,localFrame,unique⟩ := original_selection_input_geometry scope boundary selected starts
  have actual := input_coefficient child codes same localFrame unique
    scope.interval.before.quantum.frame physical logical bound
  rw [axes] at actual
  exact actual

#print axioms original_selection_input_coefficient

theorem original_selection_input_action {Reference : Type}
    {dependencies program block callStart callCount inputs ordinary effect sources caller before returned retired value}
    {event : SourceTypes.SourceRuntimeContext.NamedEvent sources caller}
    (scope : @RuntimeCallScope.Checked dependencies program block callStart callCount inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before returned retired value)
    {first size localInputs outputs selector target}
    (selected : RuntimePureInterval.Checked scope.prepared.block 2 first size localInputs outputs [selector,target])
    (source : RuntimeOwnerTransition.Selection selected.interval localInputs outputs [selector,target])
    (starts : first = 0)
    (same : carrierOwners source.before.bindings = carrierOwners boundary.input.ordered)
    (child : Frame source.before) (codes : OwnerCodes boundary.input.ordered)
    (joint : Nat → Reference → Complex) (physical : Nat) (reference : Reference) :
    referenceAction child joint (gather physical (RuntimeNamedFrameAxes.mixedAxes scope)) reference =
      ((List.range (sparseProduct codes).dimension).map fun logical =>
        coefficients scope.interval.before.quantum.frame codes physical logical * joint logical reference).sum := by
  obtain ⟨dimension,_entries⟩ := frame_entries child codes same
  unfold referenceAction
  rw [dimension]
  apply Qleisli.Exact.sum_map_congr
  intro logical member
  rw [original_selection_input_coefficient scope boundary selected source starts same child codes physical logical
    (by rw [dimension]; exact List.mem_range.mp member)]

#print axioms original_selection_input_action

end Qleisli.RuntimeNamedCarrierEncoding
