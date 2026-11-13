import Qleisli.RawBranchFunction
import Qleisli.RawPureInstrumentAction
import Qleisli.RoutedControlCommutation
import Qleisli.RuntimeForestProduct
import QleisliKernel.Qirf.RuntimeAccessCallee

/-! Interpret the actual checked access sectors in the complex semantics.
Both the original Raw program meaning and off-sector zero coefficients come
from the same reconstruction retained by the independent access checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.AccessCommutation
open QleisliKernel Qirf Semantics.ControlAccess

private theorem scalar_zero {value : Semantics.Exact.Scalar} (zero : Zero value) :
    Qleisli.Semantics.Exact.scalar value = 0 := by
  obtain ⟨ha,hb,hc,hd⟩ := zero
  simp [Qleisli.Semantics.Exact.scalar,Qleisli.Semantics.Exact.rational,ha,hb,hc,hd]

theorem checked_sector_meaning {tokens dependencies program callee lookup names calls block start count inputs outputs}
    {call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls block start count inputs outputs}
    (sectors : RuntimeAccessInterval.Sectors call) :
    Qleisli.Semantics.ObservingFunction.BodyMeaning dependencies call.fragment sectors.actual ∧
      ∀ row : Fin sectors.actual.rows, ∀ col : Fin sectors.actual.cols,
        Semantics.Finite.gather row.val (RuntimeAccessInterval.controlAxes call.places) ≠
          Semantics.Finite.gather col.val (RuntimeAccessInterval.controlAxes call.places) →
        Qleisli.Semantics.Exact.entry sectors.actual row.val col.val = 0 := by
  obtain ⟨work,left,reconstructed⟩ := sectors.reconstructed
  refine ⟨Qleisli.Raw.BranchFunction.reconstruct_denotes _ _ rfl _ work left reconstructed,?_⟩
  intro row col different
  exact scalar_zero (sectors.preserved row.val (List.mem_range.mpr row.isLt)
    col.val (List.mem_range.mpr col.isLt) different)

/-- For the same literal Raw fragment, any pure trace returned by the reference
reader acts as the checked matrix on each arbitrary reference column. -/
theorem checked_sector_action {tokens dependencies program callee lookup names calls block start count inputs outputs}
    {call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls block start count inputs outputs}
    (sectors : RuntimeAccessInterval.Sectors call)
    (prepared : Semantics.Observation.Prepared)
    (reader : Semantics.Observation.read call.fragment = some prepared)
    (events : List Semantics.Raw.Event) (pureEvents : prepared.events = events.map Semantics.Observation.Event.pure)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Fin sectors.actual.rows) (reference : Reference) :
    Qleisli.Semantics.Exact.action sectors.actual joint row.val reference =
      Qleisli.Semantics.RawAction.events dependencies events (fun col => joint col reference) row.val := by
  obtain ⟨work,left,reconstructed⟩ := sectors.reconstructed
  exact Qleisli.Raw.PureInstrumentAction.reconstructed_action _ _ _ work left reconstructed
    prepared reader events pureEvents joint row.val reference row.isLt

/-- Promoting the checked local action to ordered caller axes preserves
every unselected coordinate and every selected coherent control coordinate.
The promotion equation retains the exact phase of the local action. -/
theorem promoted_preserves_coordinates
    {tokens dependencies program callee lookup names calls block start count inputs outputs}
    {call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls block start count inputs outputs}
    (sectors : RuntimeAccessInterval.Sectors call) (bits : Nat) (axes : List Nat)
    (actual : Semantics.Exact.Matrix) (work left : Nat)
    (read : (Raw.promote bits axes sectors.actual).run work = (.ok actual,left))
    (row : Fin actual.rows) (col : Fin actual.cols)
    (nonzero : Qleisli.Semantics.Exact.entry actual row.val col.val ≠ 0) :
    (∀ axis ∉ axes, Semantics.Finite.bit row.val axis = Semantics.Finite.bit col.val axis) ∧
      Semantics.Finite.gather (Semantics.Finite.gather row.val axes)
          (RuntimeAccessInterval.controlAxes call.places) =
        Semantics.Finite.gather (Semantics.Finite.gather col.val axes)
          (RuntimeAccessInterval.controlAxes call.places) := by
  have embedded := Qleisli.Raw.promote_denotes _ _ _ _ work left read
  have entry := embedded.2.2 row.val col.val row.isLt col.isLt
  obtain ⟨_,middle,guarded,_⟩ := Finite.bind_success _ _ _ _ _ read
  have shape := (Finite.guard_success _ _ _ middle guarded).1
  simp only [Bool.and_eq_true,beq_iff_eq] at shape
  have localRow : Semantics.Finite.gather row.val axes < sectors.actual.rows :=
    shape.1.2.symm ▸ Qleisli.RuntimeForestProduct.gather_bound row.val axes
  have localCol : Semantics.Finite.gather col.val axes < sectors.actual.cols :=
    (shape.2.trans shape.1.2).symm ▸ Qleisli.RuntimeForestProduct.gather_bound col.val axes
  have selected : Semantics.Finite.scatter col.val axes (Semantics.Finite.gather row.val axes) = row.val := by
    by_contra different
    have empty : Qleisli.Semantics.Exact.entry actual row.val col.val = 0 := by
      simpa [different] using entry
    exact nonzero empty
  refine ⟨?_,?_⟩
  · intro axis outside
    rw [← selected]
    exact RuntimeScatterTransport.scatter_outside _ _ _ _ outside
  · by_contra different
    have offSector := (checked_sector_meaning sectors).2 ⟨_,localRow⟩ ⟨_,localCol⟩ different
    apply nonzero
    simpa [selected,offSector] using entry

#print axioms checked_sector_meaning
#print axioms checked_sector_action
#print axioms promoted_preserves_coordinates
#print axioms Qleisli.RoutedControlCommutation.sector_locality_exchange_reference

end Qleisli.Raw.AccessCommutation
