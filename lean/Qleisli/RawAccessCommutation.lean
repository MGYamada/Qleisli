import Qleisli.RawBranchFunction
import Qleisli.RawPureInstrumentAction
import Qleisli.RoutedControlCommutation
import Qleisli.RuntimeAdjacentInterval
import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeCallPureFold
import Qleisli.RuntimeForestProduct
import Qleisli.RuntimeIntervalTrace
import Qleisli.RuntimeNamedThreePackedOutput
import QleisliKernel.Qirf.RuntimeNamedFrameAxes
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

section CallerAxes
variable {artifact : Artifact} {root : Validity.Root} {owner name signature tokens}
  {block : RuntimeInterval.Prepared root.dependencies root.program} {callee start count inputs outputs}
  {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
  {call : @RuntimeAccessInterval.Checked tokens root.dependencies root.program callee source.lookup source.naturals
    (fun _ _ => none) block.block start count inputs outputs} {request : RuntimeAccessCallee.Context}

/-- Physical coordinates are recovered from the actual parent frame in the
same order as the original argument ports and each port's ordered wires. -/
def callerAxes : List Nat :=
  RuntimeForestCode.portAxes call.frame.interval.before.quantum.frame call.frame.selected

theorem checked_caller_axes (checked : RuntimeAccessCallee.Checked source call request) :
    let frame := call.frame.interval.before.quantum.frame
    let axes := callerAxes (call := call)
    axes.Nodup ∧ (∀ axis ∈ axes, axis < frame.length) ∧
      axes.mapM (fun axis => frame[axis]?) = some (call.places.flatMap (·.axes)) ∧
      checked.execution.prepared.entry.quantum.frame = call.places.flatMap (·.axes) := by
  intro frame axes
  let wires := call.frame.selected.flatMap Semantics.Raw.Port.wires
  have initial := RuntimeNamedFrameAxes.initialized checked.execution.prepared.inputRead
  have childFrame : checked.execution.prepared.entry.quantum.frame = wires := congrArg
    Semantics.RawTrace.Interface.frame initial.1
  have unique : wires.Nodup := by
    rw [← childFrame]
    exact (Raw.Ownership.valid _ initial.2.1).frame
  have selected := (RuntimeNamedFrameAxes.selectedPorts _ _ _ call.frame.atEntry).1
  have covered : wires ⊆ frame := by
    intro wire present
    obtain ⟨port,portMember,wireMember⟩ := List.mem_flatMap.mp present
    exact (Raw.Ownership.valid _ call.frame.interval.history.1).covered wire
      (List.mem_flatMap.mpr ⟨port,selected portMember,wireMember⟩)
  have written : wires = call.places.flatMap (·.axes) := by
    simpa only [wires,List.flatMap_def] using congrArg List.flatten call.inputAxes
  have lookup (ordered : List Nat) (inside : ordered ⊆ frame) :
      (ordered.map frame.idxOf).mapM (fun axis => frame[axis]?) = some ordered := by
    rw [List.mapM_map]
    induction ordered with
    | nil => rfl
    | cons wire rest ih =>
      have present := inside List.mem_cons_self
      have tail := ih (fun _ member => inside (List.mem_cons_of_mem _ member))
      simp [List.mapM_cons,RuntimeNamedFrameAxes.wireLookup frame present,tail]
  change (wires.map frame.idxOf).Nodup ∧ _ ∧ _ ∧ _
  refine ⟨List.Nodup.map_on (fun wire member _ _ equal => (List.idxOf_inj (covered member)).mp equal) unique,
    ?_,(lookup wires covered).trans (congrArg some written),childFrame.trans written⟩
  intro axis member
  obtain ⟨wire,found,rfl⟩ := List.mem_map.mp member
  exact List.idxOf_lt_length_of_mem (covered found)

#print axioms checked_caller_axes

/-- Tie the promoted coefficients to the actual checked callee's Raw wire
coordinates and to the coherent control mask read from its source call. -/
theorem checked_caller_promotion (checked : RuntimeAccessCallee.Checked source call request)
    (sectors : RuntimeAccessInterval.Sectors call)
    (actual : Semantics.Exact.Matrix) (work left : Nat)
    (read : (Raw.promote call.frame.interval.before.quantum.frame.length
      (callerAxes (call := call)) sectors.actual).run work = (.ok actual,left))
    (row : Fin actual.rows) (col : Fin actual.cols) :
    (let axes := callerAxes (call := call)
     Qleisli.Semantics.Exact.entry actual row.val col.val =
       if Semantics.Finite.scatter col.val axes (Semantics.Finite.gather row.val axes) == row.val then
         Qleisli.Semantics.Exact.entry sectors.actual
           (Semantics.Finite.gather row.val axes) (Semantics.Finite.gather col.val axes)
       else 0) ∧
      (callerAxes (call := call)).mapM (fun axis => call.frame.interval.before.quantum.frame[axis]?) =
        some checked.execution.prepared.entry.quantum.frame := by
  have geometry := checked_caller_axes checked
  exact ⟨(Qleisli.Raw.promote_denotes _ _ _ _ work left read).2.2 _ _ row.isLt col.isLt,
    geometry.2.2.1.trans (congrArg some geometry.2.2.2.symm)⟩

#print axioms checked_caller_promotion

/-- The complete coordinate order is the actual argument axes followed by the
remaining caller axes in their original order. Gather on this order is a
bijection of the caller's finite computational basis. -/
theorem checked_caller_route (checked : RuntimeAccessCallee.Checked source call request) :
    let width := call.frame.interval.before.quantum.frame.length
    let axes := callerAxes (call := call)
    let order := axes ++ (List.range width).filter (fun axis => !axes.contains axis)
    ∃ route : Fin (2^width) ≃ Fin (2^width),
      ∀ label, (route label).val = Semantics.Finite.gather label.val order := by
  intro width axes order
  have geometry := checked_caller_axes checked
  have unique : order.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨geometry.1,List.nodup_range.filter _,?_⟩
    intro axis member spectator held same
    subst spectator
    simpa [member] using (List.mem_filter.mp held).2
  have permutation : order.Perm (List.range width) := by
    apply (List.perm_ext_iff_of_nodup unique List.nodup_range).mpr
    intro axis
    constructor
    · intro member
      rcases List.mem_append.mp member with selected | spectator
      · exact List.mem_range.mpr (geometry.2.1 axis selected)
      · exact (List.mem_filter.mp spectator).1
    · intro member
      by_cases selected : axis ∈ axes
      · exact List.mem_append_left _ selected
      · exact List.mem_append_right _ (List.mem_filter.mpr ⟨member,by simpa using selected⟩)
  obtain ⟨gather,bijection,equation⟩ := Qleisli.RuntimeNamedThreePackedOutput.gather_bijective width order permutation
  exact ⟨Equiv.ofBijective gather bijection,equation⟩

#print axioms checked_caller_route
end CallerAxes

/-- The same computational basis can be ordered by shared coordinates, first
only, second only, and spectators. Each region keeps caller order. -/
def commonOrder (width : Nat) (first second : List Nat) : List Nat :=
  let (onFirst,offFirst) := (List.range width).partition (fun axis => first.contains axis)
  let (shared,firstOnly) := onFirst.partition (fun axis => second.contains axis)
  let (secondOnly,spectators) := offFirst.partition (fun axis => second.contains axis)
  shared ++ firstOnly ++ secondOnly ++ spectators

theorem commonOrder_perm (width : Nat) (first second : List Nat) :
    (commonOrder width first second).Perm (List.range width) := by
  simp only [commonOrder,List.partition_eq_filter_filter, List.append_assoc]
  let original := List.range width
  let onFirst := original.filter (fun axis => first.contains axis)
  let offFirst := original.filter (fun axis => !first.contains axis)
  have firstSplit := List.filter_append_perm (fun axis => second.contains axis) onFirst
  have secondSplit := List.filter_append_perm (fun axis => second.contains axis) offFirst
  have grouped := firstSplit.append secondSplit
  simpa only [onFirst,offFirst,original,List.append_assoc] using
    grouped.trans (List.filter_append_perm (fun axis => first.contains axis) original)

theorem commonOrder_bijective (width : Nat) (first second : List Nat) :
    ∃ route : Fin (2^width) ≃ Fin (2^width),
      ∀ label, (route label).val = Semantics.Finite.gather label.val (commonOrder width first second) := by
  obtain ⟨gather,bijective,equation⟩ := Qleisli.RuntimeNamedThreePackedOutput.gather_bijective
    width (commonOrder width first second) (commonOrder_perm width first second)
  exact ⟨Equiv.ofBijective gather bijective,equation⟩

example : commonOrder 6 [4,1,5] [3,5,1] = [1,5,4,3,0,2] := by decide
example : commonOrder 2 [] [0] = [0,1] := by decide

#print axioms commonOrder_bijective

/-- In a checked pair, a wire common to both actual ordered argument lists
comes from a coherent control operand on each side. -/
theorem shared_wires_are_controls
    {sources owner name dependencies program signature root source firstStart firstCount firstInputs firstOutputs
      first start count inputs outputs}
    (second : @RuntimeAccessPartition.Second sources owner name dependencies program signature root source
      firstStart firstCount firstInputs firstOutputs first start count inputs outputs)
    (wire : Nat)
    (left : wire ∈ first.call.interval.frame.selected.flatMap Semantics.Raw.Port.wires)
    (right : wire ∈ second.call.frame.selected.flatMap Semantics.Raw.Port.wires) :
    (∃ place ∈ first.call.interval.places, place.role = .ctrl ∧ wire ∈ place.axes) ∧
      (∃ place ∈ second.call.places, place.role = .ctrl ∧ wire ∈ place.axes) := by
  simp only [List.flatMap_def,first.call.interval.inputAxes] at left
  simp only [List.flatMap_def,second.call.inputAxes] at right
  rw [← List.flatMap_def] at left right
  obtain ⟨a,inFirst,onFirst⟩ := List.mem_flatMap.mp left
  obtain ⟨b,inSecond,onSecond⟩ := List.mem_flatMap.mp right
  have controls : a.role = .ctrl ∧ b.role = .ctrl := by
    cases ha : a.role <;> cases hb : b.role
    · exact ⟨rfl,rfl⟩
    · exact False.elim (SourceTypes.AccessSyntax.exclusive_disjoint _ _ second.compatible
        a b inFirst inSecond (.inr hb) wire onFirst onSecond)
    · exact False.elim (SourceTypes.AccessSyntax.exclusive_disjoint _ _ second.compatible
        a b inFirst inSecond (.inl ha) wire onFirst onSecond)
    · exact False.elim (SourceTypes.AccessSyntax.exclusive_disjoint _ _ second.compatible
        a b inFirst inSecond (.inl ha) wire onFirst onSecond)
  exact ⟨⟨a,inFirst,controls.1,onFirst⟩,⟨b,inSecond,controls.2,onSecond⟩⟩

#print axioms shared_wires_are_controls

open SourceTypes.AccessSyntax (Place) in
private theorem written_control_position (places : List Place) (offset : Nat) (prior : List Nat)
    (place : Place) (member : place ∈ places) (control : place.role = .ctrl)
    (wire : Nat) (present : wire ∈ place.axes) :
    ∃ index, (places.flatMap (·.axes))[index]? = some wire ∧
      offset+index ∈ (places.foldl (fun (base,axes) item =>
        (base+item.axes.length, if item.role == .ctrl then
          axes ++ (List.range item.axes.length).map (base+·) else axes)) (offset,prior)).2 := by
  have retained (items : List Place) (base : Nat) (before : List Nat) (index : Nat)
      (held : index ∈ before) :
      index ∈ (items.foldl (fun (base,axes) item =>
        (base+item.axes.length, if item.role == .ctrl then
          axes ++ (List.range item.axes.length).map (base+·) else axes)) (base,before)).2 := by
    induction items generalizing base before with
    | nil => exact held
    | cons first rest ih =>
      simp only [List.foldl_cons]
      apply ih
      split <;> simp [held]
  induction places generalizing offset prior with
  | nil => cases member
  | cons first rest ih =>
    simp only [List.flatMap_cons,List.foldl_cons]
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨index,bounded,read⟩ := List.getElem_of_mem present
      refine ⟨index,?_,?_⟩
      · rw [List.getElem?_append_left bounded,List.getElem?_eq_getElem bounded,read]
      · apply retained
        have indexed : offset+index ∈ (List.range place.axes.length).map (offset+·) :=
          List.mem_map_of_mem (List.mem_range.mpr bounded)
        rw [control]
        exact List.mem_append_right _ indexed
    · obtain ⟨index,read,held⟩ := ih (offset+first.axes.length)
        (if first.role == .ctrl then prior ++ (List.range first.axes.length).map (offset+·) else prior) later
      refine ⟨first.axes.length+index,?_,?_⟩
      · rwa [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
      · simpa only [Nat.add_assoc] using held

/-- A written coherent control wire occurs at its actual position in the
matrix mask, even when its port follows an exclusive or zero-width port. -/
theorem control_wire_index (places : List SourceTypes.AccessSyntax.Place)
    (place : SourceTypes.AccessSyntax.Place) (member : place ∈ places) (control : place.role = .ctrl)
    (wire : Nat) (present : wire ∈ place.axes) :
    ∃ index ∈ RuntimeAccessInterval.controlAxes places, (places.flatMap (·.axes))[index]? = some wire := by
  obtain ⟨index,read,held⟩ := written_control_position places 0 [] place member control wire present
  exact ⟨index,by simpa only [Nat.zero_add,RuntimeAccessInterval.controlAxes] using held,read⟩

#print axioms control_wire_index

section SharedCoordinate
variable {artifact : Artifact} {root : Validity.Root} {owner name signature tokens}
  {block : RuntimeInterval.Prepared root.dependencies root.program} {callee start count inputs outputs}
  {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
  {call : @RuntimeAccessInterval.Checked tokens root.dependencies root.program callee source.lookup source.naturals
    (fun _ _ => none) block.block start count inputs outputs} {request : RuntimeAccessCallee.Context}

/-- A nonzero promoted entry cannot change the physical bit of any written
coherent-control operand. The frame lookup rules out a default axis. -/
theorem checked_caller_control_bit
    (sectors : RuntimeAccessInterval.Sectors call) (actual : Semantics.Exact.Matrix) (work left : Nat)
    (read : (Raw.promote call.frame.interval.before.quantum.frame.length
      (callerAxes (call := call)) sectors.actual).run work = (.ok actual,left))
    (row : Fin actual.rows) (col : Fin actual.cols)
    (nonzero : Qleisli.Semantics.Exact.entry actual row.val col.val ≠ 0)
    (place : SourceTypes.AccessSyntax.Place) (member : place ∈ call.places) (control : place.role = .ctrl)
    (wire : Nat) (present : wire ∈ place.axes) :
    Semantics.Finite.bit row.val (call.frame.interval.before.quantum.frame.idxOf wire) =
      Semantics.Finite.bit col.val (call.frame.interval.before.quantum.frame.idxOf wire) := by
  let axis := call.frame.interval.before.quantum.frame.idxOf wire
  obtain ⟨index,maskMember,written⟩ := control_wire_index call.places place member control wire present
  have original : (call.frame.selected.flatMap Semantics.Raw.Port.wires)[index]? = some wire := by
    rw [List.flatMap_def,call.inputAxes,← List.flatMap_def]
    exact written
  have mapped : (callerAxes (call := call))[index]? = some axis := by
    simp only [callerAxes,RuntimeForestCode.portAxes,List.getElem?_map,original,Option.map_some,axis]
  have axisBound : index < (callerAxes (call := call)).length := List.getElem?_eq_some_iff.mp mapped |>.1
  have axisEq : (callerAxes (call := call))[index]'axisBound = axis := by
    simpa only [List.getElem?_eq_getElem axisBound,Option.some.injEq] using mapped
  obtain ⟨position,maskBound,maskEq⟩ := List.getElem_of_mem maskMember
  have preserves := (promoted_preserves_coordinates sectors _ _ actual work left read row col nonzero).2
  have bitEq := congrArg (fun label => Semantics.Finite.bit label position) preserves
  dsimp only at bitEq
  rw [RuntimeScatterTransport.gather_at _ _ _ maskBound,
    RuntimeScatterTransport.gather_at _ _ _ maskBound,maskEq,
    RuntimeScatterTransport.gather_at _ _ _ axisBound,
    RuntimeScatterTransport.gather_at _ _ _ axisBound,axisEq] at bitEq
  exact bitEq

#print axioms checked_caller_control_bit
end SharedCoordinate

section PromotionFactors
open Semantics.Finite (bit gather scatter)
open Qleisli.Semantics.Exact (entry)

private theorem labels_equal_of_bits (a b : Nat) (equal : ∀ axis, bit a axis = bit b axis) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro axis
  have same := equal axis
  simp only [bit,← Nat.toNat_testBit] at same
  cases left : a.testBit axis <;> cases right : b.testBit axis <;> simp_all

private theorem scatter_gather_eq_iff (axes : List Nat) (unique : axes.Nodup) (row col : Nat) :
    scatter col axes (gather row axes) = row ↔ ∀ axis ∉ axes, bit row axis = bit col axis := by
  constructor
  · intro same axis outside
    rw [← same]
    exact RuntimeScatterTransport.scatter_outside _ _ _ _ outside
  · intro outside
    apply labels_equal_of_bits
    intro axis
    by_cases selected : axis ∈ axes
    · obtain ⟨index,bound,rfl⟩ := List.getElem_of_mem selected
      rw [RuntimeScatterTransport.scatter_at _ _ _ unique _ bound,
        RuntimeScatterTransport.gather_at _ _ _ bound]
    · rw [RuntimeScatterTransport.scatter_outside _ _ _ _ selected,outside axis selected]

private theorem gather_same_on (axes : List Nat) (row col : Nat)
    (same : ∀ axis ∈ axes, bit row axis = bit col axis) : gather row axes = gather col axes := by
  unfold gather
  apply congrArg List.sum
  apply List.map_congr_left
  intro indexed member
  rcases indexed with ⟨axis,index⟩
  change bit row axis * 2^index = bit col axis * 2^index
  rw [same axis (List.fst_mem_of_mem_zipIdx member)]

/-- The coefficient of an actual promotion is its local coefficient on the
unchanged spectator fibre. The identity factors can be read one bit at a time. -/
theorem promotion_entry_on_fibre (bits : Nat) (axes : List Nat) (localMap actual : Semantics.Exact.Matrix)
    (work left : Nat) (read : (Raw.promote bits axes localMap).run work = (.ok actual,left))
    (row : Fin actual.rows) (col : Fin actual.cols) : open Classical in
    entry actual row.val col.val = if ∀ axis ∉ axes, bit row.val axis = bit col.val axis then
      entry localMap (gather row.val axes) (gather col.val axes) else 0 := by
  classical
  obtain ⟨_,middle,guarded,_⟩ := Finite.bind_success _ _ _ _ _ read
  have shape := (Finite.guard_success _ _ _ middle guarded).1
  simp only [Bool.and_eq_true,beq_iff_eq] at shape
  have valid := shape.1.1.2
  simp only [Finite.axesValid,Bool.and_eq_true] at valid
  have unique := Raw.Ownership.unique_nodup axes valid.2
  have coefficient := (Qleisli.Raw.promote_denotes _ _ _ _ work left read).2.2 _ _ row.isLt col.isLt
  simpa only [beq_iff_eq,scatter_gather_eq_iff axes unique] using coefficient

/-- When the local coordinates coincide, changing the spectator coordinates
within the same fibre cannot change the promoted coefficient. -/
theorem promotion_fibre_independence (bits : Nat) (axes : List Nat) (localMap actual : Semantics.Exact.Matrix)
    (work left : Nat) (read : (Raw.promote bits axes localMap).run work = (.ok actual,left))
    (row row' : Fin actual.rows) (col col' : Fin actual.cols)
    (rowLocal : ∀ axis ∈ axes, bit row.val axis = bit row'.val axis)
    (colLocal : ∀ axis ∈ axes, bit col.val axis = bit col'.val axis)
    (spectators : ∀ axis ∉ axes, bit row.val axis = bit col.val axis)
    (spectators' : ∀ axis ∉ axes, bit row'.val axis = bit col'.val axis) :
    entry actual row.val col.val = entry actual row'.val col'.val := by
  rw [promotion_entry_on_fibre bits axes localMap actual work left read row col, if_pos spectators,
    promotion_entry_on_fibre bits axes localMap actual work left read row' col', if_pos spectators',
    gather_same_on axes _ _ rowLocal,gather_same_on axes _ _ colLocal]

#print axioms promotion_entry_on_fibre
#print axioms promotion_fibre_independence
end PromotionFactors

/-- Read a shared caller coordinate through both checked argument lists.
The same coordinate in a common physical frame must identify the same wire. -/
theorem shared_caller_axis_is_control
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs)
    (sameFrame : first.call.interval.frame.interval.before.quantum.frame =
      second.call.frame.interval.before.quantum.frame)
    (axis : Nat) (left : axis ∈ callerAxes (call := first.call.interval))
    (right : axis ∈ callerAxes (call := second.call)) :
    ∃ wire, first.call.interval.frame.interval.before.quantum.frame[axis]? = some wire ∧
      (∃ place ∈ first.call.interval.places, place.role = .ctrl ∧ wire ∈ place.axes) ∧
      (∃ place ∈ second.call.places, place.role = .ctrl ∧ wire ∈ place.axes) := by
  obtain ⟨a,inFirst,firstIndex⟩ := List.mem_map.mp left
  obtain ⟨b,inSecond,secondIndex⟩ := List.mem_map.mp right
  have present {offset length : Nat} (interval : RuntimeInterval.Checked block.block offset length)
      (ports : List Semantics.Raw.Port)
      (tokens : List Nat) (read : PureInterval.ports interval.before tokens = some ports)
      (wire : Nat) (member : wire ∈ ports.flatMap (·.wires)) : wire ∈ interval.before.quantum.frame := by
    obtain ⟨port,selected,onPort⟩ := List.mem_flatMap.mp member
    have live := (RuntimeNamedFrameAxes.selectedPorts _ _ _ read).1 selected
    exact (Raw.Ownership.valid _ interval.history.1).covered wire (List.mem_flatMap.mpr ⟨port,live,onPort⟩)
  have firstPresent := present _ _ _ first.call.interval.frame.atEntry a inFirst
  have secondPresent := present _ _ _ second.call.frame.atEntry b inSecond
  have firstRead := RuntimeNamedFrameAxes.wireLookup _ firstPresent
  have secondRead := RuntimeNamedFrameAxes.wireLookup _ secondPresent
  change first.call.interval.frame.interval.before.quantum.frame.idxOf a = axis at firstIndex
  change second.call.frame.interval.before.quantum.frame.idxOf b = axis at secondIndex
  rw [firstIndex] at firstRead
  rw [secondIndex,← sameFrame] at secondRead
  have same := Option.some.inj (firstRead.symm.trans secondRead)
  subst b
  exact ⟨a,firstRead,shared_wires_are_controls second a inFirst inSecond⟩

#print axioms Qleisli.RoutedControlCommutation.sector_fibre_exchange
#print axioms shared_caller_axis_is_control

/-- The first promoted call can change only coordinates used exclusively by
that call. The second call's selected coordinates are therefore preserved. -/
theorem first_promotion_preserves_second_axes
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs)
    (sameFrame : first.call.interval.frame.interval.before.quantum.frame =
      second.call.frame.interval.before.quantum.frame)
    (sectors : RuntimeAccessInterval.Sectors first.call.interval)
    (actual : Semantics.Exact.Matrix) (work left : Nat)
    (read : (Raw.promote first.call.interval.frame.interval.before.quantum.frame.length
      (callerAxes (call := first.call.interval)) sectors.actual).run work = (.ok actual,left))
    (row : Fin actual.rows) (col : Fin actual.cols)
    (nonzero : Qleisli.Semantics.Exact.entry actual row.val col.val ≠ 0)
    (axis : Nat) (secondUses : axis ∈ callerAxes (call := second.call)) :
    Semantics.Finite.bit row.val axis = Semantics.Finite.bit col.val axis := by
  by_cases firstUses : axis ∈ callerAxes (call := first.call.interval)
  · obtain ⟨wire,wireAt,⟨place,member,control,present⟩,_⟩ :=
      shared_caller_axis_is_control second sameFrame axis firstUses secondUses
    have wireIn := List.mem_of_getElem? wireAt
    have indexed := RuntimeNamedFrameAxes.wireLookup _ wireIn
    have position : first.call.interval.frame.interval.before.quantum.frame.idxOf wire = axis := by
      have valid := (Raw.Ownership.valid _ first.call.interval.frame.interval.history.1).frame
      exact (List.getElem?_inj (List.idxOf_lt_length_of_mem wireIn) valid).mp (indexed.trans wireAt.symm)
    rw [← position]
    exact checked_caller_control_bit sectors actual work left read row col nonzero place member control wire present
  · exact (promoted_preserves_coordinates sectors _ _ actual work left read row col nonzero).1 axis firstUses

#print axioms first_promotion_preserves_second_axes

/-- The source-bound extracts, calls and restores are consecutive reads of
one Raw block. The matched boundaries retain the complete observing state. -/
theorem checked_pair_boundaries
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs) :
    first.owners.preamble.after = first.call.interval.frame.interval.before ∧
    first.call.interval.frame.interval.after = first.owners.routing.before ∧
    first.owners.routing.after = second.owners.preamble.before ∧
    second.owners.preamble.after = second.call.frame.interval.before ∧
    second.call.frame.interval.after = second.owners.routing.before := by
  have adjacentAt {deps program} {body : RuntimeInterval.Block deps program} {begin count offset length : Nat}
      (route : RuntimeInterval.Checked body begin count)
      (call : RuntimeInterval.Checked body offset length) (stop : begin+count = offset) :
      route.after = call.before := by
    subst offset
    exact RuntimeAdjacentSlices.adjacent route call
  exact ⟨adjacentAt first.owners.preamble first.call.interval.frame.interval (by simp),
    RuntimeAdjacentSlices.adjacent first.call.interval.frame.interval first.owners.routing,
    RuntimeAdjacentSlices.adjacent first.owners.routing second.owners.preamble,
    adjacentAt second.owners.preamble second.call.frame.interval (Nat.add_sub_of_le second.owners.bounded),
    RuntimeAdjacentSlices.adjacent second.call.frame.interval second.owners.routing⟩

#print axioms checked_pair_boundaries

private theorem take_frame {before after : Semantics.RawTrace.Interface} {token port}
    (read : Semantics.RawTrace.take before token = some (port,after)) :
    after.frame = before.frame := by
  unfold Semantics.RawTrace.take at read
  obtain ⟨_,_,returned⟩ := Option.bind_eq_some_iff.mp read
  exact (congrArg (fun pair : Semantics.Raw.Port × Semantics.RawTrace.Interface => pair.2.frame)
    (Option.some.inj returned)).symm

private theorem structural_step {before after : Semantics.RawTrace.Interface} {operation events}
    (read : Semantics.RawTrace.step before operation = some (after,events))
    (routing : RuntimeAccessPartition.isRoute (.pure operation) = true) :
    after.frame = before.frame ∧ events = [] := by
  cases operation <;> simp only [RuntimeAccessPartition.isRoute,Bool.false_eq_true] at routing
  case split input left right bits =>
    simp only [Semantics.RawTrace.step] at read
    obtain ⟨⟨port,rest⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp read
    have data := Prod.mk.inj (Option.some.inj returned)
    have frame := congrArg Semantics.RawTrace.Interface.frame data.1
    change rest.frame = after.frame at frame
    exact ⟨frame.symm.trans (take_frame taken),data.2.symm⟩
  case join left right output =>
    simp only [Semantics.RawTrace.step] at read
    obtain ⟨⟨l,rest⟩,leftRead,read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨r,tail⟩,rightRead,returned⟩ := Option.bind_eq_some_iff.mp read
    have data := Prod.mk.inj (Option.some.inj returned)
    have frame := congrArg Semantics.RawTrace.Interface.frame data.1
    change tail.frame = after.frame at frame
    exact ⟨frame.symm.trans ((take_frame rightRead).trans (take_frame leftRead)),data.2.symm⟩

private theorem structural_fold (operations : List Semantics.Raw.Op)
    {before after : Semantics.RawTrace.Prepared}
    (routing : (operations.map Semantics.Observation.Op.pure).all RuntimeAccessPartition.isRoute = true)
    (read : operations.foldlM Semantics.RawTrace.advance before = some after) :
    after.state.frame = before.state.frame ∧ after.events = before.events := by
  induction operations generalizing before with
  | nil =>
    cases Option.some.inj read
    exact ⟨rfl,rfl⟩
  | cons operation operations ih =>
    simp only [List.map_cons,List.all_cons,Bool.and_eq_true] at routing
    rw [List.foldlM_cons] at read
    obtain ⟨next,advanced,tail⟩ := Option.bind_eq_some_iff.mp read
    unfold Semantics.RawTrace.advance at advanced
    obtain ⟨⟨state,events⟩,stepped,returned⟩ := Option.bind_eq_some_iff.mp advanced
    have ⟨frame,empty⟩ := structural_step stepped routing.1
    have same := Option.some.inj returned
    subst next
    have ⟨lastFrame,lastEvents⟩ := ih routing.2 tail
    exact ⟨lastFrame.trans frame,by simpa only [empty,List.append_nil] using lastEvents⟩

/-- The actual routing slice changes owner ports and keeps the complete
physical frame in order. Its independent trace emits no quantum events. -/
theorem structural_interval {dependencies program} {block : RuntimeInterval.Block dependencies program}
    {start count} (interval : RuntimeInterval.Checked block start count)
    (routing : (((block.operations.drop start).take count).all RuntimeAccessPartition.isRoute) = true) :
    ∃ operations : List Semantics.Raw.Op,
      (block.operations.drop start).take count = operations.map Semantics.Observation.Op.pure ∧
      RuntimeLocalEvents.trace interval.before.quantum.reference operations =
        some ⟨interval.after.quantum.reference,[],interval.before.quantum.frame.length⟩ ∧
      interval.after.quantum.frame = interval.before.quantum.frame := by
  have pure_routes (operations : List RuntimeInterval.Op)
      (routes : operations.all RuntimeAccessPartition.isRoute = true) :
      ∃ pureOps : List Semantics.Raw.Op, operations = pureOps.map Semantics.Observation.Op.pure := by
    induction operations with
    | nil => exact ⟨[],rfl⟩
    | cons operation operations ih =>
      simp only [List.all_cons,Bool.and_eq_true] at routes
      obtain ⟨tail,equation⟩ := ih routes.2
      cases operation with
      | pure op => exact ⟨op :: tail,congrArg _ equation⟩
      | _ => cases routes.1
  obtain ⟨operations,original⟩ := pure_routes _ routing
  obtain ⟨work,left,read⟩ := interval.intervalRead
  rw [original] at read routing
  obtain ⟨events,trace⟩ := RuntimeIntervalTrace.checkOps_pure_trace dependencies block.fuel
    interval.before interval.after operations work left read
  have ⟨frame,empty⟩ := structural_fold operations routing trace
  change events = [] at empty
  subst events
  exact ⟨operations,original,trace,frame⟩

theorem checked_routing_intervals {tokens dependencies program block callee lookup names calls start count inputs outputs}
    {call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs}
    {entry begin} (routing : RuntimeAccessPartition.Restored call entry begin) :
    routing.preamble.after.quantum.frame = routing.preamble.before.quantum.frame ∧
    routing.routing.after.quantum.frame = routing.routing.before.quantum.frame := by
  have allowed := RuntimeAccessPartition.replay_routes routing.replayed
  exact ⟨(structural_interval routing.preamble allowed.1).choose_spec.2.2,
    (structural_interval routing.routing allowed.2).choose_spec.2.2⟩

#print axioms structural_interval
#print axioms checked_routing_intervals

private theorem selected_spectator_partition (state : Raw.Observation.State)
    (valid : Raw.stateValid state.quantum = true) (tokens : List Nat) (selected : List Semantics.Raw.Port)
    (read : PureInterval.ports state tokens = some selected) (unique : tokens.Nodup) :
    state.quantum.live.Perm (selected ++ PureInterval.spectators state tokens) := by
  let chosen := fun port : Semantics.Raw.Port => tokens.contains port.token
  have ⟨present,order⟩ := RuntimeNamedFrameAxes.selectedPorts _ _ _ read
  have owners := (Raw.Ownership.valid _ valid).owners
  have liveUnique : state.quantum.live.Nodup := List.Pairwise.of_map (·.token)
    (fun _ _ different same => different (congrArg Semantics.Raw.Port.token same)) owners
  have selectedUnique : selected.Nodup := List.Pairwise.of_map (·.token)
    (fun _ _ different same => different (congrArg Semantics.Raw.Port.token same)) (order.symm ▸ unique)
  have selectedPerm : (state.quantum.live.filter chosen).Perm selected := by
    apply (List.perm_ext_iff_of_nodup (List.filter_sublist.nodup liveUnique) selectedUnique).mpr
    intro port
    constructor
    · intro found
      have ⟨live,chosenPort⟩ := List.mem_filter.mp found
      have token : port.token ∈ selected.map (·.token) := order.symm ▸ List.contains_iff_mem.mp chosenPort
      obtain ⟨original,selectedPort,same⟩ := List.mem_map.mp token
      have first := RuntimeNamedFrameAxes.tokenLookup _ port owners live
      have second := RuntimeNamedFrameAxes.tokenLookup _ original owners (present selectedPort)
      rw [same] at second
      exact (Option.some.inj (second.symm.trans first)) ▸ selectedPort
    · intro member
      exact List.mem_filter.mpr ⟨present member,List.contains_iff_mem.mpr
        (order ▸ List.mem_map_of_mem (f := Semantics.Raw.Port.token) member)⟩
  exact (List.filter_append_perm chosen state.quantum.live).symm.trans
    (selectedPerm.append_right (PureInterval.spectators state tokens))

private theorem checked_call_input_unique
    {tokens dependencies program block callee lookup names calls start count inputs outputs}
    (call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs) : inputs.Nodup := by
  obtain ⟨work,left,read⟩ := call.frame.pureRead
  have prepared := (Raw.Pure.verify_conditions _ _ _ work left read).1
  obtain ⟨initial,_,opened,_,_,_,_⟩ := Raw.prepare_conditions _ _ _ prepared
  have initialValid := Raw.inputs_valid _ _ _ (by decide) opened
  have inputUnique := (Raw.Ownership.valid _ initialValid).owners
  change (initial.live.map (·.token)).Nodup at inputUnique
  have live := congrArg Semantics.RawTrace.Interface.live (Raw.inputs_reference _ _ _ opened)
  change initial.live = [] ++ call.frame.selected at live
  rw [live,List.nil_append,(RuntimeNamedFrameAxes.selectedPorts _ _ _ call.frame.atEntry).2] at inputUnique
  exact inputUnique

/-- The selected input and returned wire lists agree in the original call.
Together with its checked spectator list they account for the same physical
width at both complete Raw boundaries, including zero-width owner tokens. -/
theorem checked_call_width {tokens dependencies program block callee lookup names calls start count inputs outputs}
    (call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs) :
    call.frame.interval.after.quantum.frame.length = call.frame.interval.before.quantum.frame.length := by
  obtain ⟨work,left,read⟩ := call.frame.pureRead
  let fragment := RuntimePureInterval.fragment call.frame.selected call.frame.operations outputs
  have prepared := (Raw.Pure.verify_conditions dependencies fragment call.frame.pureBody work left read).1
  obtain ⟨_,_,_,_,finished,_,_⟩ := Raw.prepare_conditions _ _ _ prepared
  have outputUnique : outputs.Nodup := by
    simp only [Raw.outputValid,Bool.and_eq_true] at finished
    exact Raw.Ownership.unique_nodup outputs finished.1.1.1.1
  have before := selected_spectator_partition _ call.frame.interval.history.1 _ _ call.frame.atEntry
    (checked_call_input_unique call)
  have after := selected_spectator_partition _ call.frame.interval.history.2.2.1 _ _ call.frame.atExit outputUnique
  have beforeLength := (before.flatMap_right Semantics.Raw.Port.wires).length_eq
  have afterLength := (after.flatMap_right Semantics.Raw.Port.wires).length_eq
  have beforeCount := (Raw.Ownership.valid _ call.frame.interval.history.1).count
  have afterCount := (Raw.Ownership.valid _ call.frame.interval.history.2.2.1).count
  change (call.frame.interval.before.quantum.live.flatMap (·.wires)).length =
    call.frame.interval.before.quantum.frame.length at beforeCount
  change (call.frame.interval.after.quantum.live.flatMap (·.wires)).length =
    call.frame.interval.after.quantum.frame.length at afterCount
  have wires : call.frame.returned.flatMap Semantics.Raw.Port.wires =
      call.frame.selected.flatMap Semantics.Raw.Port.wires := by
    simp only [List.flatMap_def,call.inputAxes,call.outputAxes]
  rw [← beforeCount,← afterCount,beforeLength,afterLength,List.flatMap_append,List.flatMap_append,
    call.frame.spectators,wires]

#print axioms checked_call_width

private theorem takeTargets_frame (targets : List Semantics.Raw.Target)
    (ports selected : List Semantics.Raw.Port) (before after : Semantics.RawTrace.Interface)
    (read : targets.foldlM (fun (ports,next) target => do
      let (port,next) ← Semantics.RawTrace.take next target.input
      pure (ports ++ [port],next)) (ports,before) = some (selected,after)) :
    after.frame = before.frame := by
  induction targets generalizing ports before with
  | nil => exact (congrArg (fun pair : List Semantics.Raw.Port × Semantics.RawTrace.Interface => pair.2.frame)
      (Option.some.inj read)).symm
  | cons target targets ih =>
    simp only [List.foldlM_cons] at read
    obtain ⟨⟨nextPorts,next⟩,first,tail⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨port,rest⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp first
    have frame : rest.frame = next.frame := congrArg
      (fun pair : List Semantics.Raw.Port × Semantics.RawTrace.Interface => pair.2.frame) (Option.some.inj returned)
    exact (ih nextPorts next tail).trans (frame.symm.trans (take_frame taken))

private theorem pure_step_frame_prefix {before after : Semantics.RawTrace.Interface} {operation events}
    (read : Semantics.RawTrace.step before operation = some (after,events)) : before.frame <+: after.frame := by
  have result {state : Semantics.RawTrace.Interface} {emitted : List Semantics.Raw.Event}
      (returned : some (state,emitted) = some (after,events)) : state.frame = after.frame :=
    congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame)
      (Option.some.inj returned)
  cases operation with
  | init0 output wire =>
    rw [← result read]
    exact ⟨[wire],rfl⟩
  | liftBasis input output wires table =>
    obtain ⟨⟨port,rest⟩,_,returned⟩ := Option.bind_eq_some_iff.mp read
    rw [← result returned]
    exact ⟨wires.drop port.bits,rfl⟩
  | computeUseUncompute input output targets ancilla function uses =>
    obtain ⟨⟨port,rest⟩,taken,tail⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨ports,last⟩,selected,returned⟩ := Option.bind_eq_some_iff.mp tail
    let insert := fun (next : Semantics.RawTrace.Interface) (item : Semantics.Raw.Target × Semantics.Raw.Port) =>
      Semantics.RawTrace.insert next item.1.output item.2.wires
    have unchanged (items : List (Semantics.Raw.Target × Semantics.Raw.Port)) (next : Semantics.RawTrace.Interface) :
        (items.foldl insert next).frame = next.frame := by
      induction items generalizing next with
      | nil => rfl
      | cons head tail ih => exact ih (insert next head)
    rw [← result returned]
    change before.frame <+: ((targets.zip ports).foldl insert (Semantics.RawTrace.insert last output port.wires)).frame
    rw [unchanged]
    have frame := (takeTargets_frame targets [] ports rest last selected).trans (take_frame taken)
    change before.frame <+: last.frame
    rw [frame]
  | packUnit output =>
    rw [← result read]
    exact List.prefix_rfl
  | unpackUnit input =>
    simp only [Semantics.RawTrace.step] at read
    obtain ⟨⟨port,rest⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp read
    split at returned
    · rw [← result returned, take_frame taken]
    · cases returned
  | gate | cnot | toffoli | quantumIf | split | join | applyUnitary | certifiedCompute =>
    simp only [Semantics.RawTrace.step] at read
    obtain ⟨⟨port,rest⟩,taken,tail⟩ := Option.bind_eq_some_iff.mp read
    have first := take_frame taken
    first
    | have frame := result tail
      simp only [Semantics.RawTrace.insert] at frame
      rw [← frame,first]
    | obtain ⟨⟨port₂,rest₂⟩,taken₂,tail₂⟩ := Option.bind_eq_some_iff.mp tail
      have second := take_frame taken₂
      first
      | have frame := result tail₂
        simp only [Semantics.RawTrace.insert] at frame
        rw [← frame,second,first]
      | obtain ⟨⟨port₃,rest₃⟩,taken₃,tail₃⟩ := Option.bind_eq_some_iff.mp tail₂
        have third := take_frame taken₃
        have frame := result tail₃
        simp only [Semantics.RawTrace.insert] at frame
        rw [← frame,third,second,first]

private theorem pure_fold_frame_prefix (operations : List Semantics.Raw.Op)
    {before after : Semantics.RawTrace.Prepared}
    (read : operations.foldlM Semantics.RawTrace.advance before = some after) :
    before.state.frame <+: after.state.frame := by
  induction operations generalizing before with
  | nil => cases Option.some.inj read; exact List.prefix_rfl
  | cons operation operations ih =>
    rw [List.foldlM_cons] at read
    obtain ⟨next,advanced,tail⟩ := Option.bind_eq_some_iff.mp read
    unfold Semantics.RawTrace.advance at advanced
    obtain ⟨⟨state,events⟩,stepped,returned⟩ := Option.bind_eq_some_iff.mp advanced
    have same := Option.some.inj returned
    subst next
    exact (pure_step_frame_prefix stepped).trans (ih tail)

/-- Pure Raw instructions keep the existing frame as a prefix. The exact
selected and spectator widths rule out growth in an original access call. -/
theorem checked_call_frame {tokens dependencies program block callee lookup names calls start count inputs outputs}
    (call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs) :
    call.frame.interval.after.quantum.frame = call.frame.interval.before.quantum.frame := by
  obtain ⟨result,read,after,_⟩ := RuntimeIntervalTrace.interval_trace call.frame
  have kept := pure_fold_frame_prefix call.frame.operations read
  rw [after] at kept
  exact (kept.eq_of_length (checked_call_width call).symm).symm

/-- Both written calls refer to the same ordered caller frame. The equality
comes from the actual intervening calls and checked split/join operations. -/
theorem checked_pair_frame
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs) :
    first.call.interval.frame.interval.before.quantum.frame = second.call.frame.interval.before.quantum.frame := by
  obtain ⟨_,firstRestore,between,secondExtract,_⟩ := checked_pair_boundaries second
  have restored := (checked_routing_intervals first.owners).2
  have extracted := (checked_routing_intervals second.owners).1
  rw [← firstRestore,between] at restored
  rw [secondExtract] at extracted
  exact ((extracted.trans restored).trans (checked_call_frame first.call.interval)).symm

#print axioms checked_call_frame
#print axioms checked_pair_frame

/-- The second call preserves every physical axis used by the first call.
The intervening checked operations supply the common frame. -/
theorem second_promotion_preserves_first_axes
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs)
    (sectors : RuntimeAccessInterval.Sectors second.call)
    (actual : Semantics.Exact.Matrix) (work left : Nat)
    (read : (Raw.promote second.call.frame.interval.before.quantum.frame.length
      (callerAxes (call := second.call)) sectors.actual).run work = (.ok actual,left))
    (row : Fin actual.rows) (col : Fin actual.cols)
    (nonzero : Qleisli.Semantics.Exact.entry actual row.val col.val ≠ 0)
    (axis : Nat) (firstUses : axis ∈ callerAxes (call := first.call.interval)) :
    Semantics.Finite.bit row.val axis = Semantics.Finite.bit col.val axis := by
  by_cases secondUses : axis ∈ callerAxes (call := second.call)
  · have same := checked_pair_frame second
    obtain ⟨wire,atFirst,_,place,member,control,present⟩ :=
      shared_caller_axis_is_control second same axis firstUses secondUses
    have atSecond : second.call.frame.interval.before.quantum.frame[axis]? = some wire := same ▸ atFirst
    have wireIn := List.mem_of_getElem? atSecond
    have indexed := RuntimeNamedFrameAxes.wireLookup _ wireIn
    have position : second.call.frame.interval.before.quantum.frame.idxOf wire = axis := by
      have valid := (Raw.Ownership.valid _ second.call.frame.interval.history.1).frame
      exact (List.getElem?_inj (List.idxOf_lt_length_of_mem wireIn) valid).mp (indexed.trans atSecond.symm)
    rw [← position]
    exact checked_caller_control_bit sectors actual work left read row col nonzero place member control wire present
  · exact (promoted_preserves_coordinates sectors _ _ actual work left read row col nonzero).1 axis secondUses

#print axioms second_promotion_preserves_first_axes

/-- The original local and caller traces are related at every coefficient,
using the spectator partition derived from the actual source-bound inputs. -/
theorem checked_call_literal_action
    {tokens dependencies program block callee lookup names calls start count inputs outputs}
    (call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs) :
    let frame := call.frame
    let spectators := PureInterval.spectators frame.interval.before inputs
    ∃ entry : Raw.State, ∃ parentEvents childEvents,
      entry.reference = ⟨frame.selected,frame.selected.flatMap (·.wires)⟩ ∧
      RuntimeLocalEvents.trace frame.interval.before.quantum.reference frame.operations =
        some ⟨frame.interval.after.quantum.reference,parentEvents,frame.interval.before.quantum.frame.length⟩ ∧
      RuntimeLocalEvents.trace entry.reference frame.operations =
        some ⟨frame.pureBody.state.reference,childEvents,entry.frame.length⟩ ∧
      Qleisli.RawFiniteRows.BoundedEvents frame.interval.before.quantum.frame.length parentEvents
        frame.interval.after.quantum.frame.length ∧
      Qleisli.RuntimeCallHistory.PureAction dependencies frame.interval.before.quantum.reference entry.reference
        frame.interval.after.quantum.reference frame.pureBody.state.reference spectators parentEvents childEvents := by
  have partition := selected_spectator_partition _ call.frame.interval.history.1 _ _ call.frame.atEntry
    (checked_call_input_unique call)
  obtain ⟨entry,parentEvents,childEvents,entryRead,parentRead,childRead,_,_,bounds,action⟩ :=
    Qleisli.RuntimeCallHistory.pure_interval_events call.frame _ partition
  exact ⟨entry,parentEvents,childEvents,entryRead,parentRead,childRead,bounds,action⟩

#print axioms checked_call_literal_action

private theorem fragment_observing_trace {program : Semantics.Raw.Program}
    {entry : Semantics.RawTrace.Interface} {result : Semantics.RawTrace.Prepared}
    (input : entry = Semantics.RawTrace.initial program.inputs)
    (trace : RuntimeLocalEvents.trace entry program.operations = some result) :
    Semantics.Observation.read (Semantics.Ownership.pureProgram program) =
      some ⟨(Semantics.RawTrace.finish program result).state,
        (Semantics.RawTrace.finish program result).events.map Semantics.Observation.Event.pure,
        entry.frame.length⟩ := by
  have read := Qleisli.RuntimeAdjacentSlices.readOps_pure 64 _ _ _ trace
  rw [input] at read ⊢
  unfold Semantics.Observation.read Semantics.Ownership.pureProgram
  simp only [read,bind,Option.bind,pure,Semantics.RawTrace.finish,List.map_append,List.map_cons,List.map_nil]

/-- Reconstruct the exact local coefficient of the original child trace at
the same physical row, with the recorded return order and reference column. -/
theorem checked_sector_literal_action
    {tokens dependencies program block callee lookup names calls start count inputs outputs}
    {call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs} (sectors : RuntimeAccessInterval.Sectors call)
    {entry : Raw.State} {childEvents : List Semantics.Raw.Event}
    (entryRead : entry.reference = ⟨call.frame.selected,call.frame.selected.flatMap (·.wires)⟩)
    (childTrace : RuntimeLocalEvents.trace entry.reference call.frame.operations =
      some ⟨call.frame.pureBody.state.reference,childEvents,entry.frame.length⟩)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (rowBound : row < 2^call.frame.pureBody.state.frame.length)
    (matrixBound : Qleisli.RuntimeCallHistory.project call.frame.pureBody.state.reference
      (call.frame.returned.flatMap (·.wires)) row < sectors.actual.rows) :
    Qleisli.Semantics.RawAction.events dependencies childEvents (fun col => joint col reference) row =
      Qleisli.Semantics.Exact.action sectors.actual joint
        (Qleisli.RuntimeCallHistory.project call.frame.pureBody.state.reference
          (call.frame.returned.flatMap (·.wires)) row) reference := by
  obtain ⟨whole,wholeRead,action⟩ := Qleisli.RuntimeCallHistory.fragment_prefix_action
    call.frame.toLiteral entryRead childTrace (fun col => joint col reference) row rowBound
  let fragment := RuntimePureInterval.fragment call.frame.selected call.frame.operations outputs
  let trace : Semantics.RawTrace.Prepared := ⟨call.frame.pureBody.state.reference,childEvents,entry.frame.length⟩
  have opened : entry.reference = Semantics.RawTrace.initial fragment.inputs := entryRead
  have observed := fragment_observing_trace opened childTrace
  have finished : Semantics.RawTrace.finish fragment trace = whole := by
    apply Option.some.inj
    rw [← wholeRead]
    symm
    change (do
      let result ← RuntimeLocalEvents.trace (Semantics.RawTrace.initial fragment.inputs) fragment.operations
      pure (Semantics.RawTrace.finish fragment result)) = _
    rw [← opened]
    change (do
      let result ← RuntimeLocalEvents.trace entry.reference call.frame.operations
      pure (Semantics.RawTrace.finish fragment result)) = _
    rw [childTrace]
    rfl
  change Semantics.Observation.read call.fragment = some ⟨(Semantics.RawTrace.finish fragment trace).state,
    (Semantics.RawTrace.finish fragment trace).events.map Semantics.Observation.Event.pure,entry.frame.length⟩ at observed
  rw [finished] at observed
  exact action.symm.trans (checked_sector_action sectors _ observed whole.events rfl joint ⟨_,matrixBound⟩ reference).symm

#print axioms checked_sector_literal_action

section LiteralPromotion
open Semantics.Finite (gather scatter)
open Qleisli.RuntimeForestProduct (gather_bound)
open Qleisli.RuntimeCallTraceFrames (WireOrder native_wires)
open Qleisli.RuntimeCallHistory (project)
open Qleisli.Semantics.Exact (action)
open Qleisli.Semantics.RawAction (events)

private theorem gather_scatter_disjoint (row value : Nat) (axes spectators : List Nat)
    (outside : ∀ axis ∈ spectators, axis ∉ axes) :
    gather (scatter row axes value) spectators = gather row spectators :=
  gather_same_on spectators _ _ (fun axis present => RuntimeScatterTransport.scatter_outside _ _ _ _ (outside axis present))

/-- A single pair of ordered coordinates gives the finite input for the
parent action, including when one of the coordinate lists is empty. -/
private theorem combine_coordinates {parent child spectators : List Nat}
    (partition : parent.Perm (child++spectators)) (distinct : parent.Nodup) :
    let axes := child.map parent.idxOf
    let rest := spectators.map parent.idxOf
    let combine := fun low high => scatter (scatter 0 rest high) axes low
    ∀ low high, low < 2^axes.length → high < 2^rest.length →
      combine low high < 2^parent.length ∧ gather (combine low high) axes = low ∧
      gather (combine low high) rest = high := by
  intro axes rest combine low high localBound highBound
  have permutation : (axes ++ rest).Perm (List.range parent.length) :=
    Qleisli.RuntimeCallTraceProjection.split_axes partition distinct
  have unique := (List.nodup_append.mp (permutation.symm.nodup List.nodup_range))
  have inside : ∀ axis ∈ axes ++ rest, axis < parent.length := fun axis present =>
    List.mem_range.mp (permutation.subset present)
  have zero : 0 < 2^parent.length := Nat.two_pow_pos _
  have highPhysical := Qleisli.Finite.Pull.scatter_bound 0 parent.length high rest zero
    (fun axis present => inside axis (List.mem_append_right _ present))
  refine ⟨Qleisli.Finite.Pull.scatter_bound _ _ _ _ highPhysical
    (fun axis present => inside axis (List.mem_append_left _ present)),
    Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ unique.1 localBound,?_⟩
  change gather (scatter (scatter 0 rest high) axes low) rest = high
  rw [gather_scatter_disjoint _ _ _ _ (fun axis inRest inAxes => unique.2.2 axis inAxes axis inRest rfl)]
  exact Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ unique.2.1 highBound

private theorem checked_child_frame
    {tokens dependencies program block callee lookup names calls start count inputs outputs}
    (call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs) {entry : Raw.State} {childEvents : List Semantics.Raw.Event}
    (entryRead : entry.reference = ⟨call.frame.selected,WireOrder call.frame.selected⟩)
    (childTrace : RuntimeLocalEvents.trace entry.reference call.frame.operations =
      some ⟨call.frame.pureBody.state.reference,childEvents,entry.frame.length⟩) :
    call.frame.pureBody.state.frame = WireOrder call.frame.selected := by
  have kept := pure_fold_frame_prefix call.frame.operations childTrace
  have entryFrame := congrArg Semantics.RawTrace.Interface.frame entryRead
  change entry.frame = WireOrder call.frame.selected at entryFrame
  change entry.frame <+: call.frame.pureBody.state.frame at kept
  rw [entryFrame] at kept
  have ⟨ports,valid⟩ := Qleisli.RuntimeCallHistory.fragment_return_ports call.frame
  have wireOrder : WireOrder call.frame.returned = WireOrder call.frame.selected := by
    simp only [List.flatMap_def,call.inputAxes,call.outputAxes]
  have widths := ((ports.flatMap_right Semantics.Raw.Port.wires).trans (native_wires _ valid)).length_eq
  change (WireOrder call.frame.returned).length = _ at widths
  rw [wireOrder] at widths
  exact (kept.eq_of_length widths).symm

/-- In the original caller frame, each column of the checked promotion is
the exact action of the actual Raw interval on that column. -/
theorem checked_call_promoted_action
    {tokens dependencies program block callee lookup names calls start count inputs outputs}
    (call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs) (sectors : RuntimeAccessInterval.Sectors call)
    (actual : Semantics.Exact.Matrix) (work left : Nat)
    (read : (Raw.promote call.frame.interval.before.quantum.frame.length
      (RuntimeForestCode.portAxes call.frame.interval.before.quantum.frame call.frame.selected)
      sectors.actual).run work = (.ok actual,left)) :
    ∃ parentEvents,
      RuntimeLocalEvents.trace call.frame.interval.before.quantum.reference call.frame.operations =
        some ⟨call.frame.interval.after.quantum.reference,parentEvents,call.frame.interval.before.quantum.frame.length⟩ ∧
      ∀ (Reference : Type) (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
        row < actual.rows →
        events dependencies parentEvents (fun col => joint col reference) row = action actual joint row reference := by
  obtain ⟨entry,parentEvents,childEvents,entryRead,parentRead,childRead,bounded,locality⟩ := checked_call_literal_action call
  refine ⟨parentEvents,parentRead,?_⟩
  intro Reference joint row reference rowBound
  let parent := call.frame.interval.before.quantum.frame
  let chosen := WireOrder call.frame.selected
  let spectators := PureInterval.spectators call.frame.interval.before inputs
  let axes := chosen.map parent.idxOf
  let rest := (WireOrder spectators).map parent.idxOf
  let combine := fun low high => scatter (scatter 0 rest high) axes low
  have parentDistinct := (Raw.Ownership.valid _ call.frame.interval.history.1).frame
  change parent.Nodup at parentDistinct
  have parentPorts := selected_spectator_partition _ call.frame.interval.history.1 _ _ call.frame.atEntry
    (checked_call_input_unique call)
  have partition : parent.Perm (chosen ++ WireOrder spectators) := by
    simpa only [parent,chosen,spectators,List.flatMap_append] using
      (native_wires _ call.frame.interval.history.1).symm.trans (parentPorts.flatMap_right Semantics.Raw.Port.wires)
  have both := Qleisli.RuntimeCallTraceProjection.split_axes partition parentDistinct
  have unique := List.nodup_append.mp (both.symm.nodup List.nodup_range)
  have geometry := Qleisli.Raw.promote_denotes _ _ _ _ work left read
  have inParent : row < 2^parent.length := geometry.1 ▸ rowBound
  have frame := checked_call_frame call
  have childFrame := checked_child_frame call entryRead childRead
  have entryFrame := congrArg Semantics.RawTrace.Interface.frame entryRead
  have sameInput (input : Nat) (inside : input < 2^parent.length) :
      joint input reference = joint (combine (gather input axes) (gather input rest)) reference := by
    have data := combine_coordinates partition parentDistinct (gather input axes) (gather input rest)
      (gather_bound _ _) (gather_bound _ _)
    exact congrArg (fun index => joint index reference)
      ((Qleisli.RuntimeCallTraceProjection.split_eq partition parentDistinct inside data.1).mpr
        ⟨data.2.1.symm,data.2.2.symm⟩)
  have localAction := locality (fun low high => joint (combine low high) reference) row
    (by change row < 2^call.frame.interval.after.quantum.frame.length; rwa [frame])
  change entry.frame = chosen at entryFrame
  change events dependencies parentEvents (fun col => joint (combine (gather col (entry.frame.map parent.idxOf))
    (gather col rest)) reference) row =
    events dependencies childEvents
      (fun col => joint (combine col (gather row ((WireOrder spectators).map call.frame.interval.after.quantum.frame.idxOf))) reference)
      (gather row (call.frame.pureBody.state.frame.map call.frame.interval.after.quantum.frame.idxOf)) at localAction
  rw [entryFrame,frame,childFrame] at localAction
  have traceAction := (bounded.congr dependencies _ _ sameInput row (by rw [frame]; exact inParent)).trans localAction
  have childWidth : axes.length = call.frame.pureBody.state.frame.length := by rw [childFrame,List.length_map]
  have returnOrder : WireOrder call.frame.returned = chosen := by
    simp only [chosen,List.flatMap_def,call.inputAxes,call.outputAxes]
  have returnCoord : project call.frame.pureBody.state.reference (WireOrder call.frame.returned) (gather row axes) =
      gather row axes := by
    have chosenUnique : chosen.Nodup := (List.nodup_append.mp (parentDistinct.perm partition)).1
    change gather (gather row axes) ((WireOrder call.frame.returned).map call.frame.pureBody.state.frame.idxOf) = _
    rw [returnOrder,childFrame,RuntimeNamedCallerAction.self_indices _ chosenUnique,
      Qleisli.RuntimeNamedCallerAction.gather_range]
    exact Nat.mod_eq_of_lt (by simpa only [axes,List.length_map] using gather_bound row axes)
  obtain ⟨_,middle,guarded,_⟩ := Finite.bind_success _ _ _ _ _ read
  have shape := (Finite.guard_success _ _ _ middle guarded).1
  simp only [Bool.and_eq_true,beq_iff_eq] at shape
  have child := checked_sector_literal_action sectors entryRead childRead
    (fun col ref => joint (combine col (gather row rest)) ref) (gather row axes) reference
    (by rw [← childWidth]; exact gather_bound _ _) (by rw [returnCoord,shape.1.2]; exact gather_bound _ _)
  rw [returnCoord] at child
  have promoted := Qleisli.Raw.ReconstructedAction.promoted_action work left read joint row reference rowBound
  rw [traceAction,child,promoted]
  unfold action
  apply Qleisli.Exact.sum_map_congr
  intro col member
  have colBound : col < 2^axes.length := (shape.2.trans shape.1.2) ▸ List.mem_range.mp member
  have data := combine_coordinates partition parentDistinct col (gather row rest) colBound (gather_bound _ _)
  have scattered : scatter row axes col < 2^parent.length := Qleisli.Finite.Pull.scatter_bound _ _ _ _ inParent
    (fun axis member => List.mem_range.mp (both.subset (List.mem_append_left _ member)))
  have same := (Qleisli.RuntimeCallTraceProjection.split_eq partition parentDistinct data.1 scattered).mpr
    ⟨data.2.1.trans (Qleisli.RuntimeFiniteTargetScatter.gather_scatter _ _ _ unique.1 colBound).symm,
      data.2.2.trans (gather_scatter_disjoint _ _ _ _ (fun axis inRest inAxes => unique.2.2 axis inAxes axis inRest rfl)).symm⟩
  change combine col (gather row rest) = scatter row axes col at same
  change Semantics.Exact.entry sectors.actual (gather row axes) col * joint (combine col (gather row rest)) reference =
    Semantics.Exact.entry sectors.actual (gather row axes) col * joint (scatter row axes col) reference
  rw [same]

#print axioms checked_call_promoted_action

/-- The ordered action of the two original call traces equals the ordered
composition of their promotions on every finite row and reference column. -/
theorem checked_pair_promoted_action
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs)
    {firstRequest secondRequest} (pair : RuntimeAccessCallee.Pair second firstRequest secondRequest)
    (firstMap secondMap : Semantics.Exact.Matrix) (a b c d : Nat)
    (firstRead : (Raw.promote first.call.interval.frame.interval.before.quantum.frame.length
      (callerAxes (call := first.call.interval)) pair.firstSectors.actual).run a = (.ok firstMap,b))
    (secondRead : (Raw.promote second.call.frame.interval.before.quantum.frame.length
      (callerAxes (call := second.call)) pair.secondSectors.actual).run c = (.ok secondMap,d)) :
    ∃ firstEvents secondEvents,
      RuntimeLocalEvents.trace first.call.interval.frame.interval.before.quantum.reference first.call.interval.frame.operations =
        some ⟨first.call.interval.frame.interval.after.quantum.reference,firstEvents,
          first.call.interval.frame.interval.before.quantum.frame.length⟩ ∧
      RuntimeLocalEvents.trace second.call.frame.interval.before.quantum.reference second.call.frame.operations =
        some ⟨second.call.frame.interval.after.quantum.reference,secondEvents,
          second.call.frame.interval.before.quantum.frame.length⟩ ∧
      ∀ (Reference : Type) (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
        row < secondMap.rows →
        events root.dependencies (firstEvents ++ secondEvents) (fun col => joint col reference) row =
          action secondMap (action firstMap joint) row reference := by
  obtain ⟨firstEvents,firstTrace,firstAction⟩ :=
    checked_call_promoted_action first.call.interval pair.firstSectors firstMap a b firstRead
  obtain ⟨secondEvents,secondTrace,secondAction⟩ :=
    checked_call_promoted_action second.call pair.secondSectors secondMap c d secondRead
  obtain ⟨entry,parentEvents,childEvents,entryRead,parentRead,childRead,bounded,locality⟩ :=
    checked_call_literal_action second.call
  have same := congrArg Semantics.RawTrace.Prepared.events (Option.some.inj (parentRead.symm.trans secondTrace))
  change parentEvents = secondEvents at same
  subst parentEvents
  refine ⟨firstEvents,secondEvents,firstTrace,secondTrace,?_⟩
  intro Reference joint row reference rowBound
  have firstRows := (Qleisli.Raw.promote_denotes _ _ _ _ a b firstRead).1
  have secondRows := (Qleisli.Raw.promote_denotes _ _ _ _ c d secondRead).1
  have sameFrame := checked_pair_frame second
  have after := checked_call_frame second.call
  have sameInput (col : Nat) (within : col < 2^second.call.frame.interval.before.quantum.frame.length) :
      events root.dependencies firstEvents (fun input => joint input reference) col =
        action firstMap joint col reference := by
    apply firstAction
    rwa [firstRows,sameFrame]
  have outputBound : row < 2^second.call.frame.interval.after.quantum.frame.length := by
    rwa [after,← secondRows]
  simp only [events,List.foldl_append]
  exact (bounded.congr root.dependencies _ _ sameInput row outputBound).trans
    (secondAction Reference (action firstMap joint) row reference rowBound)

#print axioms checked_pair_promoted_action

end LiteralPromotion

section Exchange
open Semantics.Finite (bit gather)
open Qleisli.RuntimeForestProduct (gather_bound)
open Qleisli.Semantics.Exact (entry action)
open scoped BigOperators Matrix

private def coordinate (axes : List Nat) (label : Nat) : Fin (2^axes.length) :=
  ⟨gather label axes,gather_bound label axes⟩

private theorem coordinate_eq_iff (axes : List Nat) (a b : Nat) :
    coordinate axes a = coordinate axes b ↔ ∀ axis ∈ axes, bit a axis = bit b axis := by
  constructor
  · intro same axis present
    obtain ⟨index,bound,rfl⟩ := List.getElem_of_mem present
    have digits := congrArg (fun x : Fin (2^axes.length) => bit x.val index) same
    change bit (gather a axes) index = bit (gather b axes) index at digits
    simpa only [RuntimeScatterTransport.gather_at _ _ _ bound] using digits
  · intro same
    exact Fin.ext (gather_same_on axes a b same)

private theorem bit_outside_width {label bits axis : Nat} (inside : label < 2^bits)
    (outside : bits ≤ axis) : bit label axis = 0 := by
  have power : 2^bits ≤ 2^axis := Nat.pow_le_pow_right (by decide) outside
  simp [bit,Nat.div_eq_of_lt (inside.trans_le power)]

private noncomputable def sectorRoute {bits : Nat} {shared first second rest : List Nat}
    (partition : (shared ++ first ++ second ++ rest).Perm (List.range bits)) :
    Fin (2^bits) ≃ Fin (2^shared.length) × (Fin (2^first.length) × (Fin (2^second.length) × Fin (2^rest.length))) := by
  let route := fun label : Fin (2^bits) =>
    (coordinate shared label.val,coordinate first label.val,coordinate second label.val,coordinate rest label.val)
  apply Equiv.ofBijective route
  apply (Fintype.bijective_iff_injective_and_card route).mpr
  constructor
  · intro a b same
    apply Fin.ext
    apply labels_equal_of_bits
    intro axis
    by_cases inside : axis < bits
    · have present := partition.symm.subset (List.mem_range.mpr inside)
      simp only [List.mem_append] at present
      obtain ((onShared | onFirst) | onSecond) | onRest := present
      · exact (coordinate_eq_iff _ _ _).mp (congrArg Prod.fst same) axis onShared
      · exact (coordinate_eq_iff _ _ _).mp (congrArg (fun p => p.2.1) same) axis onFirst
      · exact (coordinate_eq_iff _ _ _).mp (congrArg (fun p => p.2.2.1) same) axis onSecond
      · exact (coordinate_eq_iff _ _ _).mp (congrArg (fun p => p.2.2.2) same) axis onRest
    · exact (bit_outside_width a.isLt (Nat.le_of_not_gt inside)).trans
        (bit_outside_width b.isLt (Nat.le_of_not_gt inside)).symm
  · have length := partition.length_eq
    simp only [List.length_append,List.length_range] at length
    rw [← length]
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.pow_add,Nat.mul_assoc]

private theorem sectorRoute_read {bits : Nat} {shared first second rest : List Nat}
    (partition : (shared ++ first ++ second ++ rest).Perm (List.range bits))
    (label : Fin (2^bits)) : sectorRoute partition label =
      (coordinate shared label.val,coordinate first label.val,coordinate second label.val,coordinate rest label.val) := rfl

private theorem promotion_exchange {bits : Nat} {firstAxes secondAxes : List Nat}
    {localFirst localSecond first second : Semantics.Exact.Matrix} {a b c d : Nat}
    (firstRead : (Raw.promote bits firstAxes localFirst).run a = (.ok first,b))
    (secondRead : (Raw.promote bits secondAxes localSecond).run c = (.ok second,d))
    (firstPreserves : ∀ (row : Fin first.rows) (col : Fin first.cols), entry first row.val col.val ≠ 0 →
      ∀ axis ∈ secondAxes, bit row.val axis = bit col.val axis)
    (secondPreserves : ∀ (row : Fin second.rows) (col : Fin second.cols), entry second row.val col.val ≠ 0 →
      ∀ axis ∈ firstAxes, bit row.val axis = bit col.val axis)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Fin (2^bits)) (reference : Reference) :
    action second (action first joint) row.val reference = action first (action second joint) row.val reference := by
  let onFirst := (List.range bits).filter (fun axis => firstAxes.contains axis)
  let offFirst := (List.range bits).filter (fun axis => !firstAxes.contains axis)
  let shared := onFirst.filter (fun axis => secondAxes.contains axis)
  let firstOnly := onFirst.filter (fun axis => !secondAxes.contains axis)
  let secondOnly := offFirst.filter (fun axis => secondAxes.contains axis)
  let spectators := offFirst.filter (fun axis => !secondAxes.contains axis)
  have order : (shared ++ firstOnly ++ secondOnly ++ spectators).Perm (List.range bits) := by
    simpa only [commonOrder,List.partition_eq_filter_filter,shared,firstOnly,secondOnly,spectators,onFirst,offFirst]
      using commonOrder_perm bits firstAxes secondAxes
  let route := sectorRoute order
  have fShape := Qleisli.Raw.promote_denotes _ _ _ _ a b firstRead
  have sShape := Qleisli.Raw.promote_denotes _ _ _ _ c d secondRead
  let firstMatrix : Matrix (Fin (2^bits)) (Fin (2^bits)) ℂ := fun r k => entry first r.val k.val
  let secondMatrix : Matrix (Fin (2^bits)) (Fin (2^bits)) ℂ := fun r k => entry second r.val k.val
  have firstBound : ∀ axis ∈ firstAxes, axis < bits := by
    obtain ⟨_,middle,guarded,_⟩ := Finite.bind_success _ _ _ _ _ firstRead
    have shape := (Finite.guard_success _ _ _ middle guarded).1
    simp only [Bool.and_eq_true,Finite.axesValid,List.all_eq_true,decide_eq_true_eq] at shape
    exact shape.1.1.2.1.2
  have secondBound : ∀ axis ∈ secondAxes, axis < bits := by
    obtain ⟨_,middle,guarded,_⟩ := Finite.bind_success _ _ _ _ _ secondRead
    have shape := (Finite.guard_success _ _ _ middle guarded).1
    simp only [Bool.and_eq_true,Finite.axesValid,List.all_eq_true,decide_eq_true_eq] at shape
    exact shape.1.1.2.1.2
  have sharedMem (axis : Nat) : axis ∈ shared ↔ axis ∈ firstAxes ∧ axis ∈ secondAxes := by
    simp only [shared,onFirst,List.mem_filter,List.mem_range,List.contains_iff_mem]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨firstBound axis h.1,h.1⟩,h.2⟩⟩
  have absent (axes : List Nat) (axis : Nat) : axes.contains axis = false ↔ axis ∉ axes := by
    rw [← Bool.not_eq_true,List.contains_iff_mem]
  have firstMem (axis : Nat) : axis ∈ firstOnly ↔ axis ∈ firstAxes ∧ axis ∉ secondAxes := by
    simp only [firstOnly,onFirst,List.mem_filter,List.mem_range,Bool.not_eq_true',List.contains_iff_mem,absent]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨firstBound axis h.1,h.1⟩,h.2⟩⟩
  have secondMem (axis : Nat) : axis ∈ secondOnly ↔ axis ∉ firstAxes ∧ axis ∈ secondAxes := by
    simp only [secondOnly,offFirst,List.mem_filter,List.mem_range,Bool.not_eq_true',List.contains_iff_mem,absent]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨secondBound axis h.2,h.1⟩,h.2⟩⟩
  have restMem (axis : Nat) : axis ∈ spectators ↔ axis < bits ∧ axis ∉ firstAxes ∧ axis ∉ secondAxes := by
    simp only [spectators,offFirst,List.mem_filter,List.mem_range,Bool.not_eq_true',absent,and_assoc]
  have bitsIn {x y : Fin (2^bits)} (axes : List Nat) (same : coordinate axes x.val = coordinate axes y.val) :
      ∀ axis ∈ axes, bit x.val axis = bit y.val axis := (coordinate_eq_iff _ _ _).mp same
  have bitsOut {x y : Fin (2^bits)} (axis : Nat) (outside : ¬axis < bits) : bit x.val axis = bit y.val axis :=
    (bit_outside_width x.isLt (Nat.le_of_not_gt outside)).trans
      (bit_outside_width y.isLt (Nat.le_of_not_gt outside)).symm
  have routeRead (p : Fin (2^shared.length) × (Fin (2^firstOnly.length) × (Fin (2^secondOnly.length) × Fin (2^spectators.length)))) :
      (coordinate shared (route.symm p).val,coordinate firstOnly (route.symm p).val,
        coordinate secondOnly (route.symm p).val,coordinate spectators (route.symm p).val) = p := by
    exact (sectorRoute_read order _).symm.trans (route.apply_symm_apply p)
  have commute := Qleisli.RoutedControlCommutation.sector_fibre_exchange route firstMatrix secondMatrix 0 0 0
    (by
      intro s f t r s' f' t' r' nonzero
      let x := route.symm (s,f,t,r)
      let y := route.symm (s',f',t',r')
      let rx : Fin first.rows := ⟨x.val,fShape.1.symm ▸ x.isLt⟩
      let cy : Fin first.cols := ⟨y.val,fShape.2.1.symm ▸ y.isLt⟩
      have on := firstPreserves rx cy nonzero
      have off : ∀ axis ∉ firstAxes, bit x.val axis = bit y.val axis := by
        by_contra different
        exact nonzero ((promotion_entry_on_fibre _ _ _ _ a b firstRead rx cy).trans (if_neg different))
      have xRead := routeRead (s,f,t,r)
      have yRead := routeRead (s',f',t',r')
      refine ⟨?_,?_,?_⟩
      · exact (congrArg Prod.fst xRead).symm.trans (((coordinate_eq_iff _ _ _).mpr
          (fun axis present => on axis ((sharedMem axis).mp present).2)).trans (congrArg Prod.fst yRead))
      · exact (congrArg (fun p => p.2.2.1) xRead).symm.trans (((coordinate_eq_iff _ _ _).mpr
          (fun axis present => off axis ((secondMem axis).mp present).1)).trans (congrArg (fun p => p.2.2.1) yRead))
      · exact (congrArg (fun p => p.2.2.2) xRead).symm.trans (((coordinate_eq_iff _ _ _).mpr
          (fun axis present => off axis ((restMem axis).mp present).2.1)).trans (congrArg (fun p => p.2.2.2) yRead)))
    (by
      intro s f t r s' f' t' r' nonzero
      let x := route.symm (s,f,t,r)
      let y := route.symm (s',f',t',r')
      let rx : Fin second.rows := ⟨x.val,sShape.1.symm ▸ x.isLt⟩
      let cy : Fin second.cols := ⟨y.val,sShape.2.1.symm ▸ y.isLt⟩
      have on := secondPreserves rx cy nonzero
      have off : ∀ axis ∉ secondAxes, bit x.val axis = bit y.val axis := by
        by_contra different
        exact nonzero ((promotion_entry_on_fibre _ _ _ _ c d secondRead rx cy).trans (if_neg different))
      have xRead := routeRead (s,f,t,r)
      have yRead := routeRead (s',f',t',r')
      refine ⟨?_,?_,?_⟩
      · exact (congrArg Prod.fst xRead).symm.trans (((coordinate_eq_iff _ _ _).mpr
          (fun axis present => on axis ((sharedMem axis).mp present).1)).trans (congrArg Prod.fst yRead))
      · exact (congrArg (fun p => p.2.1) xRead).symm.trans (((coordinate_eq_iff _ _ _).mpr
          (fun axis present => off axis ((firstMem axis).mp present).2)).trans (congrArg (fun p => p.2.1) yRead))
      · exact (congrArg (fun p => p.2.2.2) xRead).symm.trans (((coordinate_eq_iff _ _ _).mpr
          (fun axis present => off axis ((restMem axis).mp present).2.2)).trans (congrArg (fun p => p.2.2.2) yRead)))
    (by
      intro s f f' t r
      let x := route.symm (s,f,t,r)
      let y := route.symm (s,f',t,r)
      let x' := route.symm (s,f,0,0)
      let y' := route.symm (s,f',0,0)
      have selected {u v : Fin (2^bits)} (sharedEq : coordinate shared u.val = coordinate shared v.val)
          (targetEq : coordinate firstOnly u.val = coordinate firstOnly v.val) :
          ∀ axis ∈ firstAxes, bit u.val axis = bit v.val axis := by
        intro axis first
        by_cases second : axis ∈ secondAxes
        · exact bitsIn _ sharedEq axis ((sharedMem axis).mpr ⟨first,second⟩)
        · exact bitsIn _ targetEq axis ((firstMem axis).mpr ⟨first,second⟩)
      have other {u v : Fin (2^bits)} (targetEq : coordinate secondOnly u.val = coordinate secondOnly v.val)
          (restEq : coordinate spectators u.val = coordinate spectators v.val) :
          ∀ axis ∉ firstAxes, bit u.val axis = bit v.val axis := by
        intro axis first
        by_cases second : axis ∈ secondAxes
        · exact bitsIn _ targetEq axis ((secondMem axis).mpr ⟨first,second⟩)
        · by_cases inside : axis < bits
          · exact bitsIn _ restEq axis ((restMem axis).mpr ⟨inside,first,second⟩)
          · exact bitsOut axis inside
      have xr := routeRead (s,f,t,r)
      have yr := routeRead (s,f',t,r)
      have xr' := routeRead (s,f,0,0)
      have yr' := routeRead (s,f',0,0)
      exact promotion_fibre_independence _ _ _ _ a b firstRead
        ⟨x.val,fShape.1.symm ▸ x.isLt⟩ ⟨x'.val,fShape.1.symm ▸ x'.isLt⟩
        ⟨y.val,fShape.2.1.symm ▸ y.isLt⟩ ⟨y'.val,fShape.2.1.symm ▸ y'.isLt⟩
        (selected ((congrArg Prod.fst xr).trans (congrArg Prod.fst xr').symm)
          ((congrArg (fun p => p.2.1) xr).trans (congrArg (fun p => p.2.1) xr').symm))
        (selected ((congrArg Prod.fst yr).trans (congrArg Prod.fst yr').symm)
          ((congrArg (fun p => p.2.1) yr).trans (congrArg (fun p => p.2.1) yr').symm))
        (other ((congrArg (fun p => p.2.2.1) xr).trans (congrArg (fun p => p.2.2.1) yr).symm)
          ((congrArg (fun p => p.2.2.2) xr).trans (congrArg (fun p => p.2.2.2) yr).symm))
        (other ((congrArg (fun p => p.2.2.1) xr').trans (congrArg (fun p => p.2.2.1) yr').symm)
          ((congrArg (fun p => p.2.2.2) xr').trans (congrArg (fun p => p.2.2.2) yr').symm)))
    (by
      intro s f t t' r
      let x := route.symm (s,f,t,r)
      let y := route.symm (s,f,t',r)
      let x' := route.symm (s,0,t,0)
      let y' := route.symm (s,0,t',0)
      have selected {u v : Fin (2^bits)} (sharedEq : coordinate shared u.val = coordinate shared v.val)
          (targetEq : coordinate secondOnly u.val = coordinate secondOnly v.val) :
          ∀ axis ∈ secondAxes, bit u.val axis = bit v.val axis := by
        intro axis second
        by_cases first : axis ∈ firstAxes
        · exact bitsIn _ sharedEq axis ((sharedMem axis).mpr ⟨first,second⟩)
        · exact bitsIn _ targetEq axis ((secondMem axis).mpr ⟨first,second⟩)
      have other {u v : Fin (2^bits)} (targetEq : coordinate firstOnly u.val = coordinate firstOnly v.val)
          (restEq : coordinate spectators u.val = coordinate spectators v.val) :
          ∀ axis ∉ secondAxes, bit u.val axis = bit v.val axis := by
        intro axis second
        by_cases first : axis ∈ firstAxes
        · exact bitsIn _ targetEq axis ((firstMem axis).mpr ⟨first,second⟩)
        · by_cases inside : axis < bits
          · exact bitsIn _ restEq axis ((restMem axis).mpr ⟨inside,first,second⟩)
          · exact bitsOut axis inside
      have xr := routeRead (s,f,t,r)
      have yr := routeRead (s,f,t',r)
      have xr' := routeRead (s,0,t,0)
      have yr' := routeRead (s,0,t',0)
      exact promotion_fibre_independence _ _ _ _ c d secondRead
        ⟨x.val,sShape.1.symm ▸ x.isLt⟩ ⟨x'.val,sShape.1.symm ▸ x'.isLt⟩
        ⟨y.val,sShape.2.1.symm ▸ y.isLt⟩ ⟨y'.val,sShape.2.1.symm ▸ y'.isLt⟩
        (selected ((congrArg Prod.fst xr).trans (congrArg Prod.fst xr').symm)
          ((congrArg (fun p => p.2.2.1) xr).trans (congrArg (fun p => p.2.2.1) xr').symm))
        (selected ((congrArg Prod.fst yr).trans (congrArg Prod.fst yr').symm)
          ((congrArg (fun p => p.2.2.1) yr).trans (congrArg (fun p => p.2.2.1) yr').symm))
        (other ((congrArg (fun p => p.2.1) xr).trans (congrArg (fun p => p.2.1) yr).symm)
          ((congrArg (fun p => p.2.2.2) xr).trans (congrArg (fun p => p.2.2.2) yr).symm))
        (other ((congrArg (fun p => p.2.1) xr').trans (congrArg (fun p => p.2.1) yr').symm)
          ((congrArg (fun p => p.2.2.2) xr').trans (congrArg (fun p => p.2.2.2) yr').symm)))
    (fun label => joint label.val) row reference
  have rangeSum (n : Nat) (f : Nat → ℂ) :
      ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,ih,Finset.sum_range_succ]
  have matAction (matrix : Semantics.Exact.Matrix) (columns : matrix.cols = 2^bits)
      (input : Nat → Reference → ℂ) (output : Fin (2^bits)) :
      ((fun r k : Fin (2^bits) => entry matrix r.val k.val : Matrix (Fin (2^bits)) (Fin (2^bits)) ℂ) *ᵥ
        (fun k => input k.val reference)) output = action matrix input output.val reference := by
    unfold Matrix.mulVec dotProduct action
    rw [Fin.sum_univ_eq_sum_range (fun k => entry matrix output.val k * input k reference),columns,rangeSum]
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec] at commute
  have firstApply : firstMatrix *ᵥ (fun k => joint k.val reference) =
      fun k => action first joint k.val reference := funext (matAction first fShape.2.1 joint)
  have secondApply : secondMatrix *ᵥ (fun k => joint k.val reference) =
      fun k => action second joint k.val reference := funext (matAction second sShape.2.1 joint)
  rw [firstApply,secondApply] at commute
  exact (matAction second sShape.2.1 (action first joint) row).symm.trans
    (commute.trans (matAction first fShape.2.1 (action second joint) row))

#print axioms promotion_exchange

/-- The original checked calls admit the same ordered action after exchanging
their promoted operators. Shared control bits come from the written places. -/
theorem checked_pair_exchange
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs)
    {firstRequest secondRequest} (pair : RuntimeAccessCallee.Pair second firstRequest secondRequest)
    (firstMap secondMap : Semantics.Exact.Matrix) (a b c d : Nat)
    (firstRead : (Raw.promote first.call.interval.frame.interval.before.quantum.frame.length
      (callerAxes (call := first.call.interval)) pair.firstSectors.actual).run a = (.ok firstMap,b))
    (secondRead : (Raw.promote second.call.frame.interval.before.quantum.frame.length
      (callerAxes (call := second.call)) pair.secondSectors.actual).run c = (.ok secondMap,d)) :
    ∃ firstEvents secondEvents,
      RuntimeLocalEvents.trace first.call.interval.frame.interval.before.quantum.reference first.call.interval.frame.operations =
        some ⟨first.call.interval.frame.interval.after.quantum.reference,firstEvents,
          first.call.interval.frame.interval.before.quantum.frame.length⟩ ∧
      RuntimeLocalEvents.trace second.call.frame.interval.before.quantum.reference second.call.frame.operations =
        some ⟨second.call.frame.interval.after.quantum.reference,secondEvents,
          second.call.frame.interval.before.quantum.frame.length⟩ ∧
      ∀ (Reference : Type) (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
        row < secondMap.rows →
        Qleisli.Semantics.RawAction.events root.dependencies (firstEvents ++ secondEvents)
          (fun col => joint col reference) row = action firstMap (action secondMap joint) row reference := by
  obtain ⟨firstEvents,secondEvents,firstTrace,secondTrace,original⟩ :=
    checked_pair_promoted_action second pair firstMap secondMap a b c d firstRead secondRead
  refine ⟨firstEvents,secondEvents,firstTrace,secondTrace,?_⟩
  intro Reference joint row reference rowBound
  have sameFrame := checked_pair_frame second
  have firstOn := first_promotion_preserves_second_axes second sameFrame pair.firstSectors firstMap a b firstRead
  have secondOn := second_promotion_preserves_first_axes second pair.secondSectors secondMap c d secondRead
  have secondRows := (Qleisli.Raw.promote_denotes _ _ _ _ c d secondRead).1
  have sameWidth := congrArg List.length sameFrame
  have secondInFirst := secondRead
  rw [← sameWidth] at secondInFirst
  have bounded : row < 2^first.call.interval.frame.interval.before.quantum.frame.length := by
    rwa [sameWidth,← secondRows]
  exact (original Reference joint row reference rowBound).trans
    (promotion_exchange firstRead secondInFirst firstOn secondOn joint ⟨row,bounded⟩ reference)

#print axioms checked_pair_exchange

private theorem routing_read {dependencies program} {block : RuntimeInterval.Block dependencies program}
    {start count} (interval : RuntimeInterval.Checked block start count)
    (routes : (((block.operations.drop start).take count).all RuntimeAccessPartition.isRoute) = true) :
    Semantics.Observation.readOps 65 interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (interval.after.quantum.reference,[]) := by
  obtain ⟨operations,literal,trace,_⟩ := structural_interval interval routes
  rw [literal]
  exact Qleisli.RuntimeAdjacentSlices.readOps_pure 64 _ _ _ trace

private theorem call_read {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {events : List Semantics.Raw.Event}
    (trace : RuntimeLocalEvents.trace frame.interval.before.quantum.reference frame.operations =
      some ⟨frame.interval.after.quantum.reference,events,frame.interval.before.quantum.frame.length⟩) :
    Semantics.Observation.readOps 65 frame.interval.before.quantum.reference ((block.operations.drop start).take count) =
      some (frame.interval.after.quantum.reference,events.map Semantics.Observation.Event.pure) := by
  rw [frame.literal]
  exact Qleisli.RuntimeAdjacentSlices.readOps_pure 64 _ _ _ trace

private theorem pair_root_events
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs)
    {firstRequest secondRequest} (pair : RuntimeAccessCallee.Pair second firstRequest secondRequest)
    {firstEvents secondEvents : List Semantics.Raw.Event}
    (firstTrace : RuntimeLocalEvents.trace first.call.interval.frame.interval.before.quantum.reference
      first.call.interval.frame.operations = some ⟨first.call.interval.frame.interval.after.quantum.reference,firstEvents,
        first.call.interval.frame.interval.before.quantum.frame.length⟩)
    (secondTrace : RuntimeLocalEvents.trace second.call.frame.interval.before.quantum.reference
      second.call.frame.operations = some ⟨second.call.frame.interval.after.quantum.reference,secondEvents,
        second.call.frame.interval.before.quantum.frame.length⟩) :
    let exit := second.owners.routing.after.quantum.reference
    block.whole.prepared.state = exit ∧
    block.whole.prepared.events = (firstEvents ++ secondEvents).map Semantics.Observation.Event.pure ++
      [.pure (.reorder exit.frame.length (Semantics.RawTrace.axes exit
        (root.program.outputs.flatMap fun token => ((exit.live.find? (fun port => port.token == token)).map (·.wires)).getD [])))] := by
  intro exit
  let ops := root.program.operations
  let firstCountRoutes := RuntimeAccessPartition.routingCount first.call.interval.places
  let lastCountRoutes := RuntimeAccessPartition.routingCount second.call.places
  let mid := first.nextOffset
  have middle : mid = firstStart+firstCount+firstCountRoutes := rfl
  have finish := pair.finalOffset
  change start+count+lastCountRoutes = ops.length at finish
  have join : mid + (start-mid) = start := Nat.add_sub_of_le second.owners.bounded
  have split : ops = ((((ops.take firstStart ++ (ops.drop firstStart).take firstCount) ++
      (ops.drop (firstStart+firstCount)).take firstCountRoutes) ++ (ops.drop mid).take (start-mid)) ++
      (ops.drop start).take count) ++ (ops.drop (start+count)).take lastCountRoutes := by
    simp only [← Qleisli.RuntimeAdjacentSlices.prefixSplit,← middle,join,finish,List.take_length]
  have firstRoutes := RuntimeAccessPartition.replay_routes first.owners.replayed
  have secondRoutes := RuntimeAccessPartition.replay_routes second.owners.replayed
  have takeFirst := routing_read first.owners.preamble firstRoutes.1
  have putFirst := routing_read first.owners.routing firstRoutes.2
  have takeSecond := routing_read second.owners.preamble secondRoutes.1
  have putSecond := routing_read second.owners.routing secondRoutes.2
  have executeFirst := call_read first.call.interval.frame firstTrace
  have executeSecond := call_read second.call.frame secondTrace
  have ⟨beginFirst,endFirst,between,beginSecond,endSecond⟩ := checked_pair_boundaries second
  have opened : first.owners.preamble.before = block.entry := by
    obtain ⟨work,left,read⟩ := first.owners.preamble.prefixRead
    change (Raw.Observation.checkOps root.dependencies 65 block.entry []).run work =
      (.ok first.owners.preamble.before,left) at read
    obtain ⟨_,_,folded,rest⟩ := Finite.bind_success _ _ _ _ _ read
    obtain ⟨_,_,_,done_⟩ := Finite.bind_success _ _ _ _ _ rest
    exact (Finite.pure_success _ _ _ _ done_).1.trans (Finite.pure_success _ _ _ _ folded).1
  have initial := (RuntimeNamedFrameAxes.initialized block.inputRead).1
  rw [opened,initial,beginFirst] at takeFirst
  rw [← endFirst,between] at putFirst
  rw [beginSecond] at takeSecond
  rw [← endSecond] at putSecond
  change Semantics.Observation.readOps 65 (Semantics.RawTrace.initial root.program.inputs) (ops.take firstStart) =
    some (first.call.interval.frame.interval.before.quantum.reference,[]) at takeFirst
  change Semantics.Observation.readOps 65 first.call.interval.frame.interval.after.quantum.reference
    ((ops.drop (firstStart+firstCount)).take firstCountRoutes) = some (second.owners.preamble.before.quantum.reference,[]) at putFirst
  change Semantics.Observation.readOps 65 second.owners.preamble.before.quantum.reference
    ((ops.drop mid).take (start-mid)) = some (second.call.frame.interval.before.quantum.reference,[]) at takeSecond
  change Semantics.Observation.readOps 65 second.call.frame.interval.after.quantum.reference
    ((ops.drop (start+count)).take lastCountRoutes) = some (exit,[]) at putSecond
  change Semantics.Observation.readOps 65 first.call.interval.frame.interval.before.quantum.reference
    ((ops.drop firstStart).take firstCount) =
      some (first.call.interval.frame.interval.after.quantum.reference,
        firstEvents.map Semantics.Observation.Event.pure) at executeFirst
  change Semantics.Observation.readOps 65 second.call.frame.interval.before.quantum.reference
    ((ops.drop start).take count) = some (second.call.frame.interval.after.quantum.reference,
      secondEvents.map Semantics.Observation.Event.pure) at executeSecond
  have appendRead (initial middle final : Semantics.RawTrace.Interface)
      (left right : List Semantics.Observation.Op) (before after : List Semantics.Observation.Event)
      (first : Semantics.Observation.readOps 65 initial left = some (middle,before))
      (second : Semantics.Observation.readOps 65 middle right = some (final,after)) :
      Semantics.Observation.readOps 65 initial (left ++ right) = some (final,before ++ after) := by
    rw [Qleisli.RuntimeAdjacentSlices.readOps_append 64,first]
    change (do let result ← Semantics.Observation.readOps 65 middle right
               pure (result.1,before ++ result.2)) = _
    rw [second]
    rfl
  have bodyRead : Semantics.Observation.readOps 65 (Semantics.RawTrace.initial root.program.inputs) ops =
      some (exit,(firstEvents ++ secondEvents).map Semantics.Observation.Event.pure) := by
    have read := appendRead _ _ _ _ _ _ _ (appendRead _ _ _ _ _ _ _
      (appendRead _ _ _ _ _ _ _ (appendRead _ _ _ _ _ _ _
        (appendRead _ _ _ _ _ _ _ takeFirst executeFirst) putFirst) takeSecond) executeSecond) putSecond
    rw [← split] at read
    simpa only [List.nil_append,List.append_nil,List.map_append] using read
  have actual := block.originalRoot.reader
  change Semantics.Observation.read root.program = some block.whole.prepared at actual
  change Semantics.Observation.readOps 65 (Semantics.RawTrace.initial root.program.inputs) root.program.operations = _ at bodyRead
  simp only [Semantics.Observation.read,bodyRead,bind,Option.bind,pure] at actual
  exact ⟨(congrArg Semantics.Observation.Prepared.state (Option.some.inj actual)).symm,
    (congrArg Semantics.Observation.Prepared.events (Option.some.inj actual)).symm⟩

#print axioms pair_root_events

/-- The independently read root applies the exchanged operators and then the
same literal output permutation. The equality holds on arbitrary reference
amplitudes with the exact phase and the original output-token order. -/
theorem checked_pair_root_exchange
    {artifact : Artifact} {root : Validity.Root} {owner name signature}
    {block : RuntimeInterval.Prepared root.dependencies root.program}
    {source : @RuntimeAccessSource.Checked artifact.sources owner name root.dependencies root.program signature block}
    {firstStart firstCount firstInputs firstOutputs start count inputs outputs}
    {first : RuntimeAccessPartition.Checked source firstStart firstCount firstInputs firstOutputs}
    (second : RuntimeAccessPartition.Second first start count inputs outputs)
    {firstRequest secondRequest} (pair : RuntimeAccessCallee.Pair second firstRequest secondRequest)
    (firstMap secondMap : Semantics.Exact.Matrix) (a b c d : Nat)
    (firstRead : (Raw.promote first.call.interval.frame.interval.before.quantum.frame.length
      (callerAxes (call := first.call.interval)) pair.firstSectors.actual).run a = (.ok firstMap,b))
    (secondRead : (Raw.promote second.call.frame.interval.before.quantum.frame.length
      (callerAxes (call := second.call)) pair.secondSectors.actual).run c = (.ok secondMap,d)) :
    let exit := second.owners.routing.after.quantum.reference
    let returned := root.program.outputs.flatMap fun token =>
      ((exit.live.find? (fun port => port.token == token)).map (·.wires)).getD []
    let finish := Semantics.Raw.Event.reorder exit.frame.length (Semantics.RawTrace.axes exit returned)
    ∃ firstEvents secondEvents,
      block.whole.prepared.state = exit ∧
      block.whole.prepared.events = (firstEvents ++ secondEvents ++ [finish]).map Semantics.Observation.Event.pure ∧
      ∀ (Reference : Type) (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
        Qleisli.Semantics.RawAction.events root.dependencies (firstEvents ++ secondEvents ++ [finish])
          (fun col => joint col reference) row = Qleisli.Semantics.RawAction.event root.dependencies finish
            (fun col => action firstMap (action secondMap joint) col reference) row := by
  intro exit returned finish
  obtain ⟨firstEvents,secondEvents,firstTrace,secondTrace,exchange⟩ :=
    checked_pair_exchange second pair firstMap secondMap a b c d firstRead secondRead
  obtain ⟨state,original⟩ := pair_root_events second pair firstTrace secondTrace
  refine ⟨firstEvents,secondEvents,state,?_,?_⟩
  · simpa only [List.map_append,List.map_cons,List.map_nil] using original
  intro Reference joint row reference
  have endFrame := (checked_routing_intervals second.owners).2
  have callEnd := (checked_pair_boundaries second).2.2.2.2
  rw [← callEnd,checked_call_frame second.call] at endFrame
  have rows := (Qleisli.Raw.promote_denotes _ _ _ _ c d secondRead).1
  have width : secondMap.rows = 2^exit.frame.length := by
    change secondMap.rows = 2^second.owners.routing.after.quantum.frame.length
    rw [endFrame,rows]
  simp only [Qleisli.Semantics.RawAction.events,List.foldl_append,List.foldl_cons,List.foldl_nil]
  unfold finish Qleisli.Semantics.RawAction.event
  apply Qleisli.Exact.sum_map_congr
  intro col member
  have bounded : col < secondMap.rows := width.symm ▸ List.mem_range.mp member
  have same := exchange Reference joint col reference bounded
  simpa only [Qleisli.Semantics.RawAction.events,List.foldl_append] using congrArg
    (fun coefficient => if gather col (Semantics.RawTrace.axes exit returned) == row then coefficient else 0) same

#print axioms checked_pair_root_exchange

end Exchange

end Qleisli.Raw.AccessCommutation
