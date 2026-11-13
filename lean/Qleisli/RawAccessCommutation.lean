import Qleisli.RawBranchFunction
import Qleisli.RawPureInstrumentAction
import Qleisli.RoutedControlCommutation
import Qleisli.RuntimeAdjacentInterval
import Qleisli.RuntimeForestProduct
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

end Qleisli.Raw.AccessCommutation
