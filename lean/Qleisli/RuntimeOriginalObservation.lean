import Qleisli.RuntimeForestFrameEvidence
import QleisliKernel.Qirf.RuntimeObservationAction
import Qleisli.RuntimeNamedThreePackedOutput
import Qleisli.RuntimeObservingPrefix
import Qleisli.RuntimeNamedHeadCoefficients
import Qleisli.Semantics.ObservingAction
import QleisliKernel.FiniteRestriction.Coordinates

/-! Exact action of an original source measure_z or discard. The actual
erasure event, owner receipts and ordered surviving Raw frame fix each
outcome's operator without a product-state premise.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalObservation
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map Owner byOwner)
open QleisliKernel.Qirf.RuntimeForestCode (Frame)

private theorem order_lookup (previous : Map) (roles : List Owner) (ordered : Map)
    (work left : Nat)
    (ran : (roles.mapM (fun owner => do
      let some binding := byOwner previous owner | throw .request
      pure binding) : WorkM Map).run work = (.ok ordered,left)) :
    roles.mapM (byOwner previous) = some ordered := by
  induction roles generalizing ordered work left with
  | nil =>
    have same := (pure_success _ _ _ _ ran).1
    subst ordered
    rfl
  | cons role roles ih =>
    simp only [List.mapM_cons] at ran
    obtain ⟨head,middle,first,rest⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨tail,budget,tailRead,returned⟩ := bind_success _ _ _ _ _ rest
    have all := (pure_success _ _ _ _ returned).1
    subst ordered
    have later := ih tail middle budget tailRead
    cases found : byOwner previous role with
    | none =>
      have impossible : (Except.error Error.request : Except Error Binding) = .ok head := by
        simpa only [found] using congrArg Prod.fst first
      cases impossible
    | some actual =>
      have performed : (pure actual : WorkM Binding).run work = (.ok head,middle) := by
        simpa only [found] using first
      have same := (pure_success _ _ _ _ performed).1
      subst head
      simp only [List.mapM_cons,found,later,bind,Option.bind,pure]

private theorem boundary_lookup {roles state previous result}
    (computed : RuntimeInterval.Computed
      (RuntimeObservationAction.boundary roles state previous) result) :
    roles.mapM (byOwner previous) = some result.bindings := by
  obtain ⟨work,left,ran⟩ := computed
  unfold RuntimeObservationAction.boundary at ran
  obtain ⟨ordered,middle,read,rest⟩ := bind_success _ _ _ _ _ ran
  unfold RuntimeOwnerMap.check at rest
  obtain ⟨certificate,budget,_checked,returned⟩ := bind_success _ _ _ _ _ rest
  have same : result = certificate.val := (pure_success _ _ _ _ returned).1
  subst result
  rw [certificate.property]
  unfold RuntimeOwnerMap.order at read
  obtain ⟨_,budget,_charge,mapped⟩ := bind_success _ _ _ _ _ read
  exact order_lookup previous roles ordered budget middle mapped

/-- The actual observation entry selects its ordered owners from the original
source bindings by full owner identity. -/
theorem original_before_bindings {sources caller dependencies program functionName event block position previous}
    (checked : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous) :
    (checked.operand :: RuntimeObservationAction.spectators event).mapM (byOwner previous) =
      some checked.before.bindings :=
  boundary_lookup checked.beforeRead

/-- The ordered survivors are read from the original owner map. -/
theorem original_after_bindings {sources caller dependencies program functionName event block position previous}
    (checked : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous) :
    (RuntimeObservationAction.spectators event).mapM (byOwner previous) =
      some checked.after.bindings :=
  boundary_lookup checked.afterRead

/-- Both original observation boundary reads select from the same owner map.
The measured or discarded owner is the first coordinate and the original
survivors retain their complete bindings in order. -/
private theorem observation_bindings {sources caller dependencies program functionName event block position previous}
    (checked : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous) :
    checked.before.bindings = checked.input :: checked.after.bindings := by
  have before := original_before_bindings checked
  have after := original_after_bindings checked
  cases found : byOwner previous checked.operand with
  | none => simp [List.mapM_cons,found] at before
  | some head =>
    have full : checked.before.bindings = head :: checked.after.bindings := by
      simpa only [List.mapM_cons,found,after,bind,Option.bind,pure,Option.some.injEq] using before.symm
    have owner : head.owner = checked.operand := by
      have ordered := checked.before.ordered
      rw [full,List.map_cons] at ordered
      exact (List.cons.inj ordered).1
    have chosen : byOwner checked.before.bindings checked.operand = some head := by
      rw [full]
      simp [byOwner,owner]
    have same : checked.input = head := Option.some.inj (checked.inputRead.symm.trans chosen)
    rw [same]
    exact full

open QleisliKernel.Semantics.Finite (gather bit)
open Qleisli.RuntimeForestProduct (gather_append gather_bound)
open QleisliKernel.FiniteRestriction (pack pack_low pack_high)

private theorem unpack {low first row second width : Nat}
    (lowBound : low < 2^width) (firstBound : first < 2^width)
    (same : pack width low row = pack width first second) : low = first ∧ row = second := by
  constructor
  · have projected := congrArg (fun value => value % 2^width) same
    simpa only [pack_low _ _ _ lowBound,pack_low _ _ _ firstBound] using projected
  · have projected := congrArg (fun value => value / 2^width) same
    simpa only [pack_high _ _ _ lowBound,pack_high _ _ _ firstBound] using projected

/-- The independent erasure branch selects the unique original physical
coordinate for an outcome and surviving row. The amplitude can be one column
of any inherited operator, including an entangled reference. -/
private theorem erase_at (bits : Nat) (axes : List Nat) (outcome row : Nat)
    (values : Nat → ℂ) :
    let kept := (List.range bits).filter (fun axis => !axes.contains axis)
    (axes++kept).Perm (List.range bits) →
    outcome < 2^axes.length → row < 2^kept.length →
    ∃ input : Fin (2^bits), gather input.val axes = outcome ∧ gather input.val kept = row ∧
      Qleisli.Semantics.ObservingAction.erase bits axes outcome values row = values input.val := by
  intro kept partition outcomeBound rowBound
  have width : axes.length+kept.length = bits := by
    simpa only [List.length_append,List.length_range] using partition.length_eq
  have coordinateBound : pack axes.length outcome row < 2^bits := by
    rw [← width,Nat.pow_add]
    unfold pack
    calc
      outcome + 2^axes.length*row < 2^axes.length + 2^axes.length*row :=
        Nat.add_lt_add_right outcomeBound _
      _ = 2^axes.length*(row+1) := by rw [Nat.mul_succ,Nat.add_comm]
      _ ≤ 2^axes.length*2^kept.length := Nat.mul_le_mul_left _ rowBound
  obtain ⟨projection,bijection,projectionEq⟩ :=
    Qleisli.RuntimeNamedThreePackedOutput.gather_bijective bits (axes++kept) partition
  obtain ⟨input,chosen⟩ := bijection.2 ⟨pack axes.length outcome row,coordinateBound⟩
  have packed (physical : Nat) :
      gather physical (axes++kept) =
        pack axes.length (gather physical axes) (gather physical kept) := by
    rw [gather_append]
    rfl
  have found : gather input.val (axes++kept) = pack axes.length outcome row :=
    (projectionEq input).symm.trans (congrArg Fin.val chosen)
  have coordinates := unpack (gather_bound input.val axes) outcomeBound ((packed input.val).symm.trans found)
  refine ⟨input,coordinates.1,coordinates.2,?_⟩
  unfold Qleisli.Semantics.ObservingAction.erase
  change ((List.range (2^bits)).map (fun candidate =>
    if gather candidate axes = outcome ∧ gather candidate kept = row then values candidate else 0)).sum =
    values input.val
  calc
    _ = ((List.range (2^bits)).map (fun candidate => if input.val = candidate then values candidate else 0)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro candidate present
      have bound : candidate < 2^bits := List.mem_range.mp present
      have only : gather candidate axes = outcome ∧ gather candidate kept = row ↔ input.val = candidate := by
        constructor
        · rintro ⟨first,second⟩
          have projected : gather candidate (axes++kept) = pack axes.length outcome row := by
            rw [packed,first,second]
          have same : projection input = projection ⟨candidate,bound⟩ := Fin.ext
            ((projectionEq input).trans (found.trans (projected.symm.trans (projectionEq ⟨candidate,bound⟩).symm)))
          exact congrArg Fin.val (bijection.1 same)
        · intro same
          rw [← same]
          exact coordinates
      simp only [only]
    _ = values input.val := Qleisli.Exact.range_delta_sum _ _ _ input.isLt

/-- A surviving owner's coordinate is the same before erasure and after
compressing the exact surviving Raw frame. -/
private theorem gather_retained (before after wires axes : List Nat)
    (kept : after.map before.idxOf = axes) (inside : wires ⊆ after) (physical : Nat) :
    gather (gather physical axes) (wires.map after.idxOf) = gather physical (wires.map before.idxOf) := by
  simp only [gather,List.zipIdx_map,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair member
  change bit (gather physical axes) (after.idxOf pair.1) * 2^pair.2 =
    bit physical (before.idxOf pair.1) * 2^pair.2
  have present : pair.1 ∈ wires := by
    have inWires : pair.1 ∈ wires.zipIdx.map Prod.fst := List.mem_map_of_mem member
    simpa only [List.zipIdx_map_fst] using inWires
  have retained := inside present
  have bound : after.idxOf pair.1 < axes.length := by
    rw [← kept,List.length_map]
    exact List.idxOf_lt_length_of_mem retained
  have lookup : axes[after.idxOf pair.1]? = some (before.idxOf pair.1) := by
    rw [← kept,List.getElem?_map,RuntimeNamedFrameAxes.wireLookup after retained]
    rfl
  have slot := Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans lookup)
  rw [RuntimeScatterTransport.gather_at _ axes _ bound,slot]

#print axioms erase_at

private theorem index_contains (frame wires : List Nat) (wire : Nat)
    (present : wire ∈ frame) (covered : wires ⊆ frame) :
    (wires.map frame.idxOf).contains (frame.idxOf wire) = wires.contains wire := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,List.mem_map]
  constructor
  · rintro ⟨other,member,same⟩
    have lookup := RuntimeNamedFrameAxes.wireLookup frame (covered member)
    rw [same,RuntimeNamedFrameAxes.wireLookup frame present] at lookup
    exact (Option.some.inj lookup) ▸ member
  · intro member
    exact ⟨wire,member,rfl⟩

private theorem kept_indices (frame wires : List Nat) (unique : frame.Nodup)
    (covered : wires ⊆ frame) :
    (frame.filter (fun wire => !wires.contains wire)).map frame.idxOf =
      (List.range frame.length).filter (fun axis => !(wires.map frame.idxOf).contains axis) := by
  rw [← Qleisli.RuntimeNamedCallerAction.self_indices _ unique,List.filter_map]
  apply congrArg (List.map frame.idxOf)
  apply List.filter_congr
  intro wire present
  simp only [Function.comp_def,index_contains frame wires wire present covered]

private theorem axes_partition (bits : Nat) (axes : List Nat) (unique : axes.Nodup)
    (covered : axes ⊆ List.range bits) :
    (axes ++ (List.range bits).filter (fun axis => !axes.contains axis)).Perm (List.range bits) := by
  have selected : axes.Perm ((List.range bits).filter axes.contains) := by
    apply (List.perm_ext_iff_of_nodup unique ((List.nodup_range).filter _)).mpr
    intro axis
    simp only [List.mem_filter,List.contains_iff_mem]
    exact ⟨fun h => ⟨covered h,h⟩,And.right⟩
  exact (selected.append_right _).trans (List.filter_append_perm axes.contains _)

private theorem read_erasure_instruction (fuel : Nat) (before : Semantics.RawTrace.Interface)
    (port : Semantics.Raw.Port) {kind ops output}
    (instruction : RuntimeObservationAction.Reading port.token kind ops output)
    (taken : Semantics.RawTrace.take before port.token =
      some (port,{before with live := before.live.filter (fun live => live.token != port.token)})) :
    Semantics.Observation.readOps (fuel+1) before ops =
      some ({before with
        live := before.live.filter (fun live => live.token != port.token)
        frame := Semantics.Observation.remaining before port.wires},
        [.erase before.frame.length (port.wires.map before.frame.idxOf) output]) := by
  rw [Raw.ObservationAgreement.read_succ]
  cases instruction <;>
    simp [Raw.ObservationAgreement.layer,Raw.ObservationAgreement.readStep,taken,Semantics.RawTrace.axes]

/-- The exact successful source observation emits one original erasure event.
Its retained frame is the original frame with this operand's wires removed. -/
theorem original_erasure {sources caller dependencies program functionName event block position previous}
    (checked : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous) :
    let before := checked.interval.before.quantum.reference
    let after := checked.interval.after.quantum.reference
    let axes := checked.input.port.wires.map before.frame.idxOf
    Semantics.Observation.readOps block.fuel before ((block.operations.drop position.start).take position.count) =
      some (after,[.erase before.frame.length axes checked.measured]) ∧
    after.frame = Semantics.Observation.remaining before checked.input.port.wires := by
  intro before after axes
  obtain ⟨work,left,ran⟩ := checked.interval.intervalRead
  obtain ⟨events,read⟩ := Qleisli.RuntimeObservingPrefix.checkOps_reference _ _ _ _ _ _ _ ran
  have valid := (Raw.Ownership.valid _ checked.interval.history.1)
  have live := checked.before.complete.mem_iff.mp (List.mem_map_of_mem checked.inputMember)
  have found := RuntimeNamedFrameAxes.tokenLookup before.live checked.input.port valid.owners live
  have taken : Semantics.RawTrace.take before checked.input.port.token =
    some (checked.input.port,{before with live := before.live.filter (fun port => port.token != checked.input.port.token)}) := by
    simp [Semantics.RawTrace.take,found]
  change Semantics.Observation.readOps block.fuel before
      ((block.operations.drop position.start).take position.count) = some (after,events) at read
  cases fuel : block.fuel with
  | zero => simp [Semantics.Observation.readOps,fuel] at read
  | succ depth =>
    rw [fuel] at read
    have actual := read_erasure_instruction depth before checked.input.port checked.instruction taken
    have same := Option.some.inj (read.symm.trans actual)
    have emitted : events = [.erase before.frame.length axes checked.measured] := congrArg Prod.snd same
    refine ⟨?_,congrArg (fun result => result.1.frame) same⟩
    rw [← emitted]
    exact read

open QleisliKernel.Qirf.RuntimeForestCode (OwnerCode OwnerCodes sparseLayout_complete forestBasis)
open Qleisli.RuntimeForestProduct (referenceAction owner_bounds)
open Qleisli.RuntimeForestOrderedProduct
open Qleisli.Semantics.Exact (entry)

private theorem retained_coefficients {bindings : Map} (owners : OwnerCodes bindings)
    (before after axes : List Nat) (kept : after.map before.idxOf = axes)
    (covered : ∀ binding ∈ bindings, binding.port.wires ⊆ after)
    (physical row : Nat) (coordinate : gather physical axes = row) (logical : Nat) :
    coefficients before owners physical logical = coefficients after owners row logical := by
  induction owners generalizing logical with
  | nil => rfl
  | @cons binding bindings head tail ih =>
    simp only [coefficients]
    rw [← gather_retained before after binding.port.wires axes kept (covered binding List.mem_cons_self),
      coordinate,ih (fun binding present => covered binding (List.mem_cons_of_mem _ present))]

private theorem cast_owners {bindings other : Map} (same : bindings = other)
    (owners : OwnerCodes bindings) :
    let moved : OwnerCodes other := same ▸ owners
    (sparseProduct owners).dimension = (sparseProduct moved).dimension ∧
      ∀ wires row logical, coefficients wires owners row logical = coefficients wires moved row logical := by
  cases same
  exact ⟨rfl,fun _ _ _ => rfl⟩

private theorem frame_dimension {roles state checked} (frame : @Frame roles state checked) :
    frame.code.dimension = (sparseProduct frame.owners).dimension :=
  (frame_product_agrees frame).dimension.trans (product_agrees frame.owners).dimension.symm

/-- The logical effect of consuming a coded owner at an observed physical
coordinate. It acts separately on every surviving and external reference
coordinate, even when the input is correlated. -/
noncomputable def outcomeJointLayout {Reference : Type} (layout : Semantics.FiniteCarrier.Layout)
    (outcome : Nat) (joint : Nat → Reference → ℂ) (tail : Nat) (ref : Reference) : ℂ :=
  ((List.range layout.labels.length).map fun logical =>
    entry (QleisliKernel.Semantics.FiniteCarrier.encoding layout) outcome logical *
      joint (logical+layout.labels.length*tail) ref).sum

noncomputable def outcomeJoint {Reference : Type} {binding : Binding} (owner : OwnerCode binding)
    (outcome : Nat) (joint : Nat → Reference → ℂ) : Nat → Reference → ℂ :=
  outcomeJointLayout owner.layout outcome joint

/-- Each actual erasure coefficient is the source owner's basis effect in
the original input code. The retained owners use their original output code,
including all zero-width identities and arbitrary reference amplitudes. -/
theorem original_erasure_action {sources caller dependencies program functionName event block position previous}
    (checked : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous) (input : Frame checked.before) :
    let before := checked.interval.before.quantum.frame
    let after := checked.interval.after.quantum.frame
    let axes := checked.input.port.wires.map before.idxOf
    ∃ consumed : OwnerCode checked.input, ∃ output : Frame checked.after,
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) outcome row,
        outcome < 2^axes.length → row < 2^after.length → ∀ ref,
        Qleisli.Semantics.ObservingAction.erase before.length axes outcome
          (fun physical => referenceAction input joint physical ref) row =
            referenceAction output (outcomeJoint consumed outcome joint) row ref := by
  intro before after axes
  let kept := (List.range before.length).filter (fun axis => !axes.contains axis)
  have same := observation_bindings checked
  have inputValid := Raw.Ownership.valid _ checked.interval.history.1
  have outputValid := Raw.Ownership.valid _ checked.interval.history.2.2.1
  have sourcePerm := Qleisli.RuntimeNamedThreePackedOutput.final_axes_permutation checked.before checked.interval.history.1
  rw [same] at sourcePerm
  change (QleisliKernel.Qirf.RuntimeForestCode.forestAxes before (checked.input :: checked.after.bindings)).Perm _ at sourcePerm
  simp only [QleisliKernel.Qirf.RuntimeForestCode.forestAxes,List.flatMap_cons,List.map_append] at sourcePerm
  change (axes ++ (checked.after.bindings.flatMap fun binding => binding.port.wires).map before.idxOf).Perm
    (List.range before.length) at sourcePerm
  have axisUnique : axes.Nodup := by
    have all := sourcePerm.nodup_iff.mpr List.nodup_range
    exact (List.nodup_append.mp all).1
  have inside : axes ⊆ List.range before.length :=
    fun axis member => sourcePerm.mem_iff.mp (List.mem_append_left _ member)
  have partition := axes_partition before.length axes axisUnique inside
  have operand : checked.input.port ∈ checked.interval.before.quantum.live :=
    checked.before.complete.mem_iff.mp (List.mem_map_of_mem checked.inputMember)
  have operandWires : checked.input.port.wires ⊆ before :=
    fun wire member => inputValid.covered wire (List.mem_flatMap.mpr ⟨checked.input.port,operand,member⟩)
  have remainder : after = before.filter (fun wire => !checked.input.port.wires.contains wire) :=
    (original_erasure checked).2
  have keptAxes : after.map before.idxOf = kept := by
    rw [remainder]
    exact kept_indices before checked.input.port.wires inputValid.frame operandWires
  have keptWidth : after.length = kept.length := by
    simpa only [List.length_map] using congrArg List.length keptAxes
  have outputWires : ∀ binding ∈ checked.after.bindings, binding.port.wires ⊆ after := by
    intro binding member wire belongs
    have live := checked.after.complete.mem_iff.mp (List.mem_map_of_mem member)
    exact outputValid.covered wire (List.mem_flatMap.mpr ⟨binding.port,live,belongs⟩)
  let moved : OwnerCodes (checked.input :: checked.after.bindings) := same ▸ input.owners
  have beforeFacts := cast_owners same input.owners
  change (sparseProduct input.owners).dimension = (sparseProduct moved).dimension ∧
    ∀ wires row logical, coefficients wires input.owners row logical = coefficients wires moved row logical
    at beforeFacts
  cases movedRead : moved with
  | cons consumed retained =>
    rw [movedRead] at beforeFacts
    obtain ⟨layout,layoutRead⟩ := Qleisli.RuntimeForestFrameEvidence.forest_layout retained
    obtain ⟨code,codeRead,_⟩ := sparseLayout_complete (forestBasis checked.after.bindings) layout layoutRead
    let output : Frame checked.after := ⟨retained,code,codeRead⟩
    refine ⟨consumed,output,?_⟩
    intro Reference joint outcome row outcomeBound rowBound ref
    have rowKept : row < 2^kept.length := by simpa only [← keptWidth] using rowBound
    obtain ⟨physical,selected,survives,action⟩ := erase_at before.length axes outcome row
      (fun physical => referenceAction input joint physical ref) partition outcomeBound rowKept
    rw [action,ordered_product_action,ordered_product_action]
    have dim : input.code.dimension = consumed.layout.labels.length * output.code.dimension := by
      rw [frame_dimension input,beforeFacts.1,frame_dimension output]
      rfl
    have coeff (logical : Nat) : coefficients before input.owners physical.val logical =
        entry (QleisliKernel.Semantics.FiniteCarrier.encoding consumed.layout) outcome
          (logical % consumed.layout.labels.length) *
          coefficients after output.owners row (logical / consumed.layout.labels.length) := by
      rw [beforeFacts.2]
      change entry (QleisliKernel.Semantics.FiniteCarrier.encoding consumed.layout)
        (gather physical.val axes) (logical % consumed.layout.labels.length) *
        coefficients before retained physical.val (logical / consumed.layout.labels.length) = _
      rw [selected,retained_coefficients retained before after kept keptAxes outputWires
        physical.val row survives]
    rw [dim,Qleisli.RuntimeNamedHeadCoefficients.sum_blocks]
    apply Qleisli.Exact.sum_map_congr
    intro tail _
    unfold outcomeJoint outcomeJointLayout
    rw [← List.sum_map_mul_left]
    apply Qleisli.Exact.sum_map_congr
    intro digit member
    have bound := List.mem_range.mp member
    rw [coeff,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound,
      Nat.add_mul_div_left _ _ (owner_bounds consumed).1,Nat.div_eq_of_lt bound,Nat.zero_add]
    ring

#print axioms original_erasure_action

open Qleisli.Semantics.ObservingAction (History)

/-- Every outcome of the actual source observation keeps the original
visible and hidden histories and has its exact unnormalized operator on the
remaining coded owners. Input agreement is needed only on finite Raw rows. -/
theorem original_observation_histories {sources caller dependencies program functionName event block position previous}
    (checked : @RuntimeObservationAction.Checked sources caller dependencies program functionName
      event block position previous) (input : Frame checked.before) :
    let before := checked.interval.before.quantum.reference
    let after := checked.interval.after.quantum.reference
    let axes := checked.input.port.wires.map before.frame.idxOf
    let observation := Semantics.Observation.Event.erase before.frame.length axes checked.measured
    Semantics.Observation.readOps block.fuel before ((block.operations.drop position.start).take position.count) =
      some (after,[observation]) ∧
    event.value = RuntimeObservationAction.result functionName event checked.operand checked.measured ∧
    ∃ consumed : OwnerCode checked.input, ∃ output : Frame checked.after,
      ∀ (recurse : List Semantics.Observation.Event → History → Option (List History))
        (joint : Nat → Nat → ℂ) (history : History),
        (∀ physical, physical < 2^before.frame.length → ∀ col,
          history.operator physical col = referenceAction input joint physical col) →
        ∃ branch : Nat → History,
          Qleisli.Semantics.ObservingAction.step dependencies recurse observation history =
            some ((List.range (2^axes.length)).map branch) ∧
          ∀ outcome, outcome < 2^axes.length →
            (branch outcome).values = (match checked.measured with
              | none => history.values
              | some id => history.values++[(id,outcome == 1)]) ∧
            (branch outcome).hidden = history.hidden++[outcome] ∧
            ∀ row, row < 2^after.frame.length → ∀ col,
              (branch outcome).operator row col =
                referenceAction output (outcomeJoint consumed outcome joint) row col := by
  intro before after axes observation
  obtain ⟨consumed,output,action⟩ := original_erasure_action checked input
  refine ⟨(original_erasure checked).1,checked.sourceValue,consumed,output,?_⟩
  intro recurse joint history represented
  let branch (outcome : Nat) : History := {
    values := match checked.measured with
      | none => history.values
      | some id => history.values++[(id,outcome == 1)]
    hidden := history.hidden++[outcome]
    operator := fun row col => Qleisli.Semantics.ObservingAction.erase before.frame.length axes outcome
      (fun physical => history.operator physical col) row }
  refine ⟨branch,?_,fun outcome outcomeBound => ⟨rfl,rfl,?_⟩⟩
  · cases measured : checked.measured <;> simp [Qleisli.Semantics.ObservingAction.step,observation,branch,measured]
  ·
    intro row rowBound col
    change Qleisli.Semantics.ObservingAction.erase before.frame.length axes outcome
      (fun physical => history.operator physical col) row = _
    calc
      _ = Qleisli.Semantics.ObservingAction.erase before.frame.length axes outcome
          (fun physical => referenceAction input joint physical col) row := by
        unfold Qleisli.Semantics.ObservingAction.erase
        apply Qleisli.Exact.sum_map_congr
        intro physical present
        simp only [represented physical (List.mem_range.mp present) col]
      _ = _ := action joint outcome row outcomeBound rowBound col

#print axioms original_observation_histories

end Qleisli.RuntimeOriginalObservation
