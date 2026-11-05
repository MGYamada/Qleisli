import Qleisli.RuntimeNamedOutputOrder
import Qleisli.RuntimeNamedPrimitiveOutputs

/-! Exact logical coefficient update in canonical owner order. Rectangular
logical dimensions are independent of physical padding. These laws concern
total complex amplitudes; source/owner correspondence and native work are
separate obligations. No execution capability follows from an arbitrary matrix.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedHeadCoefficients
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open Qleisli.Semantics.Exact

noncomputable def fibre {Reference : Type} (dimension spectators : Nat)
    (coefficient : Nat → Complex) (joint : Nat → Reference → Complex)
    (digit : Nat) (reference : Reference) : Complex :=
  ((List.range spectators).map fun high =>
    coefficient high * joint (digit+dimension*high) reference).sum

noncomputable def applyHead {Reference : Type} (matrix : Matrix)
    (joint : Nat → Reference → Complex) (logical : Nat) (reference : Reference) : Complex :=
  action matrix (fun input ref => joint (input+matrix.cols*(logical/matrix.rows)) ref)
    (logical%matrix.rows) reference

/-- The same spectator/reference fibre carries the exact logical matrix
update. Input/output strides are the true logical dimensions, including
non-power-of-two cardinalities and dimension-one owners. -/
theorem fibre_applyHead {Reference : Type} (matrix : Matrix) (spectators : Nat)
    (coefficient : Nat → Complex) (joint : Nat → Reference → Complex)
    (digit : Nat) (reference : Reference) (bound : digit < matrix.rows) :
    fibre matrix.rows spectators coefficient (applyHead matrix joint) digit reference =
      action matrix (fibre matrix.cols spectators coefficient joint) digit reference := by
  have positive : 0 < matrix.rows := Nat.lt_of_le_of_lt (Nat.zero_le digit) bound
  have remainder (high : Nat) : (digit+matrix.rows*high)%matrix.rows = digit := by
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]
  have quotient (high : Nat) : (digit+matrix.rows*high)/matrix.rows = high := by
    rw [Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt bound,Nat.zero_add]
  unfold fibre applyHead
  simp only [remainder,quotient]
  unfold action
  calc
    _ = ((List.range spectators).map fun high =>
        ((List.range matrix.cols).map fun input =>
          coefficient high * (entry matrix digit input * joint (input+matrix.cols*high) reference)).sum).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro high _member
      rw [List.sum_map_mul_left]
    _ = ((List.range matrix.cols).map fun input =>
        ((List.range spectators).map fun high =>
          coefficient high * (entry matrix digit input * joint (input+matrix.cols*high) reference)).sum).sum :=
      Qleisli.Exact.sum_swap _ _ _
    _ = _ := by
      simp only [mul_left_comm (coefficient _) (entry matrix _ _),List.sum_map_mul_left]

#print axioms fibre_applyHead

theorem range_blocks (low high : Nat) :
    List.range (low*high) =
      (List.range high).flatMap (fun block => (List.range low).map fun digit => digit+low*block) := by
  induction high with
  | zero => simp
  | succ high ih =>
    rw [Nat.mul_succ,List.range_add,ih,List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    apply congrArg (fun values =>
      (List.range high).flatMap (fun block => (List.range low).map fun digit => digit+low*block) ++ values)
    apply List.map_congr_left
    intro digit _member
    exact Nat.add_comm _ _

theorem sum_blocks (low high : Nat) (term : Nat → Complex) :
    ((List.range (low*high)).map term).sum =
      ((List.range high).map fun block =>
        ((List.range low).map fun digit => term (digit+low*block)).sum).sum := by
  rw [range_blocks,List.map_flatMap,List.flatMap_def,List.sum_flatten]
  simp only [List.map_map,Function.comp_def]

noncomputable def headEncoding {Reference : Type} (code : Matrix) (spectators : Nat)
    (coefficient : Nat → Complex) (joint : Nat → Reference → Complex)
    (physical : Nat) (reference : Reference) : Complex :=
  ((List.range (code.cols*spectators)).map fun logical =>
    entry code physical (logical%code.cols) *
      (coefficient (logical/code.cols) * joint logical reference)).sum

/-- Reindex the complete canonical product code using logical cardinality,
including every physical padding row. No physical width fixes a logical index. -/
theorem head_code_action {Reference : Type} (code : Matrix) (spectators : Nat)
    (coefficient : Nat → Complex) (joint : Nat → Reference → Complex)
    (physical : Nat) (reference : Reference) (positive : 0 < code.cols) :
    headEncoding code spectators coefficient joint physical reference =
      action code (fibre code.cols spectators coefficient joint) physical reference := by
  unfold headEncoding
  rw [sum_blocks]
  have rearranged (digit high : Nat) (bound : digit < code.cols) :
      (digit+code.cols*high)%code.cols = digit ∧
      (digit+code.cols*high)/code.cols = high := by
    constructor
    · simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]
    · rw [Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt bound,Nat.zero_add]
  have first :
      ((List.range spectators).map fun high =>
        ((List.range code.cols).map fun digit =>
          entry code physical ((digit+code.cols*high)%code.cols) *
            (coefficient ((digit+code.cols*high)/code.cols) * joint (digit+code.cols*high) reference)).sum).sum =
      ((List.range spectators).map fun high =>
        ((List.range code.cols).map fun digit =>
          entry code physical digit * (coefficient high * joint (digit+code.cols*high) reference)).sum).sum := by
    apply Qleisli.Exact.sum_map_congr
    intro high _present
    apply Qleisli.Exact.sum_map_congr
    intro digit member
    rw [(rearranged digit high (List.mem_range.mp member)).1,
      (rearranged digit high (List.mem_range.mp member)).2]
  rw [first,Qleisli.Exact.sum_swap]
  unfold action fibre
  simp only [List.sum_map_mul_left]

/-- Exact logical evolution of the canonical full output coefficients equals
the native output-code action on the evolved spectator/reference fibre. -/
theorem head_operator_encoding {Reference : Type} (code matrix : Matrix) (spectators : Nat)
    (coefficient : Nat → Complex) (joint : Nat → Reference → Complex)
    (physical : Nat) (reference : Reference) (positive : 0 < code.cols)
    (shape : code.cols = matrix.rows) :
    headEncoding code spectators coefficient (applyHead matrix joint) physical reference =
      action code (fun digit ref =>
        action matrix (fibre matrix.cols spectators coefficient joint) digit ref) physical reference := by
  rw [head_code_action code spectators coefficient (applyHead matrix joint) physical reference positive]
  unfold action
  apply Qleisli.Exact.sum_map_congr
  intro digit member
  have bound : digit < matrix.rows := by rw [← shape]; exact List.mem_range.mp member
  rw [shape,fibre_applyHead matrix spectators coefficient joint digit reference bound]
  rfl

#print axioms head_operator_encoding


open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.RuntimeForestProduct Qleisli.RuntimeForestOrderedProduct

/-- Reorder a real complete frame around an actual retained target binding.
The recoding uses its original source identities and logical cardinalities;
all spectator coefficients and arbitrary reference correlations remain. -/
theorem frame_head_encoding {Reference : Type} {roles state checked}
    (frame : @Frame roles state checked) (target : Binding) (rest : Map)
    (actual : OwnerCode target) (spectators : OwnerCodes rest)
    (kept : reindex frame.owners (target::rest) = some (.cons actual spectators))
    (permutation : (target::rest).Perm checked.bindings)
    (joint : Nat → Reference → Complex) (physical : Nat) (reference : Reference) :
    referenceAction frame joint physical reference =
      headEncoding (Semantics.FiniteCarrier.encoding actual.layout) (sparseProduct spectators).dimension
        (fun high => coefficients state.quantum.frame spectators physical high)
        (fun logical ref => joint
          (Qleisli.MixedRadix.recode (target::rest) checked.bindings (dimensionAt frame.owners) logical) ref)
        (Semantics.Finite.gather physical (target.port.wires.map state.quantum.frame.idxOf)) reference := by
  have law := RuntimeNamedOutputOrder.regroup_dense_action frame (target::rest)
    ⟨.cons actual spectators,kept⟩ permutation joint physical reference
  simpa only [headEncoding,sparseProduct,Sparse.tensor,Sparse.ofLayout,coefficients,mul_assoc] using law

#print axioms frame_head_encoding


def CanonicalEncoding {Reference : Type} {roles state checked}
    (frame : @Frame roles state checked) (target : Binding) (native : Matrix) : Prop :=
  ∃ spectators : OwnerCodes (checked.bindings.erase target),
    ∀ (joint : Nat → Reference → Complex) physical reference,
      referenceAction frame joint physical reference =
        headEncoding native (sparseProduct spectators).dimension
          (fun high => coefficients state.quantum.frame spectators physical high)
          (fun logical ref => joint
            (Qleisli.MixedRadix.recode (target::checked.bindings.erase target) checked.bindings
              (dimensionAt frame.owners) logical) ref)
          (Semantics.Finite.gather physical (target.port.wires.map state.quantum.frame.idxOf)) reference

/-- The original complete map and the same native code read derive the whole
canonical output encoding. The actual target, spectators and logical recoding
are never chosen by width or supplied as an encoding equation. -/
theorem original_native_head_encoding {Reference : Type} {roles state checked}
    (frame : @Frame roles state checked) (target : Binding) (member : target ∈ checked.bindings)
    (native : Matrix) (read : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨target.port,target.owner.basis⟩]) native) :
    CanonicalEncoding (Reference := Reference) frame target native := by
  have permutation : (target::checked.bindings.erase target).Perm checked.bindings :=
    (List.perm_cons_erase member).symm
  obtain ⟨all,kept⟩ := reindex_exists frame.owners (target::checked.bindings.erase target) permutation.subset
  cases all with
  | cons actual spectators =>
    refine ⟨spectators,?_⟩
    intro joint physical reference
    rw [RuntimeNamedInputAction.singleton_encoding actual native read]
    exact frame_head_encoding frame target _ actual spectators kept permutation joint physical reference

def OccurrenceCanonicalEncoding {Reference : Type} {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step) : Prop :=
  match held with
  | .named (boundary := boundary) (action := action) _ _ =>
    ∀ frame : Frame boundary.afterFrame,
      ∃ target : Binding, boundary.mapped = [target] ∧
        CanonicalEncoding (Reference := Reference) frame target action.outputCode

/-- This final canonical output description consumes the original child run
and native read, with all actual caller spectators and source output order. -/
theorem actual_occurrence_canonical_encoding {Reference : Type}
    {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step) :
    OccurrenceCanonicalEncoding (Reference := Reference) held := by
  have codes := RuntimeNamedPrimitiveOutputs.actual_occurrence_output_code held call
  cases held with
  | named original bound =>
    intro frame
    obtain ⟨target,same,member,read⟩ := codes
    exact ⟨target,same,original_native_head_encoding frame target member _ read⟩

#print axioms actual_occurrence_canonical_encoding


open Qleisli.RuntimeForestRegroup Qleisli.RuntimeFiniteTargetFibre
open Qleisli.MixedRadix

/-- Sum arbitrary original logical coefficients in the real reordered domain. -/
theorem canonical_sum {roles state checked} (frame : @Frame roles state checked)
    (wanted : Map) (retained : Retained frame.owners wanted) (permutation : wanted.Perm checked.bindings)
    (term : Nat → Complex) :
    ((List.range frame.code.dimension).map term).sum =
      ((List.range (sparseProduct retained.codes).dimension).map fun logical =>
        term (recode wanted checked.bindings (dimensionAt frame.owners) logical)).sum := by
  have indices := RuntimeNamedOutputOrder.regroup_range frame wanted retained permutation
  let inverse := recode wanted checked.bindings (dimensionAt frame.owners)
  have back := indices.map inverse
  have same : ((List.range frame.code.dimension).map (regroupIndex frame wanted)).map inverse =
      List.range frame.code.dimension := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (List.range frame.code.dimension)]
    apply List.map_congr_left
    intro logical member
    exact regroup_inverse frame wanted permutation logical (List.mem_range.mp member)
  rw [same] at back
  have sums := (back.map term).sum_eq
  simpa only [List.map_map,Function.comp_def,inverse,regroup_volume frame wanted retained permutation] using sums

/-- Recode the exact original owner digit, preserving its source identity. -/
theorem recoded_digit {roles state checked} (frame : @Frame roles state checked)
    (wanted : Map) (permutation : wanted.Perm checked.bindings) (logical : Nat)
    (bound : logical < volume wanted (dimensionAt frame.owners))
    (binding : Binding) (member : binding ∈ checked.bindings) :
    decode checked.bindings (dimensionAt frame.owners)
        (recode wanted checked.bindings (dimensionAt frame.owners) logical) binding =
      decode wanted (dimensionAt frame.owners) logical binding := by
  apply decode_encode
  · intro selected present
    exact decode_bound wanted (dimensionAt frame.owners) logical
      (fun owner inside => cards_positive frame.owners owner (permutation.subset inside))
      bound selected (permutation.mem_iff.mpr present)
  · exact member

private theorem bindings_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    checked.bindings.Nodup :=
  List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
    checked.tokensDistinct

/-- The other owners' full coefficient product is unchanged by the canonical
logical recoding. Their original identities and physical coordinates remain. -/
theorem spectator_recoded {roles state checked} (frame : @Frame roles state checked)
    (target : Binding) (member : target ∈ checked.bindings) (actual : OwnerCode target)
    (spectators : OwnerCodes (checked.bindings.erase target)) (logical physical : Nat)
    (bound : logical < actual.layout.labels.length * (sparseProduct spectators).dimension) :
    spectatorCoefficient frame target physical
        (recode (target::checked.bindings.erase target) checked.bindings (dimensionAt frame.owners) logical) =
      coefficients state.quantum.frame spectators physical (logical/actual.layout.labels.length) := by
  have permutation := (List.perm_cons_erase member).symm
  have card := dimensionAt_eq frame.owners target member actual
  have restVolume := owner_volume frame.owners spectators (List.erase_subset (a := target) (l := checked.bindings))
  have logicalBound : logical < volume (target::checked.bindings.erase target) (dimensionAt frame.owners) := by
    change logical < dimensionAt frame.owners target * volume (checked.bindings.erase target) (dimensionAt frame.owners)
    rw [card,restVolume]
    exact bound
  have tailBound : logical/actual.layout.labels.length <
      volume (checked.bindings.erase target) (dimensionAt frame.owners) := by
    rw [restVolume]
    exact Nat.div_lt_of_lt_mul bound
  rw [coefficients_factors frame.owners state.quantum.frame spectators physical
    (logical/actual.layout.labels.length) (List.erase_subset (a := target) (l := checked.bindings))
    (List.Nodup.erase target (bindings_unique checked)) tailBound]
  unfold spectatorCoefficient
  apply congrArg List.prod
  apply List.map_congr_left
  intro binding present
  have facts := (bindings_unique checked).mem_erase_iff.mp present
  rw [recoded_digit frame _ permutation logical logicalBound binding facts.2,
    decode_cons,if_neg facts.1.symm,card]

/-- The complete source-indexed target fibre is the canonical logical fibre
of the same real frame, with every original spectator/reference coefficient. -/
theorem target_fibre_canonical {Reference : Type} {roles state checked}
    (frame : @Frame roles state checked) (target : Binding) (member : target ∈ checked.bindings)
    (actual : OwnerCode target) (spectators : OwnerCodes (checked.bindings.erase target))
    (kept : reindex frame.owners (target::checked.bindings.erase target) = some (.cons actual spectators))
    (joint : Nat → Reference → Complex) (physical digit : Nat) (reference : Reference)
    (digitBound : digit < actual.layout.labels.length) :
    targetFibre frame target physical joint digit reference =
      fibre actual.layout.labels.length (sparseProduct spectators).dimension
        (fun high => coefficients state.quantum.frame spectators physical high)
        (fun logical ref => joint
          (recode (target::checked.bindings.erase target) checked.bindings (dimensionAt frame.owners) logical) ref)
        digit reference := by
  have permutation := (List.perm_cons_erase member).symm
  have card := dimensionAt_eq frame.owners target member actual
  have positive : 0 < actual.layout.labels.length := (owner_bounds actual).1
  have restVolume := owner_volume frame.owners spectators (List.erase_subset (a := target) (l := checked.bindings))
  unfold targetFibre
  rw [canonical_sum frame (target::checked.bindings.erase target) ⟨.cons actual spectators,kept⟩ permutation]
  change ((List.range (actual.layout.labels.length*(sparseProduct spectators).dimension)).map _).sum = _
  rw [sum_blocks]
  unfold fibre
  apply Qleisli.Exact.sum_map_congr
  intro high highMember
  have highBound := List.mem_range.mp highMember
  have term (low : Nat) (lowBound : low < actual.layout.labels.length) :
      let logical := low+actual.layout.labels.length*high
      logical < actual.layout.labels.length*(sparseProduct spectators).dimension := by
    dsimp only
    calc
      low+actual.layout.labels.length*high < actual.layout.labels.length+actual.layout.labels.length*high :=
        Nat.add_lt_add_right lowBound _
      _ = actual.layout.labels.length*(high+1) := by ring
      _ ≤ actual.layout.labels.length*(sparseProduct spectators).dimension :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt highBound)
  have transformed :
      ((List.range actual.layout.labels.length).map fun low =>
        if decode checked.bindings (dimensionAt frame.owners)
            (recode (target::checked.bindings.erase target) checked.bindings (dimensionAt frame.owners)
              (low+actual.layout.labels.length*high)) target = digit then
          spectatorCoefficient frame target physical
            (recode (target::checked.bindings.erase target) checked.bindings (dimensionAt frame.owners)
              (low+actual.layout.labels.length*high)) *
            joint (recode (target::checked.bindings.erase target) checked.bindings (dimensionAt frame.owners)
              (low+actual.layout.labels.length*high)) reference
        else 0).sum =
      ((List.range actual.layout.labels.length).map fun low =>
        if digit = low then coefficients state.quantum.frame spectators physical high *
          joint (recode (target::checked.bindings.erase target) checked.bindings (dimensionAt frame.owners)
            (low+actual.layout.labels.length*high)) reference else 0).sum := by
    apply Qleisli.Exact.sum_map_congr
    intro low lowMember
    have lowBound := List.mem_range.mp lowMember
    have nBound := term low lowBound
    have logicalBound : low+actual.layout.labels.length*high <
        volume (target::checked.bindings.erase target) (dimensionAt frame.owners) := by
      change low+actual.layout.labels.length*high < dimensionAt frame.owners target *
        volume (checked.bindings.erase target) (dimensionAt frame.owners)
      rw [card,restVolume]
      exact nBound
    rw [recoded_digit frame _ permutation _ logicalBound target member,decode_head,card,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lowBound,
      spectator_recoded frame target member actual spectators _ physical nBound,
      Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt lowBound,Nat.zero_add]
    simp only [eq_comm]
  rw [transformed]
  exact Qleisli.Exact.range_delta_sum actual.layout.labels.length digit _ digitBound

#print axioms target_fibre_canonical


/-- Zero logical dimension is handled by the actual empty sums. -/
theorem head_code_action_total {Reference : Type} (code : Matrix) (spectators : Nat)
    (coefficient : Nat → Complex) (joint : Nat → Reference → Complex)
    (physical : Nat) (reference : Reference) :
    headEncoding code spectators coefficient joint physical reference =
      action code (fibre code.cols spectators coefficient joint) physical reference := by
  by_cases zero : code.cols = 0
  · simp only [headEncoding,action,zero,Nat.zero_mul,List.range_zero,List.map_nil,List.sum_nil]
  · exact head_code_action code spectators coefficient joint physical reference (Nat.pos_of_ne_zero zero)

theorem head_operator_encoding_total {Reference : Type} (code matrix : Matrix) (spectators : Nat)
    (coefficient : Nat → Complex) (joint : Nat → Reference → Complex)
    (physical : Nat) (reference : Reference) (shape : code.cols = matrix.rows) :
    headEncoding code spectators coefficient (applyHead matrix joint) physical reference =
      action code (fun digit ref =>
        action matrix (fibre matrix.cols spectators coefficient joint) digit ref) physical reference := by
  rw [head_code_action_total]
  unfold action
  apply Qleisli.Exact.sum_map_congr
  intro digit member
  have bound : digit < matrix.rows := by rw [← shape]; exact List.mem_range.mp member
  rw [shape,fibre_applyHead matrix spectators coefficient joint digit reference bound]
  rfl

def OccurrenceCanonicalInputAction {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (events : List Semantics.Raw.Event) : Prop :=
  match held with
  | .named (before := before) (scope := scope) (action := primitive) _ bound =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (frame : Frame checked),
      checked.bindings = before.bindings →
      ∃ actual : OwnerCode bound.binding,
      ∃ spectators : OwnerCodes (checked.bindings.erase bound.binding),
        reindex frame.owners (bound.binding::checked.bindings.erase bound.binding) = some (.cons actual spectators) ∧
        ∀ {Reference : Type} (joint : Nat → Reference → Complex) base row reference,
          row < primitive.physical.rows →
          Qleisli.Semantics.RawAction.event dependencies
              (.reorder bound.binding.port.wires.length (bound.binding.port.wires.map bound.binding.port.wires.idxOf))
              (fun value => Qleisli.Semantics.RawAction.events dependencies events
                (fun input => referenceAction frame joint input reference)
                (Semantics.Finite.scatter base (RuntimeNamedFrameAxes.mixedAxes scope) value)) row =
            headEncoding primitive.outputCode (sparseProduct spectators).dimension
              (fun high => coefficients scope.interval.before.quantum.frame spectators base high)
              (applyHead primitive.expected (fun logical ref => joint
                (recode (bound.binding::checked.bindings.erase bound.binding) checked.bindings
                  (dimensionAt frame.owners) logical) ref)) row reference

/-- The actual original named call now supplies its full canonical logical
coefficient update from the retained input frame and native source-action law.
Its final caller output frame/spectator geometry still requires the separate
original boundary join; no source/preservation premise is inferred by width. -/
theorem actual_occurrence_canonical_input_action
    {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (events : List Semantics.Raw.Event) (lifted : RuntimeNamedOccurrenceAction.On held events) :
    OccurrenceCanonicalInputAction held events := by
  have inputs := RuntimeNamedPrimitiveInputs.actual_occurrence_input held call
  have originalLaw := RuntimeNamedInputAction.original_input_action held inputs events lifted
  cases held with
  | @named start count inputTokens sources caller before childHistory childRetired ordinary first size input output role kind
      event scope body read boundary finalOrdinary primitive original bound =>
    intro roles checked frame same
    have ordered := RuntimeSelectionPartition.order_values _ _ _ boundary.input.orderRead
    have member : bound.binding ∈ checked.bindings := by
      rw [same]
      apply ordered.1
      exact (congrArg (fun bindings => bound.binding ∈ bindings) bound.singleton).mpr
        (List.mem_singleton_self _)
    have permutation := (List.perm_cons_erase member).symm
    obtain ⟨all,kept⟩ := reindex_exists frame.owners (bound.binding::checked.bindings.erase bound.binding) permutation.subset
    cases all with
    | cons actual spectators =>
      refine ⟨actual,spectators,kept,?_⟩
      intro Reference joint base row reference small
      have inputRead := primitive.inputRead
      have carriers : primitive.interval.selected.map (fun port =>
          (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) =
          [⟨bound.binding.port,bound.binding.owner.basis⟩] := by
        simpa only [RuntimeNamedPrimitiveInputs.OccurrenceInput,bound.singleton,carrierOwners,List.map_singleton] using inputs
      rw [carriers] at inputRead
      have inputCode := RuntimeNamedInputAction.singleton_encoding actual primitive.inputCode inputRead
      have inputShape := primitive.action.logicalShape.1
      rw [primitive.equation,inputCode] at inputShape
      change primitive.expected.cols = actual.layout.labels.length at inputShape
      have outputShape := primitive.action.logicalShape.2
      rw [primitive.equation] at outputShape
      rw [head_operator_encoding_total primitive.outputCode primitive.expected _ _ _ row reference outputShape.symm]
      have law := originalLaw checked frame same joint base row reference small
      have fibres : (fun logical ref =>
          action primitive.expected (targetFibre frame bound.binding base joint) logical ref) =
          (fun logical ref => action primitive.expected
            (fibre actual.layout.labels.length (sparseProduct spectators).dimension
              (fun high => coefficients scope.interval.before.quantum.frame spectators base high)
              (fun index reference => joint
                (recode (bound.binding::checked.bindings.erase bound.binding) checked.bindings
                  (dimensionAt frame.owners) index) reference)) logical ref) := by
        funext logical ref
        unfold action
        apply Qleisli.Exact.sum_map_congr
        intro digit present
        have digitBound : digit < actual.layout.labels.length := by
          rw [← inputShape]
          exact List.mem_range.mp present
        rw [target_fibre_canonical frame bound.binding member actual spectators kept joint base digit ref digitBound]
      rw [fibres] at law
      rw [← inputShape] at law
      exact law

#print axioms actual_occurrence_canonical_input_action

end Qleisli.RuntimeNamedHeadCoefficients
