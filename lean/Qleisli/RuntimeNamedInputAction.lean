import Qleisli.RuntimeNamedPrimitiveInputs
import Qleisli.RuntimeNamedThreeRoot
import Qleisli.RuntimeNamedOccurrenceAction
import Qleisli.RuntimeNamedPrimitiveSourceLift
import Qleisli.RuntimeFiniteTargetFibre

/-! Connect a complete original owner-forest encoding
to the existing local named primitive action's spectator/reference fibre.
No native read, budget, source-body preservation or acceptance is fabricated.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeNamedInputAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open RuntimeOwnerMap (Binding)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct
open Qleisli.RuntimeForestRegroup Qleisli.RuntimeFiniteTargetFibre

/-- Complete owner maps use the authentic Raw frame's exclusive coordinates.
This uses neither physical width as logical identity nor separability. -/
theorem axes_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (valid : Raw.stateValid state.quantum = true) :
    (forestAxes state.quantum.frame checked.bindings).Nodup := by
  have facts := Raw.Ownership.valid _ valid
  have ports := List.Perm.flatMap_right (fun port : Semantics.Raw.Port => port.wires)
    checked.complete
  have unique : (checked.bindings.flatMap (fun binding => binding.port.wires)).Nodup := by
    simpa only [List.flatMap_map] using ports.symm.nodup facts.exclusive
  have covered (wire : Nat) (member : wire ∈ checked.bindings.flatMap (fun binding => binding.port.wires)) :
      wire ∈ state.quantum.frame :=
    facts.covered wire (ports.mem_iff.mp (by simpa only [List.flatMap_map] using member))
  unfold forestAxes
  exact List.Nodup.map_on (fun wire member _ _ equal => (List.idxOf_inj (covered wire member)).mp equal) unique

theorem spectator_scatter {roles state checked} (frame : @Frame roles state checked)
    (valid : Raw.stateValid state.quantum = true) (target : Binding)
    (member : target ∈ checked.bindings) (physical replacement logical : Nat) :
    spectatorCoefficient frame target
        (scatter physical (target.port.wires.map state.quantum.frame.idxOf) replacement) logical =
      spectatorCoefficient frame target physical logical := by
  have unique : checked.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
      checked.tokensDistinct
  have allAxes : (checked.bindings.flatMap
      (fun binding => binding.port.wires.map state.quantum.frame.idxOf)).Nodup := by
    simpa only [forestAxes,List.map_flatMap] using axes_unique checked valid
  unfold spectatorCoefficient
  apply congrArg List.prod
  apply List.map_congr_left
  intro binding present
  have retained := unique.mem_erase_iff.mp present
  obtain ⟨actual,_read⟩ := lookup_exists frame.owners binding retained.2
  have disjoint := List.Pairwise.forall (fun _ _ separate => separate.symm)
    (List.nodup_flatMap.mp allAxes).2 retained.2 member retained.1
  rw [factorAt_eq _ _ _ _ retained.2 actual,factorAt_eq _ _ _ _ retained.2 actual,
    Qleisli.RuntimeTargetScatter.gather_disjoint physical replacement _ _ disjoint]

theorem fibre_scatter {Reference : Type} {roles state checked} (frame : @Frame roles state checked)
    (valid : Raw.stateValid state.quantum = true) (target : Binding)
    (member : target ∈ checked.bindings) (joint : Nat → Reference → ℂ)
    (physical replacement digit : Nat) (reference : Reference) :
    targetFibre frame target (scatter physical (target.port.wires.map state.quantum.frame.idxOf) replacement)
        joint digit reference =
      targetFibre frame target physical joint digit reference := by
  unfold targetFibre
  apply Qleisli.Exact.sum_map_congr
  intro logical _present
  rw [spectator_scatter frame valid target member physical replacement logical]

/-- The complete authentic encoding is exactly a local rectangular owner code
with a spectator/reference fibre. The fibre is constructed from every other
owner's original encoding; arbitrary correlated joint amplitudes are retained. -/
theorem complete_encoding {Reference : Type} {roles state checked} (frame : @Frame roles state checked)
    (valid : Raw.stateValid state.quantum = true) (target : Binding)
    (member : target ∈ checked.bindings) (actual : OwnerCode target)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction frame joint physical reference =
      RuntimeNamedPrimitiveSourceLift.encodedParent
        (target.port.wires.map state.quantum.frame.idxOf)
        (Semantics.FiniteCarrier.encoding actual.layout)
        (fun digit environment ref => targetFibre frame target environment joint digit ref)
        physical reference := by
  rw [fibre_code_action frame target member actual joint physical reference]
  unfold RuntimeNamedPrimitiveSourceLift.encodedParent action
  apply Qleisli.Exact.sum_map_congr
  intro digit _present
  dsimp only
  rw [fibre_scatter frame valid target member joint physical 0 digit reference]

/-- A real interval-prefix computation supplies the complete geometry above;
callers need no new validity assertion or encoded-state premise. -/
theorem original_interval_encoding {Reference : Type}
    {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (checked : RuntimeOwnerMap.Checked roles interval.before) (frame : Frame checked)
    (target : Binding) (member : target ∈ checked.bindings) (actual : OwnerCode target)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction frame joint physical reference =
      RuntimeNamedPrimitiveSourceLift.encodedParent
        (target.port.wires.map interval.before.quantum.frame.idxOf)
        (Semantics.FiniteCarrier.encoding actual.layout)
        (fun digit environment ref => targetFibre frame target environment joint digit ref)
        physical reference := by
  obtain ⟨work,left,read⟩ := interval.prefixRead
  exact complete_encoding frame
    (Raw.Observation.checkOps_invariants _ _ _ _ _ work left read).1 target member actual joint physical reference

/-- The retained native singleton read has exactly this original owner's
independent encoding. No matrix equation is supplied by the producer. -/
theorem singleton_encoding {target : Binding} (actual : OwnerCode target) (native : Matrix)
    (read : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨target.port,target.owner.basis⟩]) native) :
    native = Semantics.FiniteCarrier.encoding actual.layout := by
  obtain ⟨work,left,ran⟩ := read
  obtain ⟨⟨codeBefore,codeAfter,codeRead⟩,_owners⟩ := Carrier.ownerCode_conditions _ _ work left ran
  obtain ⟨layout,_gramBefore,_gramAfter,original,equal,_gram⟩ :=
    QleisliKernel.FiniteCarrier.code_conditions _ _ codeBefore codeAfter codeRead
  have same : layout = actual.layout := Option.some.inj (original.symm.trans actual.reference.1)
  exact equal.trans (congrArg Semantics.FiniteCarrier.encoding same)

theorem original_native_encoding {Reference : Type}
    {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (checked : RuntimeOwnerMap.Checked roles interval.before) (frame : Frame checked)
    (target : Binding) (member : target ∈ checked.bindings) (actual : OwnerCode target)
    (native : Matrix) (read : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨target.port,target.owner.basis⟩]) native)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction frame joint physical reference =
      RuntimeNamedPrimitiveSourceLift.encodedParent
        (target.port.wires.map interval.before.quantum.frame.idxOf) native
        (fun digit environment ref => targetFibre frame target environment joint digit ref)
        physical reference := by
  rw [singleton_encoding actual native read]
  exact original_interval_encoding interval checked frame target member actual joint physical reference

/-- Substitute the complete original caller encoding into the genuine named
primitive's local source-action law. The carrier equality retains full ports
and basis trees; its native encoding is derived from the actual primitive read.
The conclusion retains the existing explicit final local reorder. Proving the
source-indexed carrier equality and transporting the resulting output fibre
to the caller's final source order remain the enclosing body's obligations. -/
theorem primitive_input_lift {Reference : Type}
    {dependencies program block start count inputs ordinary effect}
    (scope : @RuntimeCallScope.Checked dependencies program block start count inputs ordinary effect)
    (portBinding : Binding) (form : RuntimeNamedGateLift.Form) (output : Nat)
    {primitiveStart primitiveCount primitiveInput primitiveOutput role kind}
    (primitive : RuntimePrimitiveAction.Checked scope.prepared.block primitiveStart primitiveCount
      primitiveInput primitiveOutput role kind)
    (binding : RuntimePrimitiveSource.Checked primitive)
    (parentEvents : List Semantics.Raw.Event)
    (lifted : RuntimeNamedPrimitiveSourceLift.MixedActionOn scope portBinding form output primitive binding parentEvents)
    {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (frame : Frame checked)
    (target : Binding) (member : target ∈ checked.bindings) (actual : OwnerCode target)
    (sameCarriers : (primitive.interval.selected.map fun port =>
      (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) = [⟨target.port,target.owner.basis⟩])
    (sameAxes : RuntimeNamedFrameAxes.mixedAxes scope =
      target.port.wires.map scope.interval.before.quantum.frame.idxOf)
    (joint : Nat → Reference → ℂ) (base row : Nat) (reference : Reference)
    (bound : row < primitive.physical.rows) :
    Qleisli.Semantics.RawAction.event dependencies
        (.reorder portBinding.port.wires.length (portBinding.port.wires.map portBinding.port.wires.idxOf))
        (fun value => Qleisli.Semantics.RawAction.events dependencies parentEvents
          (fun input => referenceAction frame joint input reference)
          (scatter base (RuntimeNamedFrameAxes.mixedAxes scope) value)) row =
      action primitive.outputCode
        (fun logical ref => action primitive.expected (targetFibre frame target base joint) logical ref)
        row reference := by
  have inputRead := primitive.inputRead
  rw [sameCarriers] at inputRead
  have encoded (physical : Nat) (ref : Reference) :=
    original_native_encoding scope.interval checked frame target member actual primitive.inputCode inputRead
      joint physical ref
  rw [← sameAxes] at encoded
  obtain ⟨_childEvents,_facts,_meaning,law⟩ := lifted
  have actualLaw := law (fun digit environment ref => targetFibre frame target environment joint digit ref)
    base row reference bound
  have sameInput :
      (fun input => RuntimeNamedPrimitiveSourceLift.encodedParent (RuntimeNamedFrameAxes.mixedAxes scope)
        primitive.inputCode (fun digit environment ref => targetFibre frame target environment joint digit ref)
        input reference) = (fun input => referenceAction frame joint input reference) := by
    funext input
    exact (encoded input reference).symm
  rw [sameInput] at actualLaw
  have sameSlice : RuntimeNamedPrimitiveSourceLift.sourceSlice (RuntimeNamedFrameAxes.mixedAxes scope) base
        (fun digit environment ref => targetFibre frame target environment joint digit ref) =
      targetFibre frame target base joint := by
    funext digit ref
    unfold RuntimeNamedPrimitiveSourceLift.sourceSlice
    rw [sameAxes]
    obtain ⟨work,left,read⟩ := scope.interval.prefixRead
    exact fibre_scatter frame (Raw.Observation.checkOps_invariants _ _ _ _ _ work left read).1
      target member joint base 0 digit ref
  rw [sameSlice] at actualLaw
  exact actualLaw

#print axioms complete_encoding
#print axioms original_interval_encoding
#print axioms primitive_input_lift
end Qleisli.RuntimeNamedInputAction

namespace Qleisli.RuntimeNamedInputAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.RuntimeForestProduct Qleisli.RuntimeFiniteTargetFibre
open Qleisli.Semantics.Exact Qleisli.RuntimeNamedPrimitiveInputs

def OccurrenceWholeInput {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (events : List Semantics.Raw.Event) : Prop :=
  match held with
  | .named (before := before) (scope := scope) (action := primitive) _ bound =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (frame : Frame checked),
      checked.bindings = before.bindings → ∀ {Reference : Type} (joint : Nat → Reference → ℂ)
      (base row : Nat) (reference : Reference), row < primitive.physical.rows →
      Qleisli.Semantics.RawAction.event dependencies
          (.reorder bound.binding.port.wires.length (bound.binding.port.wires.map bound.binding.port.wires.idxOf))
          (fun value => Qleisli.Semantics.RawAction.events dependencies events
            (fun input => referenceAction frame joint input reference)
            (scatter base (RuntimeNamedFrameAxes.mixedAxes scope) value)) row =
        action primitive.outputCode
          (fun logical ref => action primitive.expected (targetFibre frame bound.binding base joint) logical ref)
          row reference

/-- The actual source-child input law removes the supplied carrier/axis
equations from the complete-encoding action consumer. Input fibres come from
the same caller's full original map and all reference states remain arbitrary.
The final local reorder and output-code obligation remain explicit. -/
theorem original_input_action {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (inputs : OccurrenceInput held) (events : List Semantics.Raw.Event)
    (lifted : RuntimeNamedOccurrenceAction.On held events) : OccurrenceWholeInput held events := by
  cases held with
  | @named _ _ _ _ _ _ _ _ _ _ _ input output _ _ _ scope _ _ boundary _ _ original bound =>
    intro roles checked frame same Reference joint base row ref small
    have ordered := RuntimeSelectionPartition.order_values _ _ _ boundary.input.orderRead
    have member : bound.binding ∈ checked.bindings := by
      rw [same]
      apply ordered.1
      exact (congrArg (fun bindings => bound.binding ∈ bindings) bound.singleton).mpr
        (List.mem_singleton_self _)
    obtain ⟨actual,_read⟩ := lookup_exists frame.owners bound.binding member
    refine primitive_input_lift scope bound.binding _ output _ original events lifted checked frame
      bound.binding member actual ?_ ?_ joint base row ref small
    · simpa only [OccurrenceInput,bound.singleton,carrierOwners,List.map_singleton] using inputs
    · have selected : scope.selected = [bound.binding.port] :=
        (RuntimeNamedFrameAxes.mixed_bound_ports scope boundary).trans
          (congrArg (List.map RuntimeOwnerMap.Binding.port) bound.singleton)
      change (scope.selected.flatMap (·.wires)).map scope.interval.before.quantum.frame.idxOf =
        bound.binding.port.wires.map scope.interval.before.quantum.frame.idxOf
      simpa only [List.flatMap_singleton] using congrArg (fun ports : List Semantics.Raw.Port =>
        (ports.flatMap (·.wires)).map scope.interval.before.quantum.frame.idxOf) selected

/-- Apply the derived source input laws to the very pre/post event slices of
the original three-call root. The center keeps its existing exact local law;
the root retains its complete instrument history and final reorder. Joining
the calls' output/input source encodings remains a separate obligation. -/
theorem original_pre_post_input_actions {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    (view : RuntimeNamedThreeOccurrence.Three body.checked.result.steps)
    (coverage : RuntimeNamedSelectionOn.Coverage view.centerSelection
      (RuntimeNamedThreeOccurrence.actual_body_middle body view)) :
    let held := RuntimeNamedThreeOccurrence.actual_body_middle body view
    let pre := RuntimeNamedOccurrenceAction.span view.prePrimitive
    let center := RuntimeNamedSelectionOn.middle view.centerSelection held coverage
    let post := RuntimeNamedOccurrenceAction.span view.postPrimitive
    pre.start = 0 → center.start = pre.start+pre.count → post.start = center.start+center.count →
    pre.count+center.count+post.count = body.root.program.operations.length →
    ∃ a b c, RuntimeNamedThreeRoot.Whole body.checked.native pre center post a b c ∧
      OccurrenceWholeInput view.prePrimitive a ∧ RuntimeNamedSelectionOn.On b view.centerSelection held ∧
      OccurrenceWholeInput view.postPrimitive c := by
  intro held pre center post starts next last covers
  obtain ⟨a,b,c,whole,preAction,centerAction,postAction⟩ :=
    RuntimeNamedThreeRoot.original_body body view coverage starts next last covers
  obtain ⟨preInput,postInput⟩ := RuntimeNamedPrimitiveInputs.original_pre_post_inputs body view
  exact ⟨a,b,c,whole,original_input_action view.prePrimitive preInput a preAction,centerAction,
    original_input_action view.postPrimitive postInput c postAction⟩

#print axioms original_pre_post_input_actions
#print axioms original_input_action
end Qleisli.RuntimeNamedInputAction
