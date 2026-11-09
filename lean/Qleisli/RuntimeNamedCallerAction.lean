import Qleisli.RuntimeNamedHeadCoefficients
import Qleisli.RuntimeNamedCallerGeometry
import Qleisli.RuntimeNamedThreeRoot
import Qleisli.RuntimeNamedThreeFlow

/-! Complete caller-state action for the same original single-primitive call.
True owner cardinalities, arbitrary correlated spectators/references and actual
returned source order are retained. General body/instrument coverage is separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeNamedCallerAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.RuntimeForestOrderedProduct
open Qleisli.RuntimeForestRegroup Qleisli.MixedRadix
open Qleisli.RuntimeNamedHeadCoefficients

noncomputable def canonicalJoint {Reference : Type} {roles state checked}
    (frame : @Frame roles state checked) (target : Binding)
    (joint : Nat → Reference → Complex) (logical : Nat) (reference : Reference) : Complex :=
  joint (recode (target::checked.bindings.erase target) checked.bindings
    (dimensionAt frame.owners) logical) reference

/-- The logical update uses the actual source operator and original ordered
owner cardinalities. No physical or joined caller matrix is reconstructed. -/
noncomputable def updatedJoint {Reference : Type}
    {inputRoles outputRoles before after inputChecked outputChecked}
    (input : @Frame inputRoles before inputChecked) (output : @Frame outputRoles after outputChecked)
    (inputTarget outputTarget : Binding) (operator : Matrix) (joint : Nat → Reference → Complex)
    (logical : Nat) (reference : Reference) : Complex :=
  applyHead operator (canonicalJoint input inputTarget joint)
    (regroupIndex output (outputTarget::outputChecked.bindings.erase outputTarget) logical) reference

theorem updated_output_encoding {Reference : Type}
    {inputRoles outputRoles before after inputChecked outputChecked}
    (input : @Frame inputRoles before inputChecked) (output : @Frame outputRoles after outputChecked)
    (inputTarget outputTarget : Binding) (member : outputTarget ∈ outputChecked.bindings)
    (actual : OwnerCode outputTarget) (spectators : OwnerCodes (outputChecked.bindings.erase outputTarget))
    (kept : reindex output.owners (outputTarget::outputChecked.bindings.erase outputTarget) =
      some (.cons actual spectators))
    (native operator : Matrix) (read : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨outputTarget.port,outputTarget.owner.basis⟩]) native)
    (joint : Nat → Reference → Complex) (physical : Nat) (reference : Reference) :
    referenceAction output (updatedJoint input output inputTarget outputTarget operator joint) physical reference =
      headEncoding native (sparseProduct spectators).dimension
        (fun high => coefficients after.quantum.frame spectators physical high)
        (applyHead operator (canonicalJoint input inputTarget joint))
        (gather physical (outputTarget.port.wires.map after.quantum.frame.idxOf)) reference := by
  have permutation := (List.perm_cons_erase member).symm
  have nativeCode := RuntimeNamedInputAction.singleton_encoding actual native read
  have law := frame_head_encoding output outputTarget _ actual spectators kept permutation
    (updatedJoint input output inputTarget outputTarget operator joint) physical reference
  rw [← nativeCode] at law
  refine law.trans ?_
  unfold headEncoding
  apply Qleisli.Exact.sum_map_congr
  intro logical present
  have bound : logical < (sparseProduct (.cons actual spectators)).dimension := by
    have small := List.mem_range.mp present
    rw [nativeCode] at small
    exact small
  dsimp only [updatedJoint]
  rw [regroup_reverse output _ ⟨.cons actual spectators,kept⟩ permutation logical bound]

/-- Same original gather, restricted to its actual finite physical rows. -/
theorem gather_range (label n : Nat) : gather label (List.range n) = label % 2^n := by
  induction n with
  | zero => simp only [gather,List.range_zero,List.zipIdx_nil,List.map_nil,List.sum_nil,Nat.pow_zero]; omega
  | succ n ih =>
    simp only [gather,List.range_succ,List.zipIdx_append,List.length_range,
      Nat.zero_add,List.zipIdx_cons,List.zipIdx_nil,List.map_append,List.map_cons,
      List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
    change gather label (List.range n) + bit label n * 2^n = label % 2^(n+1)
    rw [ih,Nat.pow_succ,Nat.mod_mul]
    simp [bit,Nat.mul_comm]

theorem self_indices (wires : List Nat) (distinct : wires.Nodup) :
    wires.map wires.idxOf = List.range wires.length := by
  induction wires with
  | nil => rfl
  | cons w rest ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
    rw [List.map_cons,List.idxOf_cons_self,List.length_cons,List.range_succ_eq_map,← ih tail,List.map_map]
    apply congrArg (List.cons 0)
    apply List.map_eq_map_iff.mpr
    intro v member
    have different : w ≠ v := fun same => fresh (same.symm ▸ member)
    simp [different]

/-- The final local reorder can be removed ONLY on the actual finite rows;
there is no assertion on arbitrary Nat amplitudes outside that domain. -/
theorem reorder_self (dependencies : List Semantics.Finite.Dependency) (wires : List Nat)
    (distinct : wires.Nodup) (values : Nat → Complex) (row : Nat) (bound : row < 2^wires.length) :
    Qleisli.Semantics.RawAction.event dependencies
      (.reorder wires.length (wires.map wires.idxOf)) values row = values row := by
  rw [self_indices wires distinct]
  calc
    _ = ((List.range (2^wires.length)).map fun input => if row = input then values input else 0).sum := by
      unfold Qleisli.Semantics.RawAction.event
      apply Qleisli.Exact.sum_map_congr
      intro input member
      rw [gather_range]
      simp only [Nat.mod_eq_of_lt (List.mem_range.mp member)]
      by_cases same : input = row
      · subst row; simp
      · simp [same,Ne.symm same]
    _ = _ := Qleisli.Exact.range_delta_sum _ _ values bound

#print axioms updated_output_encoding
#print axioms reorder_self

/-- Finish a real one-owner action in the caller's complete returned frame.
The local action is used only on finite rows. The original spectator bindings
and wire order supply the remaining coefficient equality. -/
theorem whole_caller_of_head_action
    {dependencies inputRoles outputRoles before after inputChecked outputChecked}
    (input : @Frame inputRoles before inputChecked) (output : @Frame outputRoles after outputChecked)
    (target returned : Binding) (returnedMember : returned ∈ outputChecked.bindings)
    (inputSpectators : OwnerCodes (inputChecked.bindings.erase target))
    (spectators : outputChecked.bindings.erase returned = inputChecked.bindings.erase target)
    (frames : after.quantum.frame = before.quantum.frame) (wires : returned.port.wires = target.port.wires)
    (unique : (RuntimeNamedGateLift.portAxes before.quantum target.port).Nodup)
    (native operator : Matrix) (nativeRead : RuntimeInterval.Computed
      (Carrier.ownerCode [⟨returned.port,returned.owner.basis⟩]) native)
    (events : List Semantics.Raw.Event)
    (localLaw : ∀ {Reference : Type} (joint : Nat → Reference → Complex) base row reference,
      row < native.rows →
      Qleisli.Semantics.RawAction.event dependencies
          (.reorder target.port.wires.length (target.port.wires.map target.port.wires.idxOf))
          (fun value => Qleisli.Semantics.RawAction.events dependencies events
            (fun label => referenceAction input joint label reference)
            (scatter base (RuntimeNamedGateLift.portAxes before.quantum target.port) value)) row =
        headEncoding native (sparseProduct inputSpectators).dimension
          (fun high => coefficients before.quantum.frame inputSpectators base high)
          (applyHead operator (canonicalJoint input target joint)) row reference) :
    ∀ {Reference : Type} (joint : Nat → Reference → Complex) physical reference,
      Qleisli.Semantics.RawAction.events dependencies events
          (fun label => referenceAction input joint label reference) physical =
        referenceAction output (updatedJoint input output target returned operator joint) physical reference := by
  have permutation := (List.perm_cons_erase returnedMember).symm
  obtain ⟨all,kept⟩ := reindex_exists output.owners (returned::outputChecked.bindings.erase returned) permutation.subset
  cases all with
  | cons actual outputSpectators =>
    intro Reference joint physical reference
    have shared := RuntimeNamedCallerGeometry.codes_same spectators.symm
      inputSpectators outputSpectators before.quantum.frame after.quantum.frame frames
    let axes := RuntimeNamedGateLift.portAxes before.quantum target.port
    have outputAxes : returned.port.wires.map after.quantum.frame.idxOf = axes := by
      rw [wires,frames]
      rfl
    have code := RuntimeNamedInputAction.singleton_encoding actual native nativeRead
    have physicalRows : native.rows = 2^target.port.wires.length := by
      calc
        _ = 2^actual.layout.bits := by rw [code]; rfl
        _ = 2^returned.port.wires.length := congrArg (fun n : Nat => 2^n) actual.reference.2.2.symm
        _ = _ := congrArg (fun ws : List Nat => 2^ws.length) wires
    have small : gather physical axes < 2^target.port.wires.length := by
      simpa only [axes,RuntimeNamedGateLift.portAxes,List.length_map] using gather_bound physical axes
    have wireUnique : target.port.wires.Nodup :=
      List.Pairwise.of_map before.quantum.frame.idxOf
        (fun _ _ different same => different (congrArg before.quantum.frame.idxOf same)) unique
    have law := localLaw joint physical (gather physical axes) reference (by rwa [physicalRows])
    rw [reorder_self dependencies target.port.wires wireUnique _ _ small,
      RuntimeScatterTransport.scatter_gather physical _ unique] at law
    have encoded := updated_output_encoding input output target returned returnedMember actual
      outputSpectators kept native operator nativeRead joint physical reference
    have coefficientsSame :
        (fun high => coefficients after.quantum.frame outputSpectators physical high) =
        (fun high => coefficients before.quantum.frame inputSpectators physical high) := by
      funext high
      exact (shared.2 physical high).symm
    rw [← shared.1,coefficientsSame,outputAxes] at encoded
    exact law.trans encoded.symm

#print axioms whole_caller_of_head_action

def WholeCallerAction {dependencies program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence dependencies program block step)
    (events : List Semantics.Raw.Event) : Prop :=
  match held with
  | .named (before := before) (scope := scope) (boundary := boundary) (action := primitive) _ bound =>
    ∀ {roles} (checked : RuntimeOwnerMap.Checked roles scope.interval.before) (input : Frame checked),
      checked.bindings = before.bindings →
      ∀ output : Frame boundary.afterFrame,
        ∃ returned : Binding, boundary.mapped = [returned] ∧
          ∀ {Reference : Type} (joint : Nat → Reference → Complex) physical reference,
            Qleisli.Semantics.RawAction.events dependencies events
                (fun value => referenceAction input joint value reference) physical =
              referenceAction output
                (updatedJoint input output bound.binding returned primitive.expected joint) physical reference

/-- Exact complete-caller action for this real source primitive invocation.
All surrounding owners, nominal code padding, phase and external references
remain. This is not yet induction for arbitrary source bodies or instruments. -/
theorem actual_whole_caller_action {artifact root execution fuel program block step}
    (held : @RuntimeNamedPrimitiveOccurrence.Occurrence root.dependencies program block step)
    (call : RuntimeNamedChildRuns.ChildRun artifact root execution
      (RuntimePureBody.runBlockCore artifact root execution (fuel+1)) step)
    (events : List Semantics.Raw.Event) (on : RuntimeNamedOccurrenceAction.On held events) :
    WholeCallerAction held events := by
  have actionLaw := actual_occurrence_canonical_input_action held call events on
  have geometry := RuntimeNamedCallerGeometry.actual_geometry held call events on
  have outputCodes := RuntimeNamedPrimitiveOutputs.actual_occurrence_output_code held call
  cases held with
  | @named start count tokens sources caller before childHistory childRetired ordinary first size inputToken outputToken role kind
      event scope body read boundary finalOrdinary primitive original bound =>
    intro roles checked input same output
    obtain ⟨inputActual,inputSpectators,inputKept,localLaw⟩ := actionLaw checked input same
    obtain ⟨returned,mapped,returnedMember,nativeRead⟩ := outputCodes
    obtain ⟨geometricReturn,geometricMap,_basis,wires,frames,spectators⟩ := geometry checked same
    have selectedReturn : geometricReturn = returned := (List.cons.inj (geometricMap.symm.trans mapped)).1
    subst geometricReturn
    have selected : scope.selected = [bound.binding.port] :=
      (RuntimeNamedFrameAxes.mixed_bound_ports scope boundary).trans
        (congrArg (List.map RuntimeOwnerMap.Binding.port) bound.singleton)
    have axes : RuntimeNamedFrameAxes.mixedAxes scope =
        RuntimeNamedGateLift.portAxes scope.interval.before.quantum bound.binding.port := by
      change (scope.selected.flatMap (·.wires)).map scope.interval.before.quantum.frame.idxOf = _
      simpa only [List.flatMap_singleton] using
        congrArg (fun ports : List Semantics.Raw.Port =>
          (ports.flatMap (·.wires)).map scope.interval.before.quantum.frame.idxOf) selected
    have unique := (RuntimeNamedFrameAxes.mixedAxes_bounds scope).1
    rw [axes] at unique localLaw
    refine ⟨returned,mapped,whole_caller_of_head_action input output bound.binding returned returnedMember
      inputSpectators spectators frames wires unique primitive.outputCode primitive.expected nativeRead events ?_⟩
    intro Reference joint base row reference small
    exact localLaw joint base row reference (by rwa [primitive.action.physicalShape.2])

#print axioms actual_whole_caller_action

/-- Both outside calls use their real child executions and the very event
lists obtained from the original parent body. The middle selection and final
root permutation stay attached to that same decomposition. This bounded
three-call view does not establish arbitrary-body or public-path coverage. -/
theorem original_pre_post_actions {artifact owner name arguments request prepared order runtime}
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
      WholeCallerAction view.prePrimitive a ∧
      RuntimeNamedSelectionOn.On b view.centerSelection held ∧
      WholeCallerAction view.postPrimitive c := by
  intro held pre center post starts next last covers
  obtain ⟨a,b,c,whole,preOn,centerOn,postOn⟩ :=
    RuntimeNamedThreeRoot.original_body body view coverage starts next last covers
  have calls := RuntimeNamedSourceFlow.original_child_runs body view
  exact ⟨a,b,c,whole,
    actual_whole_caller_action view.prePrimitive calls.1 a preOn,centerOn,
    actual_whole_caller_action view.postPrimitive calls.2.2 c postOn⟩

#print axioms original_pre_post_actions

end Qleisli.RuntimeNamedCallerAction
