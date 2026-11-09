import Qleisli.RuntimeSemanticForest
import Qleisli.RuntimeNamedCallerAction
import Qleisli.RuntimeLiteralNamedPrimitive

/-! Apply an original one-owner action in a complete sparse source frame.
Only the operated ports use the already checked native codes. Spectators and
external references keep the original joint amplitudes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSparseHeadAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite (gather scatter)
open QleisliKernel.Semantics.Exact (Matrix)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (forestAxes embed sparseEntry tensor_agrees ofLayout_agrees)
open Qleisli.RuntimeSemanticForest (Frame action ownerLayout owner_layout product product_agrees frame_exists regroup_action)
open Qleisli.RuntimeForestProduct (layout_bounds gather_append gather_bound)
open Qleisli.RuntimeForestOrderedProduct (agrees_entry layout_tensor_coefficient)
open Qleisli.RuntimeNamedHeadCoefficients
  (headEncoding head_code_action head_operator_encoding fibre applyHead)
open Qleisli.RuntimeNamedPrimitiveSourceLift (encodedParent sourceSlice)
open Qleisli.RuntimeNamedGateLift (portAxes)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.RuntimeLiteralHistory (applySourceOwner)
open Qleisli.Semantics.Exact (scalar entry)
open Qleisli.MixedRadix (recode)
open Semantics.FiniteCarrier (layout tensor encoding)

private noncomputable def spectatorEntry (bindings : Map) (physicalFrame : List Nat)
    (physical logical : Nat) : ℂ :=
  scalar (sparseEntry (.ofLayout (product bindings)) (gather physical (forestAxes physicalFrame bindings)) logical)

/-- Split off the exact leading source owner without building a dense code
for the ordered spectators or assuming an independent spectator state. -/
theorem canonical_encoding {head : Binding} {tail : Map} (frame : Frame (head::tail))
    (physicalFrame : List Nat) {Reference : Type} (joint : Nat → Reference → ℂ)
    (physical : Nat) (reference : Reference) :
    action frame physicalFrame joint physical reference =
      headEncoding (encoding (ownerLayout head)) (product tail).labels.length
        (spectatorEntry tail physicalFrame physical) joint
        (gather physical (head.port.wires.map physicalFrame.idxOf)) reference := by
  obtain ⟨read,width⟩ := owner_layout (frame.available head List.mem_cons_self)
  let left := ownerLayout head
  let right := product tail
  let lowAxes := head.port.wires.map physicalFrame.idxOf
  let highAxes := forestAxes physicalFrame tail
  let low := gather physical lowAxes
  let high := gather physical highAxes
  have bounds := layout_bounds _ _ read
  have lowBound : low < 2^left.bits := by simpa only [low,lowAxes,List.length_map,width] using gather_bound physical lowAxes
  have same := product_agrees frame
  change RuntimeForestCode.Agrees frame.code (tensor left right) at same
  have dimension : frame.code.dimension = left.labels.length * right.labels.length :=
    same.dimension.trans (tensor_agrees (ofLayout_agrees left) (ofLayout_agrees right)).dimension.symm
  have axes : forestAxes physicalFrame (head::tail) = lowAxes ++ highAxes := by
    simp only [forestAxes,List.flatMap_cons,List.map_append,lowAxes,highAxes]
  unfold action headEncoding
  change ((List.range frame.code.dimension).map _).sum =
    ((List.range (left.labels.length * right.labels.length)).map _).sum
  rw [dimension]
  apply Qleisli.Exact.sum_map_congr
  intro logical _
  unfold embed
  rw [agrees_entry same,axes,gather_append]
  have lowWidth : lowAxes.length = left.bits := (List.length_map _).trans width
  rw [lowWidth]
  rw [layout_tensor_coefficient left right bounds low high logical lowBound]
  rw [(ofLayout_agrees left).encodingEntry low (logical % left.labels.length) lowBound
    (Nat.mod_lt logical bounds.1)]
  unfold entry spectatorEntry
  change _ = scalar ((encoding left).entry low (logical % left.labels.length)) *
    (scalar (sparseEntry (.ofLayout right) high (logical / left.labels.length)) * joint logical reference)
  ring

private theorem singleton_from_code {binding : Binding} {native : Matrix}
    (read : RuntimeInterval.Computed (Carrier.ownerCode [⟨binding.port,binding.owner.basis⟩]) native) :
    Nonempty (RuntimeStructuralLayoutEvidence.SemanticOwnerLayout binding) ∧
      native = encoding (ownerLayout binding) := by
  obtain ⟨work,left,performed⟩ := read
  obtain ⟨⟨start,finish,codeRead⟩,owners⟩ := Carrier.ownerCode_conditions _ _ work left performed
  obtain ⟨owner,ownerRead,bitWidth,wireWidth⟩ := owners _ List.mem_cons_self
  have available : Nonempty (RuntimeStructuralLayoutEvidence.SemanticOwnerLayout binding) :=
    ⟨⟨owner,ownerRead,bitWidth,wireWidth⟩⟩
  obtain ⟨actual,_,_,original,same,_⟩ :=
    QleisliKernel.FiniteCarrier.code_conditions _ _ start finish codeRead
  exact ⟨available,same.trans (congrArg encoding
    (Option.some.inj (original.symm.trans (owner_layout available).1)))⟩

private theorem bindings_unique {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    checked.bindings.Nodup :=
  List.Pairwise.of_map (fun binding : Binding => binding.port.token)
    (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same))
    checked.tokensDistinct

private theorem source_dimensions {first second : Map} (order : first.Perm second) :
    sourceDimension first = sourceDimension second := by
  funext binding
  by_cases member : binding ∈ first
  · simp only [sourceDimension,if_pos member,if_pos (order.mem_iff.mp member)]
  · simp only [sourceDimension,if_neg member,if_neg (fun found => member (order.mem_iff.mpr found))]

/-- The same original local CodeSpace action determines the full caller
action with sparse spectators. The input/output singleton code reads belong
to the actual local operation and the output is reindexed in source order. -/
theorem whole_action {dependencies inputRoles outputRoles before after}
    (inputChecked : RuntimeOwnerMap.Checked inputRoles before)
    (outputChecked : RuntimeOwnerMap.Checked outputRoles after)
    (input : Frame inputChecked.bindings) (valid : Raw.stateValid before.quantum = true)
    (target returned : Binding) (targetMember : target ∈ inputChecked.bindings)
    (returnedMember : returned ∈ outputChecked.bindings)
    (spectators : outputChecked.bindings.erase returned = inputChecked.bindings.erase target)
    (frames : after.quantum.frame = before.quantum.frame) (wires : returned.port.wires = target.port.wires)
    (inputCode outputCode matrix : Matrix)
    (inputRead : RuntimeInterval.Computed (Carrier.ownerCode [⟨target.port,target.owner.basis⟩]) inputCode)
    (outputRead : RuntimeInterval.Computed (Carrier.ownerCode [⟨returned.port,returned.owner.basis⟩]) outputCode)
    (inputShape : matrix.cols = inputCode.cols) (outputShape : matrix.rows = outputCode.cols)
    (events : List Semantics.Raw.Event)
    (localLaw : ∀ {Reference : Type} (joint : Nat → Nat → Reference → ℂ) base row reference,
      row < outputCode.rows →
      Qleisli.Semantics.RawAction.event dependencies
        (.reorder target.port.wires.length (target.port.wires.map target.port.wires.idxOf))
        (fun value => Qleisli.Semantics.RawAction.events dependencies events
          (fun physical => encodedParent (portAxes before.quantum target.port) inputCode joint physical reference)
          (scatter base (portAxes before.quantum target.port) value)) row =
      Qleisli.Semantics.Exact.action outputCode
        (fun digit ref => Qleisli.Semantics.Exact.action matrix
          (sourceSlice (portAxes before.quantum target.port) base joint) digit ref) row reference) :
    ∃ output : Frame outputChecked.bindings,
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) physical reference,
      Qleisli.Semantics.RawAction.events dependencies events
        (fun row => action input before.quantum.frame joint row reference) physical =
      action output after.quantum.frame
        (applySourceOwner inputChecked.bindings outputChecked.bindings target returned matrix joint) physical reference := by
  let rest := inputChecked.bindings.erase target
  let canonicalIn := target::rest
  let canonicalOut := returned::outputChecked.bindings.erase returned
  let axes := portAxes before.quantum target.port
  let otherAxes := forestAxes before.quantum.frame rest
  have beforeOrder : inputChecked.bindings.Perm canonicalIn := List.perm_cons_erase targetMember
  have afterOrder : outputChecked.bindings.Perm canonicalOut := List.perm_cons_erase returnedMember
  obtain ⟨orderedIn⟩ := frame_exists (fun binding member => input.available binding (beforeOrder.symm.subset member))
  obtain ⟨_,nativeIn⟩ := singleton_from_code inputRead
  obtain ⟨returnedLayout,nativeOut⟩ := singleton_from_code outputRead
  have available : Qleisli.RuntimeSemanticForest.Available canonicalOut := by
    intro binding member
    rcases List.mem_cons.mp member with rfl | spectator
    · exact returnedLayout
    · exact input.available binding (List.erase_subset (spectators ▸ spectator))
  obtain ⟨orderedOut⟩ := frame_exists available
  obtain ⟨output⟩ := frame_exists (fun binding member => available binding (afterOrder.subset member))
  have unique : (axes ++ otherAxes).Nodup := by
    have order := ((beforeOrder.flatMap_right (fun binding : Binding => binding.port.wires)).map
      before.quantum.frame.idxOf)
    have all := order.nodup (RuntimeNamedInputAction.axes_unique inputChecked valid)
    simpa only [forestAxes,List.flatMap_cons,List.map_append,portAxes,axes,otherAxes,canonicalIn,rest] using all
  have selectedUnique := (List.nodup_append.mp unique).1
  have disjoint : otherAxes.Disjoint axes :=
    List.disjoint_left.mpr (fun axis other selected => (List.nodup_append.mp unique).2.2 axis selected axis other rfl)
  have stable (physical replacement logical : Nat) :
      spectatorEntry rest before.quantum.frame (scatter physical axes replacement) logical =
        spectatorEntry rest before.quantum.frame physical logical := by
    unfold spectatorEntry
    rw [Qleisli.RuntimeTargetScatter.gather_disjoint physical replacement axes otherAxes disjoint]
  have wireUnique : target.port.wires.Nodup := List.Pairwise.of_map before.quantum.frame.idxOf
    (fun _ _ different same => different (congrArg before.quantum.frame.idxOf same)) selectedUnique
  have inputPositive := (layout_bounds _ _ (owner_layout (input.available target targetMember)).1).1
  obtain ⟨outputLayout,outputWidth⟩ := owner_layout returnedLayout
  have outputPositive := (layout_bounds _ _ outputLayout).1
  have rows : outputCode.rows = 2^target.port.wires.length := by
    rw [nativeOut]
    change 2^(ownerLayout returned).bits = _
    rw [← outputWidth,wires]
  refine ⟨output,?_⟩
  intro Reference joint physical reference
  let canonicalJoint : Nat → Reference → ℂ := fun logical ref =>
    joint (recode canonicalIn inputChecked.bindings (sourceDimension inputChecked.bindings) logical) ref
  let localJoint : Nat → Nat → Reference → ℂ := fun digit env ref =>
    fibre inputCode.cols (product rest).labels.length (spectatorEntry rest before.quantum.frame env)
      canonicalJoint digit ref
  have incoming : (fun row => action input before.quantum.frame joint row reference) =
      (fun row => encodedParent axes inputCode localJoint row reference) := by
    funext row
    rw [regroup_action input orderedIn beforeOrder (bindings_unique inputChecked)]
    change action orderedIn before.quantum.frame canonicalJoint row reference = _
    rw [canonical_encoding orderedIn,nativeIn,head_code_action _ _ _ _ _ _ inputPositive]
    unfold encodedParent Qleisli.Semantics.Exact.action
    apply Qleisli.Exact.sum_map_congr
    intro digit _
    simp only [localJoint,nativeIn]
    unfold fibre
    simp only [stable]
    rfl
  have slice : sourceSlice axes physical localJoint =
      fibre matrix.cols (product rest).labels.length
        (spectatorEntry rest before.quantum.frame physical) canonicalJoint := by
    funext digit ref
    simp only [sourceSlice,localJoint,inputShape]
    unfold fibre
    simp only [stable]
  have small : gather physical axes < 2^target.port.wires.length := by
    simpa only [axes,portAxes,List.length_map] using gather_bound physical axes
  have law := localLaw localJoint physical (gather physical axes) reference (by rwa [rows])
  rw [← incoming,RuntimeNamedCallerAction.reorder_self _ _ wireUnique _ _ small,
    RuntimeScatterTransport.scatter_gather physical _ selectedUnique,slice] at law
  have outputLaw : action orderedOut after.quantum.frame (applyHead matrix canonicalJoint) physical reference =
      headEncoding outputCode (product rest).labels.length (spectatorEntry rest before.quantum.frame physical)
        (applyHead matrix canonicalJoint) (gather physical axes) reference := by
    rw [canonical_encoding orderedOut,← nativeOut,frames,wires,spectators]
    rfl
  have outPositive : 0 < outputCode.cols := by rw [nativeOut]; exact outputPositive
  rw [head_operator_encoding _ _ _ _ _ _ _ outPositive outputShape.symm] at outputLaw
  have resultOrder := regroup_action orderedOut output afterOrder.symm
    (afterOrder.nodup (bindings_unique outputChecked)) after.quantum.frame (applyHead matrix canonicalJoint)
    physical reference
  rw [source_dimensions afterOrder.symm] at resultOrder
  exact law.trans (outputLaw.symm.trans resultOrder)

#print axioms whole_action
end Qleisli.RuntimeSparseHeadAction
