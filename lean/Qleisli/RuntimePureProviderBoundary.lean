import Qleisli.RuntimePureProviderExecution

/-! Read the original provider's sparse source frame in its actual packed
input and output coordinates, using the retained carrier-code receipt.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimePureProviderBoundary
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open Semantics.Finite (gather)
open Semantics.FiniteCarrier (encoding)
open Semantics.Exact (Matrix)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (carrierOwners forestAxes sparseEntry)
open RuntimeSemanticForest (Frame product product_agrees frame_exists)
open Qleisli.Semantics.Exact (action entry scalar)
open Qleisli.Semantics.ObservingAction (History)
open Qleisli.RuntimeLiteralBody (SourceHistory SemanticHistoryAgreesWithInherited)
open Qleisli.RuntimeCallHistory (SourceAgreementWithin)

noncomputable def packedAction {bindings : Map} (frame : Frame bindings)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (ref : Reference) : ℂ :=
  ((List.range frame.code.dimension).map fun digit =>
    scalar (sparseEntry frame.code row digit) * joint digit ref).sum

theorem packed_code_action {bindings : Map} (frame : Frame bindings) {code : Matrix}
    (same : code = encoding (product bindings))
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (ref : Reference)
    (bounded : row < code.rows) : packedAction frame joint row ref = action code joint row ref := by
  subst code
  have layout := product_agrees frame
  unfold packedAction action
  rw [layout.dimension]
  apply Qleisli.Exact.sum_map_congr
  intro digit present
  have bound : digit < (product bindings).labels.length := List.mem_range.mp present
  exact congrArg (fun value => scalar value * joint digit ref) (layout.encodingEntry row digit bounded bound)

theorem reorder_packed {bindings : Map} (frame : Frame bindings)
    (dependencies : List Semantics.Finite.Dependency) (physicalFrame : List Nat)
    (permutation : (forestAxes physicalFrame bindings).Perm (List.range physicalFrame.length))
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (ref : Reference)
    (bounded : row < 2^physicalFrame.length) :
    Qleisli.Semantics.RawAction.event dependencies
        (.reorder physicalFrame.length (forestAxes physicalFrame bindings))
        (fun input => RuntimeSemanticForest.action frame physicalFrame joint input ref) row =
      packedAction frame joint row ref := by
  obtain ⟨original,_,coordinate,equation⟩ :=
    RuntimeNamedThreePackedOutput.reorder_gather dependencies _ _ permutation
      (fun input => RuntimeSemanticForest.action frame physicalFrame joint input ref) row bounded
  rw [equation]
  unfold RuntimeSemanticForest.action packedAction
  apply Qleisli.Exact.sum_map_congr
  intro digit _
  change scalar (sparseEntry frame.code (gather original (forestAxes physicalFrame bindings)) digit) *
    joint digit ref = scalar (sparseEntry frame.code row digit) * joint digit ref
  rw [coordinate]

private theorem reordered_subset {roles state assigned} (input : RuntimeOwnerMap.Checked roles state)
    (read : RuntimeInterval.Computed (RuntimePureBody.reordered roles state assigned) input) :
    input.bindings ⊆ assigned := by
  obtain ⟨work,left,ran⟩ := read
  unfold RuntimePureBody.reordered at ran
  obtain ⟨ordered,middle,order,checked⟩ := bind_success _ _ _ _ _ ran
  rw [RuntimeBoundaryOwnerEvidence.check_bindings input ⟨middle,left,checked⟩]
  exact (RuntimeSelectionPartition.order_values assigned roles ordered ⟨work,middle,order⟩).1

/-- The original provider's native carrier is the actual initial source
binding, even after the source's initial owner reordering. -/
theorem original_input_order {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    {roles state} (input : RuntimeOwnerMap.Checked roles state)
    (reordered : RuntimeInterval.Computed (RuntimePureBody.reordered roles state checked.originalBody.initial) input)
    (live : state.quantum.live = [checked.paths.ir.original.prepared.ports.input]) :
    input.bindings = checked.originalBody.initial ∧
      carrierOwners input.bindings =
        [⟨checked.paths.ir.original.prepared.ports.input,checked.paths.ir.original.prepared.ports.domain⟩] := by
  have assigned := RuntimeBoundaryOwnerEvidence.bindings_carriers checked.originalBody.initialRead
  have size : checked.originalBody.initial.length = 1 := by
    simpa only [carrierOwners,List.length_map,List.length_cons,List.length_nil] using congrArg List.length assigned
  have inputSize : input.bindings.length = 1 := by
    have count := input.complete.length_eq
    rw [List.length_map,live] at count
    exact count
  obtain ⟨first,source⟩ := List.length_eq_one_iff.mp size
  obtain ⟨only,ordered⟩ := List.length_eq_one_iff.mp inputSize
  have present : only ∈ checked.originalBody.initial := reordered_subset input reordered (by simp [ordered])
  have same : only = first := by simpa only [source,List.mem_singleton] using present
  have bindings : input.bindings = checked.originalBody.initial := by rw [ordered,source,same]
  exact ⟨bindings,bindings.symm ▸ assigned⟩

/-- The initial literal history is exactly the original source input
coefficients encoded through the provider's actual port. -/
theorem input_agreement {artifact context description graph index request header root demand}
    (checked : @RuntimeProviderAction.Checked artifact context description graph index request header root demand)
    (joint : Nat → Nat → ℂ)
    (input : RuntimeOwnerMap.Checked
      (SourceRuntimeScope.Subject.whole header.original.body).initialRoles
      checked.originalBody.body.result.prepared.block.entry)
    (reordered : RuntimeInterval.Computed
      (RuntimePureBody.reordered (SourceRuntimeScope.Subject.whole header.original.body).initialRoles
        checked.originalBody.body.result.prepared.block.entry checked.originalBody.initial) input) :
    let native := checked.paths.ir.original
    let state := checked.originalBody.body.result.prepared.block.entry
    let source : RuntimeStructuralAction.SourceState :=
      ⟨checked.originalBody.initial,header.original.body.checked.summary.parameterValues.flatMap
        SourceRuntimeValues.valueOwners,header.original.body.checked.summary.nextOwner⟩
    let sourceInitial : SourceHistory := ⟨source,[],[],joint,[]⟩
    let initial : History := ⟨[],[],action native.prepared.inputCode joint⟩
    SourceAgreementWithin (some (· = {})) none [] state {source with bindings := input.bindings} {} sourceInitial initial := by
  intro native state source sourceInitial initial
  have original := RuntimePureProviderExecution.entry_reference checked.originalBody.body.result.prepared
    native.prepared.ports.noClassical.1
  have nativeFrame : state.quantum.reference = ⟨[native.prepared.ports.input],native.prepared.ports.input.wires⟩ := by
    change state.quantum.reference = Semantics.RawTrace.initial native.program.inputs at original
    exact original.trans (by simp [native.prepared.ports.inputPort,Semantics.RawTrace.initial])
  have live : state.quantum.live = [native.prepared.ports.input] := congrArg Semantics.RawTrace.Interface.live nativeFrame
  have wires : state.quantum.frame = native.prepared.ports.input.wires := congrArg Semantics.RawTrace.Interface.frame nativeFrame
  obtain ⟨same,carriers⟩ := original_input_order checked input reordered live
  have codeRead : RuntimeInterval.Computed (Carrier.ownerCode (carrierOwners input.bindings))
      native.prepared.inputCode := carriers.symm ▸ native.prepared.inputCodeRead
  obtain ⟨available,codeEq⟩ := RuntimeSparseOperationAction.original_block_code codeRead
  obtain ⟨frame⟩ := frame_exists available
  have inputPorts : input.bindings.map (·.port) = [native.prepared.ports.input] := by
    simpa only [carrierOwners,List.map_map,Function.comp_def,List.map_cons,List.map_nil] using
      congrArg (List.map Semantics.CarrierInterface.Owner.port) carriers
  have valid : Raw.stateValid state.quantum = true := Raw.inputs_valid _ _ _ rfl (by
    obtain ⟨work,left,ran⟩ := checked.originalBody.body.result.prepared.inputRead
    unfold PureInterval.initial at ran
    obtain ⟨quantum,_,inserted,returned⟩ := bind_success _ _ _ _ _ ran
    rw [native.prepared.ports.noClassical.1,List.foldlM_nil] at returned
    have finish := congrArg Raw.Observation.State.quantum (pure_success _ _ _ _ returned).1
    change state.quantum = quantum at finish
    rw [finish]
    exact (lift_success _ _ _ _ inserted).1)
  have allWires : input.bindings.flatMap (fun b => b.port.wires) = state.quantum.frame := by
    have all := congrArg (List.flatMap Semantics.Raw.Port.wires) inputPorts
    simpa only [List.flatMap_map,List.flatMap_cons,List.flatMap_nil,List.append_nil,wires] using all
  have width : (product input.bindings).bits = state.quantum.frame.length :=
    (RuntimeSparseBlockEncoding.product_width available).trans (congrArg List.length allWires)
  have axes : forestAxes state.quantum.frame input.bindings = List.range state.quantum.frame.length := by
    unfold forestAxes
    rw [allWires]
    exact RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ valid).frame
  refine ⟨rfl,?_,?_⟩
  · change sourceInitial.owners = {source with bindings := input.bindings}
    rw [same]
  · change initial.hidden = sourceInitial.outcomes.map Prod.snd ∧
      Qleisli.RuntimeLiteralBranchChoice.measurementBits [] initial.values = some sourceInitial.measurements ∧ _
    refine ⟨rfl,rfl,⟨RuntimeOrdinarySSA.Agreement.empty _ _,fun id member => by cases member⟩,
      _,input,rfl,frame,?_⟩
    intro col row bounded
    have codeBound : row < native.prepared.inputCode.rows := by
      rw [codeEq]
      change row < 2^(product input.bindings).bits
      rwa [width]
    have packed := packed_code_action frame codeEq joint row col codeBound
    change action native.prepared.inputCode joint row col =
      RuntimeSemanticForest.action frame state.quantum.frame joint row col
    rw [← packed]
    unfold packedAction RuntimeSemanticForest.action RuntimeForestCode.embed
    rw [axes,Raw.Sector.gather_identity row _ bounded]

#print axioms packed_code_action
#print axioms reorder_packed
#print axioms original_input_order
#print axioms input_agreement
end Qleisli.RuntimePureProviderBoundary
