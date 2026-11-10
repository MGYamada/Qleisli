import Qleisli.RuntimeNamedPrimitiveSourceLift
import Qleisli.RuntimeNamedPrimitiveOutputs
import Qleisli.RuntimeNamedInputAction
import Qleisli.RuntimeNamedThreeFrameChain
import Qleisli.RuntimeSelectionSpectators

/-! The direct primitive receipt binds its original source operand to the
actual Raw events and exact local code action. The joint reference family
is unrestricted, and the real output reorder stays explicit.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralInlinePrimitive
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.Finite
open Qleisli.Semantics.Exact (action)
open Qleisli.RuntimeNamedGateLift (Form Facts portAxes interval_single_owner_lift)
open Qleisli.RuntimeNamedPrimitiveSourceLift (encodedParent sourceSlice source_parent_action)
open Qleisli.RuntimeForestProduct (referenceAction)
open Qleisli.RuntimeFiniteTargetFibre (targetFibre)
open Qleisli.RuntimeNamedInputAction (fibre_scatter)
open RuntimeForestCode (Frame)
open Qleisli.RuntimeNamedCallerAction (updatedJoint whole_caller_of_head_action)
open Qleisli.RuntimeNamedHeadCoefficients (output_from_target_fibre)
open RuntimeOwnerCodeReindex (lookup_exists reindex_exists)
open RuntimeOwnerMap (Binding)

/-- Recognize only the singleton spellings covered by the whole-caller law.
The equality is with the retained operations, including both original tokens. -/
def literalForm {dependencies program block start count input output role kind}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind) :
    Option {form : Form // primitive.interval.operations = [form.operation input output]} :=
  match primitive.interval.operations with
  | [.gate gate writtenInput writtenOutput] =>
    if same : writtenInput = input ∧ writtenOutput = output then
      some ⟨.gate gate,by simp only [Form.operation,← same.1,← same.2]⟩
    else none
  | [.applyUnitary writtenInput writtenOutput steps] =>
    if same : writtenInput = input ∧ writtenOutput = output then
      some ⟨.applyUnitary steps,by simp only [Form.operation,← same.1,← same.2]⟩
    else none
  | _ => none

private theorem selected_port {dependencies program block start count input output role kind}
    {primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (source : RuntimePrimitiveSource.Checked primitive) :
    primitive.interval.selected = [source.inputPort.port] := by
  have entry := RuntimeIntervalStates.same_before source.interval primitive.interval.interval
  have live := RuntimeNamedPrimitiveOutputs.port_live source.frame source.inputPort
  obtain ⟨work,left,read⟩ := source.interval.prefixRead
  have valid := Raw.Ownership.valid _ (Raw.Observation.checkOps_invariants _ _ _ _ _ work left read).1
  have lookup := RuntimeNamedFrameAxes.tokenLookup source.interval.before.quantum.live source.inputPort.port
    valid.owners live
  have atToken : PureInterval.ports source.interval.before [source.inputPort.port.token] =
      some [source.inputPort.port] := by
    simp [PureInterval.ports,PureInterval.portsOf,List.mapM_cons,lookup]
  have original := (congrArg (fun token => PureInterval.ports source.interval.before [token])
    source.inputToken).symm.trans atToken
  have native := primitive.interval.atEntry
  rw [← entry] at native
  exact Option.some.inj (native.symm.trans original)

private theorem cast_lift {dependencies program block start count input output role kind}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (port : Semantics.Raw.Port) (form : Form) (token : port.token = input)
    (selected : primitive.interval.selected = [port])
    (literal : primitive.interval.operations = [form.operation input output]) :
    ∃ localEntry : Raw.State,
      (portAxes primitive.interval.interval.before.quantum port).Nodup ∧
      Qleisli.RuntimeNamedGateLift.Lift dependencies primitive.interval.operations primitive.interval.interval.before.quantum
        primitive.interval.interval.after.quantum localEntry primitive.interval.pureBody.state
        (portAxes primitive.interval.interval.before.quantum port) port output form := by
  cases token
  exact interval_single_owner_lift port primitive.interval form selected literal

/-- Direct gates and literal apply-unitary tapes use the same exact parent
and local action proof as a named primitive. All events and the selected
port belong to the original checked interval. -/
theorem inline_reference_action {dependencies program block start count input output role kind}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (source : RuntimePrimitiveSource.Checked primitive)
    (form : Form) (literal : primitive.interval.operations = [form.operation input output]) :
    let port := source.inputPort.port
    let axes := portAxes primitive.interval.interval.before.quantum port
    ∃ localEntry parentEvents childEvents,
      Facts dependencies primitive.interval.operations primitive.interval.interval.before.quantum
        primitive.interval.interval.after.quantum localEntry primitive.interval.pureBody.state
        axes port output form parentEvents childEvents ∧ axes.Nodup ∧
      ((RuntimeSourcePrimitiveAction.operand source.event).bind
        (fun (op,owner) => Semantics.PrimitiveOperator.meaning op owner.basis)) = some primitive.expected ∧
      ∀ {Reference : Type} (joint : Nat → Nat → Reference → ℂ) (base row : Nat) (reference : Reference),
        row < primitive.physical.rows →
        Qleisli.Semantics.RawAction.event dependencies
          (.reorder port.wires.length (port.wires.map port.wires.idxOf))
          (fun value => Qleisli.Semantics.RawAction.events dependencies parentEvents
            (fun input => encodedParent axes primitive.inputCode joint input reference) (scatter base axes value)) row =
        action primitive.outputCode
          (fun logical ref => action primitive.expected (sourceSlice axes base joint) logical ref) row reference := by
  intro port axes
  have selected := selected_port source
  obtain ⟨entry,unique,parent,child,lifted⟩ := cast_lift primitive port form source.inputToken selected literal
  have sameFragment :
      RuntimePureInterval.fragment primitive.interval.selected primitive.interval.operations [output] =
        RuntimePureInterval.fragment [port] primitive.interval.operations [output] := by rw [selected]
  exact ⟨entry,parent,child,lifted,unique,
    source_parent_action primitive source lifted unique (List.length_map ..) sameFragment⟩

/-- Substitute the original complete caller encoding into the direct
primitive's exact Raw action. No factorization of the joint state is assumed. -/
theorem inline_encoded_action {dependencies program block start count input output role kind}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (source : RuntimePrimitiveSource.Checked primitive)
    (form : Form) (literal : primitive.interval.operations = [form.operation input output])
    {roles} (checked : RuntimeOwnerMap.Checked roles primitive.interval.interval.before) (frame : Frame checked)
    (bindings : checked.bindings = source.frame.bindings) :
    let before := primitive.interval.interval.before.quantum
    let after := primitive.interval.interval.after.quantum
    ∃ events,
      RuntimeLocalEvents.trace before.reference primitive.interval.operations =
        some ⟨after.reference,events,before.frame.length⟩ ∧
      ∃ target ∈ checked.bindings,
        target.owner = role ∧ target.port = source.inputPort.port ∧
        (portAxes before target.port).Nodup ∧
        after.reference = Semantics.RawTrace.insert
          {before.reference with live := before.live.filter (fun p => p.token != target.port.token)}
          output target.port.wires ∧
        ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (base row : Nat) (reference : Reference),
          row < primitive.physical.rows →
          Qleisli.Semantics.RawAction.event dependencies
            (.reorder target.port.wires.length (target.port.wires.map target.port.wires.idxOf))
            (fun value => Qleisli.Semantics.RawAction.events dependencies events
              (fun input => referenceAction frame joint input reference) (scatter base (portAxes before target.port) value))
            row =
          action primitive.outputCode
            (fun logical ref => action primitive.expected (targetFibre frame target base joint) logical ref)
            row reference := by
  intro before after
  obtain ⟨entry,events,localEvents,lifted,unique,_,law⟩ := inline_reference_action primitive source form literal
  obtain ⟨target,present,owner,port⟩ := RuntimeNamedPrimitiveOutputs.port_binding source.inputPort
  have member : target ∈ checked.bindings := bindings.symm ▸ present
  obtain ⟨actual,_⟩ := lookup_exists frame.owners target member
  have carriers : (primitive.interval.selected.map fun port =>
      (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) = [⟨target.port,target.owner.basis⟩] := by
    simp only [selected_port source,List.map_singleton,port,owner]
  have code := primitive.inputRead
  rw [carriers] at code
  refine ⟨events,lifted.parentTrace,target,member,owner,port,?_,?_,?_⟩
  · exact port.symm ▸ unique
  · exact port.symm ▸ lifted.parentInterface
  intro Reference joint base row reference bound
  have interpreted := law (fun digit environment ref => targetFibre frame target environment joint digit ref)
    base row reference bound
  have onTarget :
      (fun input => encodedParent (portAxes before source.inputPort.port) primitive.inputCode
        (fun digit environment ref => targetFibre frame target environment joint digit ref) input reference) =
      (fun input => referenceAction frame joint input reference) := by
    funext input
    rw [← port]
    exact (RuntimeNamedInputAction.original_native_encoding primitive.interval.interval checked frame target
      member actual primitive.inputCode code joint input reference).symm
  have slice : sourceSlice (portAxes before source.inputPort.port) base
        (fun digit environment ref => targetFibre frame target environment joint digit ref) =
      targetFibre frame target base joint := by
    funext digit ref
    unfold sourceSlice
    rw [← port]
    exact fibre_scatter frame primitive.interval.interval.history.1 target member joint base 0 digit ref
  rw [onTarget,slice,← port] at interpreted
  exact interpreted

/-- The local original owner return and the actual caller transport determine
the same ordered spectator map, including zero-width owners. -/
theorem inline_spectators {dependencies program block start count input output role kind}
    {primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind}
    (source : RuntimePrimitiveSource.Checked primitive)
    (target : Binding) (member : target ∈ source.frame.bindings)
    (owner : target.owner = role) (port : target.port = source.inputPort.port)
    (returned : Binding) (present : returned ∈ source.owners.after.bindings)
    (returnedOwner : returned.owner = role) :
    source.owners.after.bindings.erase returned = source.frame.bindings.erase target := by
  have partition : ([target] ++ RuntimeSelectionPartition.complement source.frame.bindings [target]).Perm
      source.frame.bindings := by
    have same : RuntimeSelectionPartition.complement source.frame.bindings [target] =
        source.frame.bindings.erase target := by
      unfold RuntimeSelectionPartition.complement
      rw [List.Nodup.erase_eq_filter _ target]
      · apply List.filter_congr
        intro binding _
        by_cases equal : binding = target
        · simp [equal]
        · simp [equal]
      · exact List.Pairwise.of_map (fun b : Binding => b.port.token)
          (fun _ _ different equal => different (congrArg (fun b : Binding => b.port.token) equal))
          source.frame.tokensDistinct
    rw [same]
    exact (List.perm_cons_erase member).symm
  have chosenOwners : [target].map Binding.owner = [role] := by simp [owner]
  have chosenPorts : [target].map Binding.port = primitive.interval.selected := by
    simp [port,selected_port source]
  have spectators := RuntimeSelectionSpectators.interval_spectators primitive.interval source.interval
    source.frame source.owners [target] chosenOwners chosenPorts partition
  rw [← RuntimeNamedCallerGeometry.owner_complement source.frame target member,
    ← RuntimeNamedCallerGeometry.owner_complement source.owners.after returned present,
    owner,returnedOwner]
  have ordered := congrArg (List.filter (fun value => !([role]).contains value)) source.owners.after.ordered
  simp only [List.filter_map,Function.comp_def] at ordered
  apply RuntimeOwnerTransitionAction.owner_order_eq _ _ _ _ ordered
  · have unique : (source.frame.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
      simpa only [← source.frame.ordered,List.map_map,Function.comp_def] using source.frame.ownersDistinct
    have selected : (source.frame.bindings.filter (fun binding => !([role]).contains binding.owner)).Sublist
        source.frame.bindings := List.filter_sublist
    exact (selected.map (fun binding => binding.owner.ordinal)).nodup unique
  · intro binding inAfter
    have belongs := List.mem_filter.mp inAfter
    exact List.mem_filter.mpr ⟨spectators binding belongs.1 (by simpa using belongs.2),belongs.2⟩

/-- The original direct primitive acts on the complete returned caller frame.
The source target and its returned owner are retained, including the relative
order and exact code of every spectator and arbitrary reference columns. -/
theorem inline_whole_action {dependencies program block start count input output role kind}
    (primitive : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (source : RuntimePrimitiveSource.Checked primitive)
    (form : Form) (literal : primitive.interval.operations = [form.operation input output])
    {roles} (checked : RuntimeOwnerMap.Checked roles primitive.interval.interval.before) (frame : Frame checked)
    (bindings : checked.bindings = source.frame.bindings) :
    let before := primitive.interval.interval.before.quantum
    let after := primitive.interval.interval.after.quantum
    ∃ events,
      RuntimeLocalEvents.trace before.reference primitive.interval.operations =
        some ⟨after.reference,events,before.frame.length⟩ ∧
      ∃ target ∈ checked.bindings, target.owner = role ∧
        ∃ returned ∈ source.owners.after.bindings, returned.owner = role ∧
          ∃ result : Frame source.owners.after,
          ∀ {Reference : Type} (joint : Nat → Reference → ℂ) physical reference,
            Qleisli.Semantics.RawAction.events dependencies events
                (fun label => referenceAction frame joint label reference) physical =
              referenceAction result
                (updatedJoint frame result target returned primitive.expected joint) physical reference := by
  intro before after
  obtain ⟨events,trace,target,member,owner,port,unique,interface,localLaw⟩ :=
    inline_encoded_action primitive source form literal checked frame bindings
  obtain ⟨returned,present,returnedOwner,returnedPort⟩ := RuntimeNamedPrimitiveOutputs.port_binding source.outputPort
  have originalMember : target ∈ source.frame.bindings := bindings ▸ member
  have spectators := (inline_spectators source target originalMember owner port returned present returnedOwner).trans
    (congrArg (fun bindings => bindings.erase target) bindings.symm)
  have stateEq := RuntimeIntervalStates.same_after source.interval primitive.interval.interval
  have frames : source.interval.after.quantum.frame = before.frame :=
    (congrArg (fun state : Raw.Observation.State => state.quantum.frame) stateEq).trans
      (congrArg Semantics.RawTrace.Interface.frame interface)
  let nativePort : Semantics.Raw.Port := ⟨output,target.port.wires,target.port.wires.length⟩
  have live := congrArg Semantics.RawTrace.Interface.live interface
  change after.live = before.live.filter (fun p => p.token != target.port.token) ++ [nativePort] at live
  have nativeMember : nativePort ∈ source.interval.after.quantum.live := by
    rw [stateEq]
    change nativePort ∈ after.live
    rw [live]
    exact List.mem_append_right _ List.mem_cons_self
  have returnedMember : returned.port ∈ source.interval.after.quantum.live :=
    source.owners.after.complete.mem_iff.mp (List.mem_map.mpr ⟨returned,present,rfl⟩)
  have sameToken : returned.port.token = nativePort.token :=
    (congrArg Semantics.Raw.Port.token returnedPort).trans source.outputToken
  have samePort := RuntimeNamedCallerGeometry.full_port_unique source.owners.after _ _ returnedMember nativeMember sameToken
  have nativeWires := congrArg Semantics.Raw.Port.wires samePort
  have wires : returned.port.wires = target.port.wires := nativeWires
  have outputCarriers : (primitive.interval.returned.map fun p =>
      (⟨p,role.basis⟩ : Semantics.CarrierInterface.Owner)) =
      [⟨returned.port,returned.owner.basis⟩] := by
    rw [RuntimeNamedPrimitiveOutputs.primitive_output_port source,← returnedPort,returnedOwner]
    rfl
  have outputRead := primitive.outputRead
  rw [outputCarriers] at outputRead
  have inputCarriers : (primitive.interval.selected.map fun p =>
      (⟨p,role.basis⟩ : Semantics.CarrierInterface.Owner)) =
      [⟨target.port,target.owner.basis⟩] := by
    rw [selected_port source,← port,owner]
    rfl
  have inputRead := primitive.inputRead
  rw [inputCarriers] at inputRead
  have permutation := (List.perm_cons_erase member).symm
  obtain ⟨all,kept⟩ := reindex_exists frame.owners (target::checked.bindings.erase target) permutation.subset
  cases all with
  | cons actual rest =>
    have inputCode := RuntimeNamedInputAction.singleton_encoding actual primitive.inputCode inputRead
    have inputShape := primitive.action.logicalShape.1
    rw [primitive.equation,inputCode] at inputShape
    change primitive.expected.cols = actual.layout.labels.length at inputShape
    have outputShape := primitive.action.logicalShape.2
    rw [primitive.equation] at outputShape
    have basis := congrArg (·.basis) (returnedOwner.trans owner.symm)
    obtain ⟨newCode⟩ := RuntimeNamedThreeFrameChain.primitive_owner_code checked source.owners.after
      primitive.interval.interval.history.1 source.interval.history.2.2.1 target returned
      member present basis wires actual
    have retained := spectators.symm ▸ rest
    obtain ⟨all,_⟩ := reindex_exists (.cons newCode retained) source.owners.after.bindings
      (List.perm_cons_erase present).subset
    obtain ⟨result⟩ := RuntimeForestFrameEvidence.of_ownerCodes source.owners.after ⟨all⟩
    refine ⟨events,trace,target,member,owner,returned,present,returnedOwner,result,
      whole_caller_of_head_action frame result target returned present rest spectators frames wires unique
        primitive.outputCode primitive.expected outputRead events ?_⟩
    intro Reference joint base row reference small
    exact (localLaw joint base row reference (by rwa [primitive.action.physicalShape.2])).trans
      (output_from_target_fibre frame target member actual rest kept
        primitive.outputCode primitive.expected inputShape outputShape.symm joint base row reference)

#print axioms inline_whole_action
#print axioms inline_spectators
#print axioms inline_reference_action
#print axioms inline_encoded_action
end Qleisli.RuntimeLiteralInlinePrimitive
