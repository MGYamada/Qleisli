import Qleisli.RuntimeNamedPrimitiveSourceLift
import Qleisli.RuntimeNamedPrimitiveOutputs
import Qleisli.RuntimeNamedInputAction

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
open RuntimeOwnerCodeReindex (lookup_exists)
open RuntimeOwnerMap (Binding)

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
        axes port output form parentEvents childEvents ∧
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
  exact ⟨entry,parent,child,lifted,
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
  obtain ⟨entry,events,localEvents,lifted,_,law⟩ := inline_reference_action primitive source form literal
  obtain ⟨target,present,owner,port⟩ := RuntimeNamedPrimitiveOutputs.port_binding source.inputPort
  have member : target ∈ checked.bindings := bindings.symm ▸ present
  obtain ⟨actual,_⟩ := lookup_exists frame.owners target member
  have carriers : (primitive.interval.selected.map fun port =>
      (⟨port,role.basis⟩ : Semantics.CarrierInterface.Owner)) = [⟨target.port,target.owner.basis⟩] := by
    simp only [selected_port source,List.map_singleton,port,owner]
  have code := primitive.inputRead
  rw [carriers] at code
  refine ⟨events,lifted.parentTrace,target,member,owner,port,?_⟩
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

#print axioms inline_reference_action
#print axioms inline_encoded_action
end Qleisli.RuntimeLiteralInlinePrimitive
