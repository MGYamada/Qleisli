import QleisliKernel.Qirf.RuntimeNamedFrameAxes
import QleisliKernel.Qirf.RuntimeStructuralAction

/-! Original structural operations preserve the physical frame and the exact
ordered concatenation of their selected wires. The proof consumes the actual
source operand order and Raw result token reads, including zero-width ports.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeStructuralWires
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface take insert step)
open RuntimeStructuralAction (PortOrder)

private def dropPort (state : Interface) (token : Nat) : Interface :=
  {state with live := state.live.filter (fun port => port.token != token)}

private theorem take_original (state : Interface) (port : Port)
    (unique : (state.live.map (·.token)).Nodup) (member : port ∈ state.live) :
    take state port.token = some (port,dropPort state port.token) := by
  unfold take
  rw [RuntimeNamedFrameAxes.tokenLookup state.live port unique member]
  rfl

private theorem drop_unique (state : Interface) (token : Nat)
    (unique : (state.live.map (·.token)).Nodup) :
    ((dropPort state token).live.map (·.token)).Nodup :=
  List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) unique

private theorem drop_absent (state : Interface) (token : Nat) :
    take (dropPort state token) token = none := by
  have absent : (dropPort state token).live.find? (fun port => port.token == token) = none := by
    apply List.find?_eq_none.mpr
    intro port member equal
    have kept := (List.mem_filter.mp member).2
    simp only [bne, equal, Bool.not_true] at kept
    cases kept
  unfold take
  rw [absent]
  rfl

private theorem ports_read (state : Interface) (ports : List Port)
    (unique : (state.live.map (·.token)).Nodup) (present : ports ⊆ state.live) :
    PureInterval.portsOf state.live (ports.map (·.token)) = some ports := by
  induction ports with
  | nil => rfl
  | cons first rest ih =>
    have found := RuntimeNamedFrameAxes.tokenLookup state.live first unique (present List.mem_cons_self)
    have later := ih (fun {_} member => present (List.mem_cons_of_mem _ member))
    unfold PureInterval.portsOf at later ⊢
    simp only [List.map_cons,List.mapM_cons,found,later,bind,Option.bind,pure]

private theorem original_result (state : Interface) (expected actual : List Port)
    (unique : (state.live.map (·.token)).Nodup) (present : expected ⊆ state.live)
    (read : PureInterval.portsOf state.live (expected.map (·.token)) = some actual) :
    actual = expected :=
  Option.some.inj (read.symm.trans (ports_read state expected unique present))

private theorem trace_result (before after : Interface) (operation : Semantics.Raw.Op)
    (trace : step before operation = some (after,[])) (computed : Interface)
    (read : step before operation = some (computed,[])) :
    after = computed :=
  congrArg Prod.fst (Option.some.inj (trace.symm.trans read))

private theorem checked_order_wires {kind operation inputs roles tokens}
    (order : PortOrder kind operation inputs roles tokens)
    (before after : Interface) (outputs : List Port)
    (inputUnique : (before.live.map (·.token)).Nodup) (outputUnique : (after.live.map (·.token)).Nodup)
    (present : inputs ⊆ before.live)
    (trace : step before operation = some (after,[]))
    (read : PureInterval.portsOf after.live tokens = some outputs) :
    after.frame = before.frame ∧ outputs.flatMap (·.wires) = inputs.flatMap (·.wires) ∧
      (inputs.map (·.token)).Nodup := by
  cases order with
  | join first second result output =>
    have takeFirst := take_original before first inputUnique (present List.mem_cons_self)
    have different : second.token ≠ first.token := by
      intro equal
      have absent : take (dropPort before first.token) second.token = none := by
        rw [equal]
        exact drop_absent before first.token
      simp only [step,takeFirst,absent,bind,Option.bind] at trace
      cases trace
    have still : second ∈ (dropPort before first.token).live :=
      List.mem_filter.mpr ⟨present (by simp),bne_iff_ne.mpr different⟩
    have takeSecond := take_original (dropPort before first.token) second
      (drop_unique before first.token inputUnique) still
    let joined : Port := ⟨output,first.wires ++ second.wires,(first.wires ++ second.wires).length⟩
    have result := trace_result before after _ trace
      (insert (dropPort (dropPort before first.token) second.token) output joined.wires) (by
        simp only [step,takeFirst,takeSecond,bind,Option.bind,pure]
        rfl)
    have placed : [joined] ⊆ after.live := by
      rw [result]
      exact fun port member => List.mem_append_right _ member
    have selected := original_result after [joined] outputs outputUnique placed read
    refine ⟨by rw [result]; rfl,?_,by simp [Ne.symm different]⟩
    simp [selected,joined]
  | split input first second left right =>
    have taken := take_original before input inputUnique (present List.mem_cons_self)
    let low := input.wires.take (RuntimeStructuralAction.basisBits first.basis)
    let high := input.wires.drop (RuntimeStructuralAction.basisBits first.basis)
    let firstPort : Port := ⟨left,low,low.length⟩
    let secondPort : Port := ⟨right,high,high.length⟩
    have result := trace_result before after _ trace
      (insert (insert (dropPort before input.token) left low) right high) (by
        simp only [step,taken,bind,Option.bind,pure]
        rfl)
    have placed : [firstPort,secondPort] ⊆ after.live := by
      rw [result]
      change [firstPort,secondPort] ⊆ ((dropPort before input.token).live ++ [firstPort]) ++ [secondPort]
      rw [List.append_assoc]
      exact fun port member => List.mem_append_right _ member
    have selected := original_result after [firstPort,secondPort] outputs outputUnique placed read
    refine ⟨by rw [result]; rfl,?_,by simp⟩
    simp only [selected,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact List.take_append_drop _ _
  | unit result output =>
    let port : Port := ⟨output,[],0⟩
    have result := trace_result before after _ trace (insert before output []) rfl
    have placed : [port] ⊆ after.live := by
      rw [result]
      exact fun port member => List.mem_append_right _ member
    have selected := original_result after [port] outputs outputUnique placed read
    exact ⟨by rw [result]; rfl,by simp [selected,port],by simp⟩
  | finish input empty =>
    have taken := take_original before input inputUnique (present List.mem_cons_self)
    have result := trace_result before after _ trace (dropPort before input.token) (by
      simp only [step,taken,bind,Option.bind,pure,empty.1,empty.2]
      rfl)
    have selected : outputs = [] := (Option.some.inj read).symm
    have wires := List.isEmpty_iff.mp empty.2
    exact ⟨by rw [result]; rfl,by simp [selected,wires],by simp⟩

/-- The selected source bindings are exactly the retained original read.
Both complete native owner checks supply token uniqueness independently. -/
theorem original_wires {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before) :
    action.interval.after.quantum.frame = action.interval.before.quantum.frame ∧
    action.outputs.flatMap (·.wires) = action.inputs.flatMap (·.wires) ∧
    (action.inputs.map (·.token)).Nodup := by
  obtain ⟨work,left,ran⟩ := action.inputRead
  obtain ⟨bindings,middle,ordered,returned⟩ := bind_success _ _ _ _ _ ran
  have original : action.inputs = bindings.map (·.port) := (pure_success _ _ _ _ returned).1
  have subset := (RuntimeSelectionPartition.order_values before.bindings action.inputRoles bindings
    ⟨work,middle,ordered⟩).1
  have inputUnique : (action.interval.before.quantum.live.map (·.token)).Nodup :=
    (action.beforeFrame.complete.map (·.token)).nodup
      (by simpa only [List.map_map,Function.comp_def] using action.beforeFrame.tokensDistinct)
  have outputUnique : (action.interval.after.quantum.live.map (·.token)).Nodup :=
    (action.afterFrame.complete.map (·.token)).nodup
      (by simpa only [List.map_map,Function.comp_def] using action.afterFrame.tokensDistinct)
  have present : action.inputs ⊆ action.interval.before.quantum.live := by
    rw [original]
    intro port member
    obtain ⟨binding,inside,same⟩ := List.mem_map.mp member
    exact action.beforeFrame.complete.mem_iff.mp
      (List.mem_map.mpr ⟨binding,action.beforeBindings.symm ▸ subset inside,same⟩)
  exact checked_order_wires action.portOrder _ _ _ inputUnique outputUnique present action.reference action.outputRead

theorem original_trace {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before) :
    RuntimeLocalEvents.trace action.interval.before.quantum.reference [action.operation] =
      some ⟨action.interval.after.quantum.reference,[],action.interval.before.quantum.frame.length⟩ := by
  simp only [RuntimeLocalEvents.trace,List.foldlM_cons,List.foldlM_nil,Semantics.RawTrace.advance,
    action.reference,bind,Option.bind,pure,List.nil_append]
  rfl

#print axioms original_wires
#print axioms original_trace
end Qleisli.RuntimeStructuralWires
