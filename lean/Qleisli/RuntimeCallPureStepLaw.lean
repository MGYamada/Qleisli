import Qleisli.RuntimeCallHistorySteps
import Qleisli.RuntimeCallTraceBasis
import Qleisli.RuntimeCallTraceProtected
import Qleisli.RuntimeStructuralTrace

/-! Use each pure constructor's original native trace to supply the shared
ordered call-history law. Geometry-only steps emit no quantum action.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Finite (Dependency)
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface)
open RuntimeCallTraceFrames (Partition WireOrder allocated)
open RuntimeCallTraceCircuit (Transfer)
open Qleisli.Semantics.RawAction (events)

private theorem empty_transfer {dependencies : List Dependency} {parent child : Raw.State}
    {spectators : List Port} {p c : Raw.Transition}
    (partition : Partition parent.reference child.reference spectators)
    (live : p.state.live.Perm (c.state.live ++ spectators))
    (pFrame : p.state.frame = parent.frame) (cFrame : c.state.frame = child.frame)
    (pEvents : p.events = []) (cEvents : c.events = []) :
    Transfer dependencies parent child spectators p c := by
  refine ⟨⟨live,?_⟩,pFrame,cFrame,?_⟩
  · change p.state.frame.Perm (c.state.frame ++ WireOrder spectators)
    rw [pFrame,cFrame]
    exact partition.frame
  · intro joint row
    simp only [pEvents,cEvents,events,List.foldl_nil]

private theorem init_action {dependencies : List Dependency} {parent child : Raw.State}
    {spectators : List Port} {p c : Raw.Transition}
    (partition : Partition parent.reference child.reference spectators) (output wire : Nat)
    (pRead : Raw.step (dependencies.map (·.signature)) parent (.init0 output wire) = .ok p)
    (cRead : Raw.step (dependencies.map (·.signature)) child (.init0 output wire) = .ok c) :
    Partition p.state.reference c.state.reference spectators ∧
    PureAction dependencies parent.reference child.reference p.state.reference c.state.reference
      spectators p.events c.events := by
  obtain ⟨after,pShape,cShape⟩ := RuntimeCallTraceFrames.allocation_events partition output wire
  have pRef := Raw.step_reference _ _ _ _ pRead
  have cRef := Raw.step_reference _ _ _ _ cRead
  obtain ⟨pState,pEvents⟩ := Prod.mk.inj (Option.some.inj (pRef.symm.trans pShape))
  obtain ⟨cState,cEvents⟩ := Prod.mk.inj (Option.some.inj (cRef.symm.trans cShape))
  have grown : (parent.frame++[wire]).Nodup := by
    change (allocated parent.reference output wire).frame.Nodup
    rw [← pState]
    exact (Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ pRead).2.2).frame
  have fresh : wire ∉ parent.frame := fun held =>
    (List.nodup_append.mp grown).2.2 wire held wire List.mem_cons_self rfl
  rw [pState,cState,pEvents,cEvents]
  refine ⟨after,?_⟩
  intro joint row bounded
  simp only [events,List.foldl_cons,List.foldl_nil]
  exact RuntimeCallTraceAllocation.allocation_correlated parent.reference child.reference spectators
    partition output wire fresh dependencies joint row bounded

private theorem pure_action {dependencies : List Dependency} {parent child : Raw.State}
    {spectators : List Port} {p c : Raw.Transition} (op : Semantics.Raw.Op)
    (partition : Partition parent.reference child.reference spectators)
    (pRead : Raw.step (dependencies.map (·.signature)) parent op = .ok p)
    (cRead : Raw.step (dependencies.map (·.signature)) child op = .ok c) :
    Partition p.state.reference c.state.reference spectators ∧
    PureAction dependencies parent.reference child.reference p.state.reference c.state.reference
      spectators p.events c.events := by
  cases op with
  | init0 output wire => exact init_action partition output wire pRead cRead
  | gate gate input output =>
    have transfer := RuntimeCallTraceCircuit.gate_correlated _ _ _ _ partition gate input output _ _ pRead cRead
    exact ⟨transfer.partition,transfer.pure_action⟩
  | cnot control target controlOut targetOut =>
    have transfer := RuntimeCallTraceCircuit.cnot_correlated _ _ _ _ partition
      control target controlOut targetOut _ _ pRead cRead
    exact ⟨transfer.partition,transfer.pure_action⟩
  | toffoli first second target firstOut secondOut targetOut =>
    have transfer := RuntimeCallTraceCircuit.toffoli_correlated _ _ _ _ partition
      first second target firstOut secondOut targetOut _ _ pRead cRead
    exact ⟨transfer.partition,transfer.pure_action⟩
  | quantumIf control target controlOut targetOut zero one =>
    have transfer := RuntimeCallTraceCircuit.quantum_if_correlated _ _ _ _ partition
      control target controlOut targetOut zero one _ _ pRead cRead
    exact ⟨transfer.partition,transfer.pure_action⟩
  | applyUnitary input output written =>
    have transfer := RuntimeCallTraceCircuit.apply_correlated _ _ _ _ partition input output written _ _ pRead cRead
    exact ⟨transfer.partition,transfer.pure_action⟩
  | certifiedCompute input output ancilla function uses logical =>
    obtain ⟨after,pFrame,cFrame,law⟩ := RuntimeCallTraceComputed.certified_compute_correlated
      _ _ _ _ partition input output ancilla function uses logical _ _ pRead cRead
    let transfer : Transfer dependencies parent child spectators p c := ⟨after,pFrame,cFrame,law⟩
    exact ⟨after,transfer.pure_action⟩
  | computeUseUncompute input output targets ancilla function uses =>
    obtain ⟨after,pFrame,cFrame,law⟩ := RuntimeCallTraceProtected.protected_compute_correlated
      _ _ _ _ partition input output targets ancilla function uses _ _ pRead cRead
    let transfer : Transfer dependencies parent child spectators p c := ⟨after,pFrame,cFrame,law⟩
    exact ⟨after,transfer.pure_action⟩
  | liftBasis input output wires table =>
    exact RuntimeCallTraceBasis.basis_lift_correlated _ _ _ _ partition input output wires table _ _ pRead cRead
  | join left right output =>
    obtain ⟨pEvents,cEvents,live,pFrame,cFrame,_,_⟩ := RuntimeStructuralTrace.join_locality
      _ _ _ _ left right output _ _ partition.live pRead cRead
    let transfer : Transfer dependencies parent child spectators p c :=
      empty_transfer partition live pFrame cFrame pEvents cEvents
    exact ⟨transfer.partition,transfer.pure_action⟩
  | split input left right leftBits =>
    obtain ⟨pEvents,cEvents,live,pFrame,cFrame,_,_⟩ := RuntimeStructuralTrace.split_locality
      _ _ _ _ input left right leftBits _ _ partition.live pRead cRead
    let transfer : Transfer dependencies parent child spectators p c :=
      empty_transfer partition live pFrame cFrame pEvents cEvents
    exact ⟨transfer.partition,transfer.pure_action⟩
  | packUnit output =>
    obtain ⟨after,pShape,cShape⟩ := RuntimeCallTraceFrames.pack_unit_events partition output
    obtain ⟨pState,pEvents⟩ := Prod.mk.inj (Option.some.inj ((Raw.step_reference _ _ _ _ pRead).symm.trans pShape))
    obtain ⟨cState,cEvents⟩ := Prod.mk.inj (Option.some.inj ((Raw.step_reference _ _ _ _ cRead).symm.trans cShape))
    have live : p.state.reference.live.Perm (c.state.reference.live ++ spectators) := by
      rw [pState,cState]
      exact after.live
    let transfer : Transfer dependencies parent child spectators p c :=
      empty_transfer partition live (congrArg Interface.frame pState) (congrArg Interface.frame cState) pEvents cEvents
    exact ⟨transfer.partition,transfer.pure_action⟩
  | unpackUnit input =>
    have valid := Raw.Ownership.valid _ (Raw.step_conditions _ _ _ _ pRead).1
    obtain ⟨pAfter,pTrace,after,pFrame,cFrame,cEvents⟩ :=
      RuntimeCallTraceFrames.unpack_unit_events partition valid.owners (Raw.step_reference _ _ _ _ cRead)
    obtain ⟨pState,pEvents⟩ := Prod.mk.inj (Option.some.inj ((Raw.step_reference _ _ _ _ pRead).symm.trans pTrace))
    have live : p.state.reference.live.Perm (c.state.reference.live ++ spectators) := by
      rw [pState]
      exact after.live
    let transfer : Transfer dependencies parent child spectators p c :=
      empty_transfer partition live ((congrArg Interface.frame pState).trans pFrame) cFrame (pEvents.trans cEvents) cEvents
    exact ⟨transfer.partition,transfer.pure_action⟩

/-- All original pure constructors use their exact checked transition,
including empty structural events and both protected-compute forms. -/
theorem pure_step_law (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (op : Semantics.Raw.Op) :
    StepLaw dependencies parentDepth childDepth spectators (.pure op) := by
  apply step_of_total
  intro parent child parentAfter childAfter parentFold childFold partition actual localHistory agrees
  obtain ⟨_,_,pRead⟩ := parentFold
  obtain ⟨_,_,cRead⟩ := childFold
  exact checked_pure dependencies parentDepth childDepth parent child parentAfter childAfter spectators
    op pRead cRead (fun _ _ => pure_action op partition) actual localHistory agrees

#print axioms pure_step_law
end Qleisli.RuntimeCallHistory
