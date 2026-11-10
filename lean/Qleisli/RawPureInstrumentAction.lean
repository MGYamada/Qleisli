import Qleisli.RawProtectedMatrixAction
import QleisliKernel.Raw.BranchFunction

/-! The exact matrix of the original observing evaluator on a pure event
list applies that same ordered Raw trace to arbitrary reference columns.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.PureInstrumentAction
open QleisliKernel QleisliKernel.Finite
open QleisliKernel.Semantics.Exact (Matrix)
open QleisliKernel.Semantics.Finite (Dependency)
open QleisliKernel.Semantics.Raw (Event)
open Qleisli.Semantics.Exact (action entry)
open Qleisli.Semantics.RawAction (event events)

private theorem identity_action {size : Nat} {initial : Matrix}
    (read : QleisliKernel.Exact.Matrix.identity size = .ok initial)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bounded : row < initial.rows) : action initial joint row reference = joint row reference := by
  obtain ⟨_,rows,cols,entries⟩ := Qleisli.Exact.identity_meaning _ _ read
  unfold action
  rw [cols]
  calc
    _ = ((List.range size).map fun col => if row = col then joint col reference else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro col member
      rw [entries row col (rows ▸ bounded) (List.mem_range.mp member)]
      split <;> simp
    _ = _ := Qleisli.Exact.range_delta_sum _ _ _ (rows ▸ bounded)

private theorem fold_action (dependencies : List Dependency)
    (recurse : List Semantics.Observation.Event → Raw.Instrument.History → WorkM (List Raw.Instrument.History))
    (operations : List Event) (initial final : Raw.Instrument.History) (work left : Nat)
    (read : ((operations.map Semantics.Observation.Event.pure).foldlM
      (fun (histories : List Raw.Instrument.History) operation => do
        let groups ← histories.mapM (Raw.Instrument.stepEvent dependencies recurse operation)
        return groups.flatten) [initial]).run work = (.ok [final],left))
    {Reference : Type} (joint input : Nat → Reference → ℂ)
    (start : ∀ row ref, row < initial.operator.rows → action initial.operator joint row ref = input row ref)
    (row : Nat) (reference : Reference) (bound : row < final.operator.rows) :
    action final.operator joint row reference =
      events dependencies operations (fun index => input index reference) row := by
  induction operations generalizing initial work input with
  | nil =>
    have same := (pure_success _ _ _ _ read).1
    have equal : final = initial := (List.cons.inj same).1
    subst final
    exact start row reference bound
  | cons operation rest ih =>
    simp only [List.map_cons,List.foldlM_cons] at read
    obtain ⟨groups,middle,first,tail⟩ := bind_success _ _ _ _ _ read
    simp only [List.mapM_cons,List.mapM_nil,bind_assoc,pure_bind,List.flatten_cons,List.flatten_nil,
      List.append_nil] at first
    obtain ⟨heads,afterHead,head,returned⟩ := bind_success _ _ _ _ _ first
    have equal : groups = heads := (pure_success _ _ _ _ returned).1
    subst groups
    unfold Raw.Instrument.stepEvent at head
    obtain ⟨_,afterCharge,_,performed⟩ := bind_success _ _ _ _ _ head
    obtain ⟨matrix,afterMatrix,matrixRead,performed⟩ := bind_success _ _ _ _ _ performed
    obtain ⟨next,afterNext,nextRead,returned⟩ := bind_success _ _ _ _ _ performed
    have headsEq := (pure_success _ _ _ _ returned).1
    subst heads
    unfold Raw.Instrument.apply at nextRead
    obtain ⟨product,afterProduct,composed,returned⟩ := bind_success _ _ _ _ _ nextRead
    have nextEq := (pure_success _ _ _ _ returned).1
    subst next
    have compose := exactWork_success _ _ _ _ composed
    have shape := Qleisli.Exact.compose_meaning _ _ _ _ _ compose
    let values := fun col ref => event dependencies operation (fun index => input index ref) col
    apply ih _ middle tail values
    intro output ref inside
    have outputBound : output < matrix.rows := shape.2.1 ▸ inside
    change action product joint output ref = values output ref
    rw [Qleisli.Exact.compose_action _ _ _ _ _ compose joint output ref outputBound]
    calc
      _ = action matrix input output ref := by
        unfold action
        apply Qleisli.Exact.sum_map_congr
        intro col member
        change entry matrix output col * action initial.operator joint col ref =
          entry matrix output col * input col ref
        rw [start col ref (shape.1 ▸ List.mem_range.mp member)]
      _ = _ := ReconstructedAction.event_action dependencies operation matrix afterCharge afterMatrix matrixRead
        input output ref outputBound

/-- Use the matrix read that actually supplied the provider, its exact initial
identity, and the event list read from the same original program. -/
theorem reconstructed_action (dependencies : List Dependency) (program : Semantics.Observation.Program)
    (actual : Matrix) (work left : Nat)
    (checked : (Raw.BranchFunction.reconstruct dependencies program).run work = (.ok actual,left))
    (prepared : Semantics.Observation.Prepared) (reader : Semantics.Observation.read program = some prepared)
    (operations : List Event) (pureEvents : prepared.events = operations.map Semantics.Observation.Event.pure)
    {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference)
    (bound : row < actual.rows) :
    action actual joint row reference =
      events dependencies operations (fun col => joint col reference) row := by
  obtain ⟨native,initial,final,a,b,c,d,verified,identity,ran,operator,_⟩ :=
    Raw.BranchFunction.reconstruct_execution _ _ _ _ _ checked
  have same := Option.some.inj ((Raw.Observation.verify_postcondition _ _ _ _ _ verified).reader.symm.trans reader)
  rw [same,pureEvents] at ran
  rw [← operator] at bound ⊢
  exact fold_action dependencies _ operations _ final c d ran joint joint (fun r ref inside =>
    identity_action identity joint r ref inside) row reference bound

#print axioms reconstructed_action
end Qleisli.Raw.PureInstrumentAction
