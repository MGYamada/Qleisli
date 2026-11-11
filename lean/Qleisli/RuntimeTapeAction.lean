import Qleisli.RawFiniteRows
import Qleisli.RawActionSector
import Qleisli.FiniteMatrixAction
import QleisliKernel.Qirf.SectorForward

/-! Interpret the original trace from a successful structural tape read.
The same event pieces and matching restriction determine each physical
output coordinate, including arbitrary amplitudes of a reference system.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeTapeAction
open QleisliKernel QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open QleisliKernel.FiniteRestriction
open Qleisli.Semantics.RawAction
open Qleisli.RawFiniteRows (OnRows BoundedEvent)

/-- Every read circuit is interpreted in order. An identity reorder only
acts as identity on the finite rows supplied by the original frame. -/
private theorem reorder_action (dependencies : List Dependency) (bits : Nat)
    (values : Nat → ℂ) : OnRows bits (event dependencies (.reorder bits (List.range bits)) values) values := by
  intro row bounded
  unfold event
  calc
    _ = ((List.range (2^bits)).map fun input => if row = input then values input else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro input present
      rw [QleisliKernel.Raw.Sector.gather_identity input bits (List.mem_range.mp present)]
      by_cases same : row = input
      · subst input
        simp
      · simp [same,Ne.symm same]
    _ = values row := Qleisli.Exact.range_delta_sum _ _ _ bounded

private abbrev Targets (bits : Nat) (steps : List Step) : Prop :=
  ∀ step ∈ steps, ∀ axis ∈ QleisliKernel.Finite.targets step.action, axis < bits

private theorem eventPieces_action (dependencies : List Dependency) (bits : Nat)
    (operations : List Event) (pieces : List (List Step))
    (related : QleisliKernel.Exact.ListRel (QleisliKernel.Raw.Sector.EventPiece bits) operations pieces)
    (bounded : Targets bits pieces.flatten) (left right : Nat → ℂ)
    (same : OnRows bits left right) :
    OnRows bits (events dependencies operations left) (circuit dependencies pieces.flatten right) := by
  induction operations generalizing pieces left right with
  | nil =>
    cases pieces with
    | nil => exact same
    | cons first rest => exact False.elim related
  | cons head tail ih =>
    cases pieces with
    | nil => exact False.elim related
    | cons first rest =>
      have headBounds : Targets bits first := by
        intro step present
        exact bounded step (List.mem_append_left _ present)
      have tailBounds : Targets bits rest.flatten := by
        intro step present
        exact bounded step (List.mem_append_right _ present)
      rcases related.1 with original | ⟨original,empty⟩
      · subst head
        have inputs := (BoundedEvent.circuit bits first headBounds).congr dependencies left right same
        simpa only [events,List.foldl_cons,event,circuit,List.flatten_cons,List.foldl_append] using
          ih rest related.2 tailBounds _ _ inputs
      · subst head first
        have inputs : OnRows bits (event dependencies (.reorder bits (List.range bits)) left) right :=
          fun row inside => (reorder_action dependencies bits left row inside).trans (same row inside)
        simpa only [events,List.foldl_cons,List.flatten_cons,List.nil_append] using
          ih rest related.2 tailBounds _ _ inputs

/-- The optimized forward evaluator has the action of every literal event in
the original checked body. Reference columns and the full scalar are retained. -/
theorem forward_action (dependencies : List Dependency) (bits : Nat)
    (program : QleisliKernel.Semantics.Observation.Program)
    (physical : QleisliKernel.Semantics.Exact.Matrix)
    (binding : QleisliKernel.Qirf.SectorForward.LiteralBinding dependencies bits program physical) :
    ∃ prepared operations,
      QleisliKernel.Semantics.Observation.read program = some prepared ∧
      prepared.events = operations.map QleisliKernel.Semantics.Observation.Event.pure ∧
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
        row < physical.rows →
        Qleisli.Semantics.Exact.action physical joint row reference =
          events dependencies operations (fun input => joint input reference) row := by
  obtain ⟨prepared,operations,reader,_,_,_,original,pieces,steps,work,left,related,flat,computed⟩ :=
    binding.original
  refine ⟨prepared,operations,reader,original,?_⟩
  intro Reference joint row reference inside
  let subject : Circuit := ⟨[.bits bits],steps⟩
  have valid := (QleisliKernel.Finite.circuitMatrix_columns dependencies subject physical work left computed).1
  simp only [QleisliKernel.Finite.circuitValid,Bool.and_eq_true] at valid
  have targets : Targets bits steps := by
    intro step present axis member
    have validStep := List.all_eq_true.mp valid.2 step present
    simp only [QleisliKernel.Finite.stepValid,QleisliKernel.Finite.axesValid,Bool.and_eq_true] at validStep
    exact of_decide_eq_true (List.all_eq_true.mp validStep.1.2.1.2 axis (List.mem_append_right _ member))
  have rows := (Qleisli.Finite.circuitMatrix_pull dependencies subject physical work left computed).1
  have rowBound : row < 2^bits := rows ▸ inside
  have action := Qleisli.Finite.circuitMatrix_action dependencies subject physical work left computed
    joint row reference inside
  change _ = circuit dependencies steps (fun input => joint input reference) row at action
  rw [flat] at targets action
  exact action.trans (eventPieces_action dependencies bits operations pieces related targets _ _
    (fun _ _ => rfl) row rowBound).symm

/-- Successful structural tape extraction binds the executable result to the
independent original Raw reader and to the exact finite action. -/
theorem program_tape (dependencies : List Dependency) (shape : QleisliKernel.Raw.Sector.TapeInterface)
    (program : Program) (tape : QleisliKernel.Raw.Sector.Tape)
    (binding : QleisliKernel.Raw.Sector.ForTapeBinding dependencies shape program tape)
    (bounded : Targets shape.bits tape.steps) (values : Nat → ℂ) :
    ∃ actual, Qleisli.Semantics.RawAction.program dependencies program values = some actual ∧
      OnRows shape.bits actual (circuit dependencies tape.steps values) := by
  obtain ⟨_,_,_,original,_,pieces,related,flat⟩ := binding
  refine ⟨events dependencies tape.prepared.events values,?_,?_⟩
  · simp only [Qleisli.Semantics.RawAction.program,original,bind,Option.bind,QleisliKernel.Raw.Prepared.reference,pure]
  · rw [flat] at bounded ⊢
    exact eventPieces_action dependencies shape.bits _ pieces related bounded values values (fun _ _ => rfl)

private theorem packed_bound {selector target label row : Nat} (low : label < 2^selector)
    (high : row < 2^target) : pack selector label row < 2^(selector+target) := by
  rw [Nat.pow_add]
  calc
    pack selector label row < 2^selector + 2^selector*row := Nat.add_lt_add_right low _
    _ = 2^selector*(row+1) := by rw [Nat.mul_add,Nat.mul_one,Nat.add_comm]
    _ ≤ 2^selector*2^target := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt high)

/-- A successful literal match determines the original Raw action at a
physical selector label, with no sector matrix reconstruction. -/
theorem program_sector {Reference : Type} (dependencies : List Dependency) (selector target : Basis)
    (program : Program) (tape : QleisliKernel.Raw.Sector.Tape)
    (binding : QleisliKernel.Raw.Sector.ForTapeBinding dependencies (.pair selector target) program tape)
    (bounded : Targets (width selector+width target) tape.steps)
    {label : Nat} {expected : List Step} (matched : TapeMatch (width selector) label tape.steps expected)
    (joint : Nat → Reference → ℂ) (reference : Reference) :
    ∃ actual, Qleisli.Semantics.RawAction.program dependencies program (fun row => joint row reference) = some actual ∧
      ∀ row, row < 2^width target →
        actual (pack (width selector) label row) =
          circuit dependencies expected (fun input => joint (pack (width selector) label input) reference) row := by
  obtain ⟨actual,read,meaning⟩ := program_tape dependencies (.pair selector target) program tape
    binding bounded (fun row => joint row reference)
  refine ⟨actual,read,fun row rowBound => (meaning _ (packed_bound matched.bounded rowBound)).trans ?_⟩
  exact congrFun (Qleisli.Semantics.RawAction.Sector.restrictSteps_slice dependencies tape.steps expected
    (width selector) label matched.bounded matched.restriction (fun row => joint row reference)) row

/-- A match at selector width zero compares the complete ordered tape. The
original finite action then composes the literal before, selection and after
tapes in that order, on arbitrary joint reference amplitudes. -/
theorem program_ordered {Reference : Type} (dependencies : List Dependency)
    (shape : QleisliKernel.Raw.Sector.TapeInterface) (program : Program) (tape : QleisliKernel.Raw.Sector.Tape)
    (binding : QleisliKernel.Raw.Sector.ForTapeBinding dependencies shape program tape)
    (bounded : Targets shape.bits tape.steps)
    {before selection after : List Step} (matched : TapeMatch 0 0 tape.steps (before ++ selection ++ after))
    (joint : Nat → Reference → ℂ) (reference : Reference) :
    ∃ actual, Qleisli.Semantics.RawAction.program dependencies program (fun row => joint row reference) = some actual ∧
      OnRows shape.bits actual (circuit dependencies after
        (circuit dependencies selection (circuit dependencies before (fun row => joint row reference)))) := by
  obtain ⟨actual,read,meaning⟩ := program_tape dependencies shape program tape binding bounded (fun row => joint row reference)
  refine ⟨actual,read,fun row rowBound => (meaning row rowBound).trans ?_⟩
  have exactOrder := congrFun (Qleisli.Semantics.RawAction.Sector.restrictSteps_slice dependencies tape.steps
    (before ++ selection ++ after) 0 0 matched.bounded matched.restriction (fun row => joint row reference)) row
  have inputSlice : Qleisli.Semantics.RawAction.Sector.slice 0 0 (fun row => joint row reference) =
      (fun row => joint row reference) := by
    funext index
    simp [Qleisli.Semantics.RawAction.Sector.slice,pack]
  rw [inputSlice] at exactOrder
  simpa only [Qleisli.Semantics.RawAction.Sector.slice,pack,Nat.pow_zero,Nat.one_mul,Nat.zero_add,
    circuit,List.foldl_append] using exactOrder

#print axioms program_tape
#print axioms forward_action
#print axioms program_sector
#print axioms program_ordered
end Qleisli.RuntimeTapeAction
