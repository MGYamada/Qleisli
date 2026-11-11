import QleisliKernel.Raw.BranchFunction
import QleisliKernel.Raw.Sector

/-! Evaluate the original forward arm using the already checked instrument
trace. Straight-line, width-preserving circuits share the finite tape
evaluator. Other original event forms use the complete instrument evaluator.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SectorForward
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics
open QleisliKernel.Semantics.Finite (Dependency Step)
open QleisliKernel.Semantics.Exact (Matrix)

private def literalEvent (bits : Nat) : Observation.Event → Option Semantics.Raw.Event
  | .pure event => if Raw.Sector.eventValid bits event then some event else none
  | _ => none

private def tapeLength (events : List Semantics.Raw.Event) : Nat :=
  (events.map fun event => match event with
    | .circuit _ steps => steps.length
    | _ => 0).sum

private def choose (bits : Nat) (program : Observation.Program) (prepared : Observation.Prepared) :
    Option (List Semantics.Raw.Event × Nat) := do
  if !(program.effect == .unitary && prepared.inputBits == bits &&
      prepared.state.frame.length == bits) then none else
  let events ← prepared.events.mapM (literalEvent bits)
  let count := tapeLength events
  if count ≤ 1024 then some (events,count) else none

private theorem literalEvents_original (bits : Nat) (original : List Observation.Event)
    (events : List Semantics.Raw.Event)
    (read : original.mapM (literalEvent bits) = some events) : original = events.map .pure := by
  induction original generalizing events with
  | nil =>
    have same : [] = events := Option.some.inj read
    subst events
    rfl
  | cons first rest ih =>
    simp only [List.mapM_cons] at read
    obtain ⟨event,selected,read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨tail,restRead,returned⟩ := Option.bind_eq_some_iff.mp read
    have same : first = .pure event := by
      cases first <;> simp only [literalEvent] at selected
      · split at selected <;> simp_all
      all_goals cases selected
    have outputs : event :: tail = events := Option.some.inj returned
    subst events
    rw [same,ih _ restRead]
    rfl

private theorem choose_bound (bits : Nat) (program : Observation.Program) (prepared : Observation.Prepared)
    (events : List Semantics.Raw.Event) (count : Nat)
    (chosen : choose bits program prepared = some (events,count)) :
    program.effect = .unitary ∧ prepared.inputBits = bits ∧
      prepared.state.frame.length = bits ∧ prepared.events = events.map .pure := by
  unfold choose at chosen
  split at chosen
  · cases chosen
  · rename_i eligible
    have widths : (program.effect == .unitary && prepared.inputBits == bits &&
        prepared.state.frame.length == bits) = true := by
      cases dimensions : (program.effect == .unitary && prepared.inputBits == bits &&
          prepared.state.frame.length == bits) with
      | false => simp [dimensions] at eligible
      | true => rfl
    obtain ⟨literal,read,returned⟩ := Option.bind_eq_some_iff.mp chosen
    dsimp only at returned
    split at returned
    · obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj returned)
      simp only [Bool.and_eq_true,beq_iff_eq] at widths
      exact ⟨widths.1.1,widths.1.2,widths.2,literalEvents_original _ _ _ read⟩
    · cases returned

private def readLiteral (dependencies : List Dependency) (bits count : Nat)
    (events : List Semantics.Raw.Event) : WorkM Matrix := do
  exactWork (Exact.charge (2*(count+1)))
  let steps ← lift (Raw.Sector.readEvents bits events)
  let matrix ← circuitMatrix dependencies ⟨[.bits bits],steps⟩
  matrixRead matrix

/-- Choose the evaluator from the checked original trace before executing
either evaluator. A selected tape's arithmetic or work failure is terminal. -/
def read (dependencies : List Dependency) (bits : Nat) (program : Observation.Program) : WorkM Matrix := do
  let checked ← Raw.Observation.verify dependencies program
  exactWork (Exact.charge (16*(checked.prepared.events.length+1)))
  match choose bits program checked.prepared with
  | none => Raw.BranchFunction.reconstructChecked dependencies checked
  | some (events,count) => readLiteral dependencies bits count events

structure LiteralBinding (dependencies : List Dependency) (bits : Nat)
    (program : Observation.Program) (physical : Matrix) : Prop where
  original : ∃ prepared events,
    Observation.read program = some prepared ∧
    program.effect = .unitary ∧ prepared.inputBits = bits ∧
    prepared.state.frame.length = bits ∧ prepared.events = events.map .pure ∧
    ∃ pieces steps work left,
      Exact.ListRel (Raw.Sector.EventPiece bits) events pieces ∧ steps = pieces.flatten ∧
      (circuitMatrix dependencies ⟨[.bits bits],steps⟩).run work = (.ok physical,left)
  admitted : Exact.Matrix.Admitted physical

inductive Binding (dependencies : List Dependency) (bits : Nat)
    (program : Observation.Program) (physical : Matrix) : Prop where
  | instrument (computed : ∃ checked work afterVerify beforeEvaluation left,
      (Raw.Observation.verify dependencies program).run work = (.ok checked,afterVerify) ∧
      (Raw.BranchFunction.reconstructChecked dependencies checked).run beforeEvaluation = (.ok physical,left))
  | literal (computed : LiteralBinding dependencies bits program physical)

theorem read_bound (dependencies : List Dependency) (bits : Nat) (program : Observation.Program)
    (physical : Matrix) (work left : Nat)
    (ok : (read dependencies bits program).run work = (.ok physical,left)) :
    Binding dependencies bits program physical := by
  obtain ⟨checked,afterVerify,verified,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,start,_,ran⟩ := bind_success _ _ _ _ _ rest
  split at ran
  · exact .instrument ⟨checked,work,afterVerify,start,left,verified,ran⟩
  · rename_i events count selected
    have reader := (Raw.Observation.verify_postcondition _ _ _ _ _ verified).reader
    obtain ⟨effect,inputs,outputs,original⟩ := choose_bound _ _ _ _ _ selected
    obtain ⟨_,beforeTape,_,ran⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨steps,beforeMatrix,readTape,ran⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨matrix,beforeAdmission,computed,admission⟩ := bind_success _ _ _ _ _ ran
    have same := (matrixRead_value _ _ _ _ admission).1
    subst matrix
    obtain ⟨pieces,related,flattened⟩ := Raw.Sector.readEvents_bound _ _ _ (lift_success _ _ _ _ readTape).1
    exact .literal ⟨⟨checked.prepared,events,reader,effect,inputs,outputs,original,
      pieces,steps,beforeMatrix,beforeAdmission,related,flattened,computed⟩,
      matrixRead_admitted _ _ _ _ admission⟩

end QleisliKernel.Qirf.SectorForward
