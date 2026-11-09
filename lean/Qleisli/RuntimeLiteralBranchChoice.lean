import Qleisli.RuntimeLiteralHistory

/-! Select the original ordinary arm from the source valuation of the
incoming history. The checked finite row uses precisely those measurement
keys and the bits that the same history contains.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeLiteralBranchChoice
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (Event readOps)
open QleisliKernel.Semantics.OrdinaryValue (lookup)
open Qleisli.Semantics.ObservingAction (History run step merge)
open Qleisli.RuntimeOriginalBranch (Trace branchEvent)
open RuntimeOrdinaryBody (Measurement valuation)
open RuntimeOrdinarySSA (Agreement Values bitValue)

/-- Extract the recorded bits in original source measurement-key order. -/
def measurementBits (measurements : List Measurement) (values : Values) : Option (List Bool) :=
  measurements.mapM fun entry => lookup values entry.output

theorem measurementBits_retains (measurements : List Measurement) {before after : Values} {bits : List Bool}
    (retains : Semantics.OrdinaryValue.Extends before after)
    (read : measurementBits measurements before = some bits) :
    measurementBits measurements after = some bits := by
  unfold measurementBits at *
  induction measurements generalizing bits with
  | nil => exact read
  | cons first rest ih =>
    cases found : lookup before first.output with
    | none => simp [List.mapM_cons,found] at read
    | some bit =>
      cases tail : rest.mapM (fun entry => lookup before entry.output) with
      | none => simp [List.mapM_cons,found,tail] at read
      | some tailBits =>
        simp only [List.mapM_cons,found,tail,bind,Option.bind,pure,Option.some.injEq] at read
        subst bits
        simp [List.mapM_cons,retains _ _ found,ih tail]

private theorem measurement_row {measurements values bits}
    (read : measurementBits measurements values = some bits) :
    bits.length = measurements.length ∧
    ∀ entry ∈ measurements, lookup ((measurements.zip bits).map fun (m,b) => (m.output,b)) entry.output =
      lookup values entry.output := by
  induction measurements generalizing bits with
  | nil =>
    cases read
    simp
  | cons first rest ih =>
    cases head : lookup values first.output with
    | none => simp [measurementBits,List.mapM_cons,head] at read
    | some bit =>
      cases tail : measurementBits rest values with
      | none =>
        unfold measurementBits at tail
        simp [measurementBits,List.mapM_cons,head,tail] at read
      | some tailBits =>
        have row : bits = bit :: tailBits := by
          have restRead := tail
          unfold measurementBits at restRead
          simpa only [measurementBits,List.mapM_cons,head,restRead,bind,Option.bind,pure,Option.some.injEq,eq_comm] using read
        subst bits
        obtain ⟨length,each⟩ := ih tail
        refine ⟨congrArg Nat.succ length,?_⟩
        intro entry member
        by_cases same : first.output = entry.output
        · rw [← same,head]
          simp [lookup]
        · have restMember : entry ∈ rest := by
            rcases List.mem_cons.mp member with rfl | found
            · exact (same rfl).elim
            · exact found
          simpa only [List.zip_cons_cons,List.map_cons,lookup,List.find?_cons,
            beq_eq_false_iff_ne.mpr same] using each entry restMember

/-- The finite condition-checker's row and the incoming source valuation
are identical on all keys once the original bits have been read. -/
theorem reference_measurement_row {measurements values bits}
    (read : measurementBits measurements values = some bits) (inputs : List Nat) :
    bits.length = measurements.length ∧
      RuntimeBranchCondition.reference inputs measurements bits = valuation inputs measurements values := by
  obtain ⟨width,each⟩ := measurement_row read
  refine ⟨width,?_⟩
  unfold RuntimeBranchCondition.reference valuation
  congr 1
  funext origin calls owner
  cases found : measurements.find? (fun entry =>
      decide (entry.origin = origin ∧ entry.calls = calls ∧ entry.owner = owner)) with
  | none => rfl
  | some entry =>
    simp only [bind,Option.bind]
    rw [each entry (List.mem_of_find?_eq_some found)]

def sourceChoice (reference : RuntimeOrdinarySSA.Valuation) (condition : RuntimeOrdinarySSA.Expression) : Option Bool :=
  match Semantics.SourceOrdinary.evaluate reference condition with
  | some 0 => some false
  | some 1 => some true
  | _ => none

/-- The selected source condition reads the same values and measurement keys
as the actual Raw branch. The independently read event uses the actual child
fuel and runs that arm's events, then applies the literal parent merge. -/
theorem branch_choice {sources rootOwner rootName owner name dependencies program block offset path source actual before}
    (checked : @RuntimeBranchCondition.Checked sources rootOwner rootName owner name dependencies program
      block offset path source actual before)
    (trace : Trace actual) (inputs : List Nat) (member : inputs ∈ checked.inputs.rows) (history : History)
    {bits : List Bool} (bitsRead : measurementBits before.measurements history.values = some bits)
    (agrees : Agreement (valuation inputs before.measurements history.values) history.values before.table)
    {events : List Event}
    (read : readOps block.fuel actual.interval.before.quantum.reference ((block.operations.drop offset).take 1) =
      some (actual.interval.after.quantum.reference,events)) :
    ∃ choice, sourceChoice (RuntimeBranchCondition.reference inputs before.measurements bits) checked.required =
      some choice ∧
      run dependencies block.fuel events history =
        (do
          let selected ← run dependencies actual.childFuel (trace.armEvents choice) history
          selected.mapM (merge choice actual.classical)) := by
  obtain ⟨width,reference⟩ := reference_measurement_row bitsRead inputs
  obtain ⟨choice,computed,executed⟩ := RuntimeOriginalBranch.original_branch_step checked trace
    (run dependencies actual.childFuel) inputs member bits width history (reference.symm ▸ agrees)
  refine ⟨choice,?_,?_⟩
  · unfold sourceChoice
    rw [computed]
    cases choice <;> rfl
  · have exactEvents : events = [branchEvent actual trace.left trace.right] :=
      congrArg Prod.snd (Option.some.inj (read.symm.trans trace.parentRead))
    rw [exactEvents,actual.depth,Qleisli.RuntimeLiteralHistory.run_single]
    exact executed

#print axioms branch_choice
end Qleisli.RuntimeLiteralBranchChoice
