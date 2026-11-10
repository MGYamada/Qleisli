import QleisliKernel.Qirf.RuntimeBodyQueries
import QleisliKernel.Raw.Ownership
import Mathlib.Data.List.Perm.Subperm

/-! Recover the original indexed handler reads of a successful coherent arm
fold, retaining their intermediate values and exact work positions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSelectionArmTrace
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf QleisliKernel.SourceTypes
open RuntimeBodyQueries (Mode)
open RuntimeBodyPlan (Queues)

inductive Trace {Index State : Type} (Data : Index → Type)
    (step : (index : Index) → Data index → State → WorkM State) :
    List Index → State → State → Nat → Nat → Prop where
  | nil (state work) : Trace Data step [] state state work work
  | cons {index rest initial middle final work budget left} (data : Data index)
      (read : (step index data initial).run work = (.ok middle,budget))
      (tail : Trace Data step rest middle final budget left) :
      Trace Data step (index::rest) initial final work left

/-- A projection that appends one value per successful read preserves the
prefix and supplies an exact indexed read for every newly appended value. -/
theorem Trace.appended_read {Index State : Type} {Value : Type*} {Data : Index → Type}
    {step : (index : Index) → Data index → State → WorkM State}
    (project : State → List Value) (Produced : (index : Index) → Data index → Value → Prop)
    (append : ∀ index data initial middle work budget,
      (step index data initial).run work = (.ok middle,budget) →
      ∃ value, project middle = project initial ++ [value] ∧ Produced index data value)
    {indices initial final work left}
    (trace : Trace Data step indices initial final work left) :
    ∃ values : List Value, project final = project initial ++ values ∧
      ∃ length : values.length = indices.length,
        ∀ position (bound : position < indices.length),
          ∃ (data : Data indices[position]) (before after : State) (incoming outgoing : Nat),
            (step indices[position] data before).run incoming = (.ok after,outgoing) ∧
              Produced indices[position] data (values[position]'(length.symm ▸ bound)) := by
  induction trace with
  | nil state work =>
    refine ⟨[],(List.append_nil _).symm,rfl,?_⟩
    intro _ bound
    simp at bound
  | @cons index rest initial middle final work budget left data read tail ih =>
    obtain ⟨value,appended,produced⟩ := append index data initial middle work budget read
    obtain ⟨values,assembled,length,atPosition⟩ := ih
    refine ⟨value :: values,?_,by simp only [List.length_cons,length],?_⟩
    · rw [assembled,appended,List.append_assoc]
      rfl
    intro position bound
    cases position with
    | zero => exact ⟨data,initial,middle,work,budget,read,produced⟩
    | succ position =>
      exact atPosition position (Nat.lt_of_succ_lt_succ bound)

private theorem fresh_trace {Index State : Type} (step : Index → State → WorkM State)
    (indices : List Index) (initial final : State) (work left : Nat)
    (read : (indices.foldlM (fun state index => step index state) initial).run work = (.ok final,left)) :
    Trace (fun _ => Unit) (fun index _ => step index) indices initial final work left := by
  induction indices generalizing initial work with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ read
    exact .nil _ _
  | cons index rest ih =>
    simp only [List.foldlM_cons] at read
    obtain ⟨middle,budget,first,tail⟩ := bind_success _ _ _ _ _ read
    exact .cons () first (ih middle budget tail)

/-- Both modes preserve the actual indexed arm reads. The planned mode
retains the plan argument consumed at each original table index. -/
theorem foldArms_trace {artifact : Artifact} (mode : Mode artifact)
    {owner name offset selector target State}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (step : (index : Fin table.arms.length) →
      mode.GraphData (table.arms[index]).operation.graph OperationAccess.controllable
        (.arm (table.arms[index]).operation) → State → WorkM State)
    (data : mode.ArmsData table) (initial final : State) (work left : Nat)
    (read : (RuntimeBodyQueries.foldArms mode table step data initial).run work = (.ok final,left)) :
    Trace (fun index => mode.GraphData (table.arms[index]).operation.graph OperationAccess.controllable
      (.arm (table.arms[index]).operation)) step (List.finRange table.arms.length) initial final work left := by
  cases mode with
  | fresh =>
    have actual := fresh_trace (fun index => step index ()) _ initial final work left read
    have same : (fun index (_ : Unit) => step index ()) = step := by
      funext index data
      cases data
      rfl
    simpa only [same] using actual
  | planned preparation =>
    rcases data with ⟨before,after,plans⟩
    unfold RuntimeBodyQueries.foldArms at read
    dsimp (config := {zeta := false}) only at read
    extract_lets visit at read
    have planned (fuel : Nat) (indices : List (Fin table.arms.length))
        {before after : Queues} (plans : RuntimeBodyPlan.Arms preparation table indices before after)
        (start finish : State) (work left : Nat)
        (read : (visit fuel indices plans start).run work = (.ok finish,left)) :
        Trace (fun index => (Mode.planned preparation).GraphData (table.arms[index]).operation.graph
          OperationAccess.controllable (.arm (table.arms[index]).operation))
          step indices start finish work left := by
      induction fuel generalizing indices before after start finish work left with
      | zero =>
        cases plans with
        | nil =>
          obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ read
          exact .nil _ _
        | cons cut graph tail => cases read
      | succ fuel ih =>
        cases plans with
        | nil =>
          obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ read
          exact .nil _ _
        | @cons index rest before after cut graph tail =>
          change (do
            let middle ← step index ⟨cut.implementations,cut.references,graph⟩ start
            visit fuel rest tail middle).run work = (.ok finish,left) at read
          obtain ⟨middle,budget,first,remaining⟩ := bind_success _ _ _ _ _ read
          exact .cons ⟨cut.implementations,cut.references,graph⟩ first
            (ih rest tail middle finish budget left remaining)
    exact planned _ _ plans initial final work left read

/-- The checked source table enumerates the entire selector domain, while
retaining the written arm order. -/
theorem ordinal_permutation {sources owner name offset selector target}
    (table : QuantumArms.Table sources owner name offset selector target) :
    (table.arms.map (·.label.ordinal)).Perm (List.range table.layout.labels.length) := by
  let ordinals := table.arms.map (·.label.ordinal)
  have complete := table.complete
  simp only [QuantumArms.partition,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at complete
  have distinct : ordinals.Nodup := Raw.Ownership.unique_nodup _ complete.2
  have bounded : ordinals ⊆ List.range table.layout.labels.length :=
    fun ordinal member => List.mem_range.mpr (complete.1.2 ordinal member)
  obtain ⟨reordered,permutation,contained⟩ := List.subperm_iff.mp (distinct.subperm bounded)
  have length : ordinals.length = reordered.length :=
    (beq_iff_eq.mp complete.1.1).trans (permutation.length_eq.trans List.length_range).symm
  change ordinals.Perm (List.range table.layout.labels.length)
  rw [contained.eq_of_length length]
  exact permutation

/-- A semantic selector ordinal names precisely one original written arm.
This supplies the connection between source-order consumption and the
ordinal-order logical table without treating their indices as equal. -/
theorem arm_at_ordinal {sources owner name offset selector target}
    (table : QuantumArms.Table sources owner name offset selector target)
    (ordinal : Nat) (bounded : ordinal < table.layout.labels.length) :
    ∃ index : Fin table.arms.length, table.arms[index].label.ordinal = ordinal ∧
      ∀ other : Fin table.arms.length, table.arms[other].label.ordinal = ordinal → other = index := by
  let ordinals := table.arms.map (·.label.ordinal)
  have permutation := ordinal_permutation table
  have member : ordinal ∈ ordinals := permutation.mem_iff.mpr (List.mem_range.mpr bounded)
  obtain ⟨index,inside,found⟩ := List.getElem_of_mem member
  have written : index < table.arms.length := by
    simpa only [ordinals,List.length_map] using inside
  have selected : table.arms[index].label.ordinal = ordinal := by
    simpa only [ordinals,List.getElem_map] using found
  refine ⟨⟨index,written⟩,selected,?_⟩
  intro other same
  have distinct : ordinals.Nodup := permutation.nodup_iff.mpr List.nodup_range
  have otherInside : other.val < ordinals.length := by
    simpa only [ordinals,List.length_map] using other.isLt
  have equal : ordinals[other.val] = ordinals[index] := by
    simpa only [ordinals,List.getElem_map] using same.trans selected.symm
  exact Fin.ext ((List.getElem_inj distinct).mp equal)

/-- The exact value at each selector ordinal is backed by the original
handler read at the corresponding written position. The final projection
still has source order, as required by the enclosing node's indexed reads. -/
theorem ordinal_read {artifact : Artifact} (mode : Mode artifact)
    {owner name offset selector target State Value}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (step : (index : Fin table.arms.length) →
      mode.GraphData (table.arms[index]).operation.graph OperationAccess.controllable
        (.arm (table.arms[index]).operation) → State → WorkM State)
    (project : State → List Value)
    (Produced : (index : Fin table.arms.length) →
      mode.GraphData (table.arms[index]).operation.graph OperationAccess.controllable
        (.arm (table.arms[index]).operation) → Value → Prop)
    (append : ∀ index data initial middle work budget,
      (step index data initial).run work = (.ok middle,budget) →
      ∃ value, project middle = project initial ++ [value] ∧ Produced index data value)
    (data : mode.ArmsData table) (initial final : State) (work left : Nat)
    (read : (RuntimeBodyQueries.foldArms mode table step data initial).run work = (.ok final,left)) :
    ∃ values : List Value, project final = project initial ++ values ∧
      ∃ length : values.length = table.arms.length,
        ∀ ordinal : Fin table.layout.labels.length,
          ∃ (index : Fin table.arms.length) (graph : mode.GraphData (table.arms[index]).operation.graph
            OperationAccess.controllable (.arm (table.arms[index]).operation))
            (before after : State) (incoming outgoing : Nat),
            table.arms[index].label.ordinal = ordinal.val ∧
            (step index graph before).run incoming = (.ok after,outgoing) ∧
            Produced index graph (values[index.val]'(length.symm ▸ index.isLt)) := by
  obtain ⟨values,assembled,count,atPosition⟩ :=
    (foldArms_trace mode table step data initial final work left read).appended_read project Produced append
  refine ⟨values,assembled,count.trans List.length_finRange,?_⟩
  intro ordinal
  obtain ⟨index,selected,_unique⟩ := arm_at_ordinal table ordinal.val ordinal.isLt
  have inRange : index.val < (List.finRange table.arms.length).length :=
    List.length_finRange.symm ▸ index.isLt
  have same : (List.finRange table.arms.length)[index.val] = index := by
    rw [List.getElem_finRange]
    exact Fin.ext rfl
  have actual := atPosition index.val inRange
  rw [same] at actual
  obtain ⟨graph,before,after,incoming,outgoing,ran,produced⟩ := actual
  exact ⟨index,graph,before,after,incoming,outgoing,selected,ran,produced⟩

#print axioms foldArms_trace
#print axioms arm_at_ordinal
#print axioms ordinal_read
end Qleisli.RuntimeSelectionArmTrace
