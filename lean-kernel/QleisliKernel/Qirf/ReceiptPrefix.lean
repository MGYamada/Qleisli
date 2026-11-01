import QleisliKernel.Qirf.FreshEntries

/-! An actual successful graph prefix retains its occupied receipt slots in
the final snapshot. Entire historical/final vectors need not be equal.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.ReceiptTransport
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.ObservingFunction

/-- The literal step of Graph.makeRanks, factored only inside this proof. -/
private def rankStep (size : Nat) (state : Nat × Array Nat) (node : Nat) :
    Option (Nat × Array Nat) := do
  let previous ← state.2[node]?
  if previous != size then none
  else some (state.1 + 1,state.2.set! node state.1)

private theorem rankStep_success {size state node next}
    (ok : rankStep size state node = some next) :
    state.2[node]? = some size ∧ next = (state.1+1,state.2.set! node state.1) := by
  cases found : state.2[node]? with
  | none => simp [rankStep,found] at ok
  | some previous =>
    by_cases fresh : previous = size
    · subst previous
      exact ⟨rfl,by simpa [rankStep,found] using ok.symm⟩
    · simp [rankStep,found,fresh] at ok

/-- A successful rank fold never visits a slot already marked non-sentinel. -/
private theorem rankFold_marked (size : Nat) (nodes : List Nat)
    (state final : Nat × Array Nat) (index marker : Nat)
    (present : state.2[index]? = some marker) (marked : marker ≠ size)
    (ok : nodes.foldlM (rankStep size) state = some final) :
    index ∉ nodes ∧ final.2[index]? = some marker := by
  induction nodes generalizing state with
  | nil =>
    have same : state = final := by simpa using ok
    subst final
    exact ⟨by simp,present⟩
  | cons node rest ih =>
    cases step : rankStep size state node with
    | none => simp [List.foldlM_cons,step] at ok
    | some next =>
      have tail : rest.foldlM (rankStep size) next = some final := by
        simpa [List.foldlM_cons,step] using ok
      obtain ⟨fresh,nextValue⟩ := rankStep_success step
      have different : node ≠ index := by
        intro same
        subst node
        exact marked (Option.some.inj (present.symm.trans fresh))
      have retained : next.2[index]? = some marker := by
        rw [nextValue]
        simp [Array.set!_eq_setIfInBounds,different,present]
      obtain ⟨absent,held⟩ := ih next retained tail
      exact ⟨by simp [Ne.symm different,absent],held⟩

private theorem rankFold_nodup (size : Nat) (nodes : List Nat)
    (state final : Nat × Array Nat) (capacity : state.1+nodes.length ≤ size)
    (ok : nodes.foldlM (rankStep size) state = some final) : nodes.Nodup := by
  induction nodes generalizing state with
  | nil => simp
  | cons node rest ih =>
    cases step : rankStep size state node with
    | none => simp [List.foldlM_cons,step] at ok
    | some next =>
      have tail : rest.foldlM (rankStep size) next = some final := by
        simpa [List.foldlM_cons,step] using ok
      obtain ⟨fresh,nextValue⟩ := rankStep_success step
      have inside : node < state.2.size := (Array.getElem?_eq_some_iff.mp fresh).choose
      have marked : next.2[node]? = some state.1 := by
        rw [nextValue]
        simp [Array.set!_eq_setIfInBounds,inside]
      have beforeEnd : state.1 < size := by simp only [List.length_cons] at capacity; omega
      have absent := (rankFold_marked size rest next final node state.1 marked
        (Nat.ne_of_lt beforeEnd) tail).1
      have bounded : next.1+rest.length ≤ size := by
        rw [nextValue]
        simp only [List.length_cons] at capacity
        omega
      exact List.nodup_cons.mpr ⟨absent,ih next bounded tail⟩

/-- This premise is the existing executable rank check, not a proposed order flag. -/
theorem makeRanks_nodup (size : Nat) (order ranks : Array Nat)
    (ok : Hierarchical.Graph.makeRanks size order = some ranks) : order.toList.Nodup := by
  unfold Hierarchical.Graph.makeRanks at ok
  split at ok
  next wrong => contradiction
  next right =>
    have sameSize : order.size = size := by simpa using right
    change (do
      let state ← order.foldlM (rankStep size) (0,Array.replicate size size)
      pure state.2) = some ranks at ok
    cases folded : order.foldlM (rankStep size) (0,Array.replicate size size) with
    | none => simp [folded] at ok
    | some final =>
      have run : order.toList.foldlM (rankStep size) (0,Array.replicate size size) = some final := by
        simpa only [Array.foldlM_toList] using folded
      exact rankFold_nodup size order.toList _ final (by simp [sameSize]) run

theorem graphCheck_nodup {nodes roots order schedule}
    (ok : Hierarchical.Graph.check nodes roots order = .ok schedule) : order.toList.Nodup :=
  makeRanks_nodup nodes.size order schedule.ranks
    (Hierarchical.Graph.check_conditions _ _ _ _ ok).2.1

theorem node_unchanged {artifact slots node next index}
    (checked : CheckedNode artifact slots node next)
    (different : node ≠ artifact.programs.size+index) : next[index]? = slots[index]? := by
  cases checked with
  | program => rfl
  | entry entry actual receipt a b c d outside found decoded ready verified =>
    have unequal : node-artifact.programs.size ≠ index := by omega
    simp [Array.set!_eq_setIfInBounds,unequal]

theorem graph_unchanged {artifact slots nodes final index}
    (checked : CheckedGraph artifact slots nodes final)
    (absent : artifact.programs.size+index ∉ nodes) : final[index]? = slots[index]? := by
  induction checked with
  | nil => rfl
  | cons slots node rest next final step remaining ih =>
    have head : node ≠ artifact.programs.size+index := by
      intro same
      exact absent (by simp [same])
    have tail : artifact.programs.size+index ∉ rest := by
      intro member
      exact absent (List.mem_cons_of_mem _ member)
    exact (ih tail).trans (node_unchanged step head)

theorem fresh_present_written {artifact nodes final index receipt}
    (checked : CheckedGraph artifact (Array.replicate artifact.entries.size none) nodes final)
    (present : final[index]?.join = some receipt) : artifact.programs.size+index ∈ nodes := by
  by_cases held : artifact.programs.size+index ∈ nodes
  · exact held
  · have same := graph_unchanged checked held
    rw [same] at present
    by_cases inside : index < artifact.entries.size <;> simp [inside] at present

theorem graph_split {artifact slots final} (frontNodes suffix : List Nat)
    (checked : CheckedGraph artifact slots (frontNodes++suffix) final) :
    ∃ middle, CheckedGraph artifact slots frontNodes middle ∧ CheckedGraph artifact middle suffix final := by
  induction frontNodes generalizing slots with
  | nil => exact ⟨slots,.nil slots,by simpa using checked⟩
  | cons node rest ih =>
    cases checked with
    | cons slots node remaining next final step tail =>
      obtain ⟨middle,front,back⟩ := ih tail
      exact ⟨middle,.cons _ _ _ _ _ step front,back⟩

/-- Holes may be filled; only a receipt already present has to stay identical. -/
def Extends (previous final : Slots) : Prop :=
  ∀ (index : Nat) (receipt : Receipt), previous[index]?.join = some receipt → final[index]?.join = some receipt

theorem fresh_prefix_extends {artifact frontNodes suffix previous final}
    (front : CheckedGraph artifact (Array.replicate artifact.entries.size none) frontNodes previous)
    (back : CheckedGraph artifact previous suffix final)
    (unique : (frontNodes++suffix).Nodup) : Extends previous final := by
  intro index receipt present
  have written := fresh_present_written front present
  have absent : artifact.programs.size+index ∉ suffix := by
    intro member
    exact (List.nodup_append.mp unique).2.2 _ written _ member rfl
  have same := graph_unchanged back absent
  simpa only [same] using present

/-- The order, graph and frontNodes are all tied to this actual successful checker run.
No separate graph is reconstructed and no producer-supplied uniqueness assertion
is accepted. -/
theorem successful_prefix {artifact order extra roots final work left}
    (ok : (checkGraphReceiptsFromRoots artifact order extra roots).run work = (.ok final,left))
    (frontNodes suffix : List Nat) (split : order.toList = frontNodes++suffix) :
    ∃ previous,
      CheckedGraph artifact (Array.replicate artifact.entries.size none) frontNodes previous ∧
      CheckedGraph artifact previous suffix final ∧ Extends previous final := by
  have graph := (checkGraphReceiptsFromRoots_fresh _ _ _ _ _ _ _ ok).1
  obtain ⟨schedule,scheduled,_⟩ := checkGraphReceiptsFromRoots_schedule _ _ _ _ _ _ _ ok
  have unique := graphCheck_nodup scheduled
  rw [split] at graph unique
  obtain ⟨previous,front,back⟩ := graph_split frontNodes suffix graph
  exact ⟨previous,front,back,fresh_prefix_extends front back unique⟩

/-- Ready is the historical node's actual check. Both implementation and
specification need this separately; a final vector alone supplies no history. -/
theorem ready_references {previous final program}
    (extension : Extends previous final) (ready : Qirf.ready previous program = true)
    (index : Nat) (referenced : index ∈ Semantics.ObservingFunction.references 65 program.operations) :
    ∃ receipt, previous[index]?.join = some receipt ∧ final[index]?.join = some receipt := by
  have present : (previous[index]?.join).isSome = true :=
    List.all_eq_true.mp ready index referenced
  cases found : previous[index]?.join with
  | none => simp [found] at present
  | some receipt => exact ⟨receipt,rfl,extension index receipt found⟩

/-- Lookup equality, not equality of the entire dependency vectors. -/
theorem before_dependency {slots : Slots} {index : Nat} {receipt : Receipt}
    (present : slots[index]?.join = some receipt) :
    ((Qirf.before slots).map Receipt.dependency)[index]? = some receipt.dependency := by
  unfold Qirf.before
  simp only [List.getElem?_map,Array.getElem?_toList]
  cases found : slots[index]? with
  | none => simp [found] at present
  | some value =>
    cases value with
    | none => simp [found] at present
    | some actual =>
      have same : actual = receipt := by simpa [found] using present
      subst actual
      simp

theorem ready_dependency_agreement {previous final program}
    (extension : Extends previous final) (ready : Qirf.ready previous program = true)
    (index : Nat) (referenced : index ∈ Semantics.ObservingFunction.references 65 program.operations) :
    ((Qirf.before previous).map Receipt.dependency)[index]? =
      ((Qirf.before final).map Receipt.dependency)[index]? := by
  obtain ⟨receipt,old,new⟩ := ready_references extension ready index referenced
  exact (before_dependency old).trans (before_dependency new).symm

end QleisliKernel.Qirf.ReceiptTransport
