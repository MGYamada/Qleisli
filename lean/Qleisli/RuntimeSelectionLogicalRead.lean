import Qleisli.RuntimeSelectionArmTrace
import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.ExactMatrix

/-! The source of every exact logical matrix in a coherent selection node.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSelectionLogicalRead
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf QleisliKernel.SourceTypes
open RuntimePureBody
open Semantics.Exact (Matrix)

def FromArms {sources owner name offset selector target dependencies program block}
    (table : QuantumArms.Table sources owner name offset selector target)
    (produced : Fin table.arms.length → Matrix → Prop) :
    Node dependencies program block → Prop
  | .selection (selector := actualSelector) (target := actualTarget) _ _ _ _ _ _ _ labels expected .. =>
    actualSelector.basis = selector ∧ actualTarget.basis = target ∧
      labels = table.layout.labels ∧ Exact.ListRel
      (fun ordinal logical => ∃ index, table.arms[index].label.ordinal = ordinal ∧ produced index logical)
      (List.range table.layout.labels.length) expected
  | _ => False

theorem FromArms.weaken {sources owner name offset selector target dependencies program block}
    {table : QuantumArms.Table sources owner name offset selector target}
    {first second : Fin table.arms.length → Matrix → Prop} {node : Node dependencies program block}
    (read : FromArms table first node)
    (implies : ∀ index matrix, first index matrix → second index matrix) :
    FromArms table second node := by
  cases node with
  | selection _ _ _ _ _ _ _ labels expected _ _ _ _ =>
    have map (ordinals : List Nat) (matrices : List Matrix)
        (related : Exact.ListRel
          (fun ordinal matrix => ∃ index, table.arms[index].label.ordinal = ordinal ∧ first index matrix)
          ordinals matrices) :
        Exact.ListRel
          (fun ordinal matrix => ∃ index, table.arms[index].label.ordinal = ordinal ∧ second index matrix)
          ordinals matrices := by
      induction ordinals generalizing matrices with
      | nil => exact related
      | cons ordinal rest ih =>
        cases matrices with
        | nil => exact related
        | cons matrix remaining =>
          obtain ⟨index,selected,produced⟩ := related.1
          exact ⟨⟨index,selected,implies index matrix produced⟩,ih remaining related.2⟩
    exact ⟨read.1,read.2.1,read.2.2.1,map _ _ read.2.2.2⟩
  | _ => exact read

theorem FromArms.at_ordinal {sources owner name offset selector target dependencies program block}
    {table : QuantumArms.Table sources owner name offset selector target}
    {produced : Fin table.arms.length → Matrix → Prop} {node : Node dependencies program block}
    (read : FromArms table produced node) (ordinal : Fin table.layout.labels.length) :
    match node with
    | .selection _ _ _ _ _ _ _ _ expected .. =>
      ∃ index matrix, table.arms[index].label.ordinal = ordinal.val ∧
        expected[ordinal.val]? = some matrix ∧ produced index matrix
    | _ => False := by
  cases node with
  | selection _ _ _ _ _ _ _ _ expected _ _ _ _ =>
    have related := read.2.2.2
    have inside : ordinal.val < (List.range table.layout.labels.length).length :=
      List.length_range.symm ▸ ordinal.isLt
    have exactRead := Exact.listRel_getElem _ _ _ related ordinal.val inside
    rw [List.getElem_range] at exactRead
    obtain ⟨index,selected,origin⟩ := exactRead
    exact ⟨index,_,selected,List.getElem?_eq_getElem _,origin⟩
  | _ => exact read

abbrev GraphData {artifact : Artifact} (mode : RuntimeBodyQueries.Mode artifact)
    {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (index : Fin table.arms.length) :=
  mode.GraphData (table.arms[index]).operation.graph OperationAccess.controllable (.arm (table.arms[index]).operation)

/-- The planned arm uses the action of the independently consumed evidence
for the original operation at the exact source index. -/
def GraphLogical {artifact : Artifact} {root : Validity.Root} (execution : ExecutionMode artifact root)
    {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (index : Fin table.arms.length) (data : GraphData execution.queries table index)
    (matrix : Matrix) : Prop :=
  match execution,data with
  | .fresh _,_ => True
  | .planned _ continuation,⟨implementations,references,plan⟩ =>
    let operation := (table.arms[index]).operation
    let request : RuntimeGraphOperation.Request artifact :=
      ⟨_,_,operation.graph,OperationAccess.controllable,implementations,references,.arm operation⟩
    ∃ evidence, RuntimeInterval.Computed (continuation.read request plan.evidence) evidence ∧
      matrix = continuation.action evidence

private theorem fold_preserves {Item State : Type}
    (step : State → Item → WorkM State) (invariant : State → Prop) (inputs : List Item)
    (preserve : ∀ current item result work left, item ∈ inputs → invariant current →
      (step current item).run work = (.ok result,left) → invariant result)
    {initial final work left} (beginning : invariant initial)
    (read : (inputs.foldlM step initial).run work = (.ok final,left)) : invariant final := by
  induction inputs generalizing initial work with
  | nil =>
    obtain ⟨rfl,_⟩ := pure_success _ _ _ _ read
    exact beginning
  | cons item rest ih =>
    simp only [List.foldlM_cons] at read
    obtain ⟨next,budget,head,tail⟩ := bind_success _ _ _ _ _ read
    exact ih (fun state entry result incoming outgoing inside =>
      preserve state entry result incoming outgoing (List.mem_cons_of_mem _ inside))
      (preserve _ _ _ _ _ List.mem_cons_self beginning head) tail

private theorem map_relation {Item Value : Type} (step : Item → WorkM Value)
    (related : Item → Value → Prop)
    (sound : ∀ item value work left, (step item).run work = (.ok value,left) → related item value)
    (items : List Item) (values : List Value) (work left : Nat)
    (read : (items.mapM step).run work = (.ok values,left)) : Exact.ListRel related items values := by
  induction items generalizing values work left with
  | nil =>
    obtain ⟨rfl,_⟩ := pure_success _ _ _ _ read
    trivial
  | cons item rest ih =>
    simp only [List.mapM_cons] at read
    obtain ⟨value,middle,first,read⟩ := bind_success _ _ _ _ _ read
    obtain ⟨tail,budget,remaining,read⟩ := bind_success _ _ _ _ _ read
    obtain ⟨rfl,_⟩ := pure_success _ _ _ _ read
    exact ⟨sound item value work middle first,ih tail middle budget remaining⟩

/-- The logical table read by the literal sector checker is assembled from
the original arm callbacks, in semantic selector order. -/
theorem selectionNode_from_arms {α : Type} (artifact : Artifact)
    {dependencies program block start count roles}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (frame : RuntimeOwnerMap.Checked roles interval.before)
    (owners : RuntimeOwnerTransition.Checked interval frame.bindings)
    (selector target : RuntimeOwnerMap.Owner) {owner name offset}
    (table : QuantumArms.Table artifact.sources owner name offset selector.basis target.basis)
    (site : RuntimeContextRequest.Site) (initial : α)
    (realize : Fin table.arms.length →
      QuantumArms.BoundArm artifact.sources owner selector.basis target.basis → α → WorkM (Matrix × α))
    (produced : Fin table.arms.length → Matrix → Prop)
    (preserve : ∀ index before logical after work left,
      (realize index table.arms[index] before).run work = (.ok (logical,after),left) → produced index logical)
    (result : Node dependencies program block × α)
    (checked : RuntimeInterval.Computed
      (selectionNode artifact interval frame owners selector target table site initial realize) result) :
    FromArms table produced result.1 := by
  obtain ⟨work,left,ran⟩ := checked
  unfold selectionNode at ran
  obtain ⟨_,a,_,h⟩ := bind_success _ _ _ _ _ ran
  obtain ⟨entry,b,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨exit,c,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨inputCode,e,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨outputCode,f,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨selectorRead,g,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨targetRead,i,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨walk,j,walked,h⟩ := bind_success _ _ _ _ _ h
  rcases walk with ⟨meanings,remaining⟩
  obtain ⟨expected,k,ordered,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨attached,l,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨restriction,m,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨logical,n,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  obtain ⟨sw,sl,slayout⟩ := selectorRead.property
  have layout := Option.some.inj ((FiniteCarrier.read_reference _ _ _ _ slayout).symm.trans table.selectorLayout)
  let Origin (ordinal : Nat) (logical : Matrix) : Prop :=
    ∃ index, table.arms[index].label.ordinal = ordinal ∧ produced index logical
  let Valid (state : List (Nat × Matrix) × α) : Prop :=
    ∀ entry ∈ state.1, Origin entry.1 entry.2
  have valid : Valid (meanings,remaining) := by
    apply fold_preserves _ Valid _ _ (by simp [Valid]) walked
    intro state item result work left member prior read
    rcases state with ⟨previous,current⟩
    rcases item with ⟨⟨index,arm⟩,subject⟩
    obtain ⟨position,bounded,sameArm⟩ := List.exists_of_mem_mapFinIdx (List.of_mem_zip member).1
    cases sameArm
    obtain ⟨output,p,realized,read⟩ := bind_success _ _ _ _ _ read
    rcases output with ⟨matrix,next⟩
    obtain ⟨actual,q,_,read⟩ := bind_success _ _ _ _ _ read
    obtain ⟨_,r,_,read⟩ := bind_success _ _ _ _ _ read
    obtain ⟨_,s,_,read⟩ := bind_success _ _ _ _ _ read
    obtain ⟨rfl,_⟩ := pure_success _ _ _ _ read
    intro pair present
    rcases List.mem_append.mp present with existing | last
    · exact prior pair existing
    · obtain rfl := List.mem_singleton.mp last
      exact ⟨⟨position,bounded⟩,rfl,preserve _ _ _ _ _ _ realized⟩
  let lookup (ordinal : Nat) : WorkM Matrix := do
    let some (_,matrix) := meanings.find? (·.1 == ordinal) | throw .request
    pure matrix
  have orderedOrigin : Exact.ListRel Origin (List.range selectorRead.val.labels.length) expected := by
    exact map_relation lookup Origin (by
      intro ordinal matrix work left read
      change (lookup ordinal).run work = (.ok matrix,left) at read
      dsimp only [lookup] at read
      cases found : meanings.find? (·.1 == ordinal) with
      | none => simp only [found] at read; cases read
      | some pair =>
        simp only [found] at read
        obtain ⟨rfl,_⟩ := pure_success _ _ _ _ read
        have sameOrdinal : pair.1 = ordinal :=
          beq_iff_eq.mp (List.find?_some (p := fun p : Nat × Matrix => p.1 == ordinal) found)
        exact sameOrdinal ▸ valid pair (List.mem_of_find?_eq_some found))
      (List.range selectorRead.val.labels.length) expected j k ordered
  exact ⟨rfl,rfl,congrArg Semantics.FiniteCarrier.Layout.labels layout, layout ▸ orderedOrigin⟩

/-- The literal comparison reads the value appended by the original arm
handler at the same written index, even when arms were written out of order. -/
theorem selectionNode_from_fold {artifact : Artifact}
    {dependencies program block start count roles State}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (frame : RuntimeOwnerMap.Checked roles interval.before)
    (owners : RuntimeOwnerTransition.Checked interval frame.bindings)
    (selector target : RuntimeOwnerMap.Owner) {owner name offset}
    (table : QuantumArms.Table artifact.sources owner name offset selector.basis target.basis)
    (site : RuntimeContextRequest.Site) (mode : RuntimeBodyQueries.Mode artifact)
    (step : (index : Fin table.arms.length) →
      mode.GraphData (table.arms[index]).operation.graph OperationAccess.controllable
        (.arm (table.arms[index]).operation) → State → WorkM State)
    (project : State → List Matrix)
    (produced : (index : Fin table.arms.length) →
      mode.GraphData (table.arms[index]).operation.graph OperationAccess.controllable
        (.arm (table.arms[index]).operation) → Matrix → Prop)
    (append : ∀ index data initial middle work budget,
      (step index data initial).run work = (.ok middle,budget) →
      ∃ value, project middle = project initial ++ [value] ∧ produced index data value)
    (data : mode.ArmsData table) (initial final : State) (empty : project initial = [])
    (fold : RuntimeInterval.Computed (RuntimeBodyQueries.foldArms mode table step data initial) final)
    (result : Node dependencies program block × Unit)
    (checked : RuntimeInterval.Computed
      (selectionNode artifact interval frame owners selector target table site () fun index _ _ => do
        exactWork (Exact.charge (index.val+1))
        let logical ← lift (readOption (project final)[index.val]?)
        pure (logical,())) result) :
    FromArms table (fun index matrix =>
      ∃ graph before after work left, (step index graph before).run work = (.ok after,left) ∧
        produced index graph matrix) result.1 := by
  obtain ⟨work,left,ran⟩ := fold
  obtain ⟨values,collected,count,each⟩ := RuntimeSelectionArmTrace.ordinal_read
    mode table step project produced append data initial final work left ran
  have stored : project final = values := by
    simpa only [empty,List.nil_append] using collected
  subst values
  apply selectionNode_from_arms artifact interval frame owners selector target table site () _ _ _ result checked
  intro index before matrix after work left read
  obtain ⟨_,budget,_,read⟩ := bind_success _ _ _ _ _ read
  obtain ⟨value,remaining,looked,read⟩ := bind_success _ _ _ _ _ read
  have same := congrArg Prod.fst (pure_success _ _ _ _ read).1
  dsimp only at same
  subst value
  have lookup := (lift_success _ _ _ _ looked).1
  have actual : (project final)[index.val]? = some matrix := by
    cases option : (project final)[index.val]? with
    | none =>
      rw [option] at lookup
      cases lookup
    | some stored =>
      rw [option] at lookup
      have equal : stored = matrix := Except.ok.inj lookup
      rw [equal]
  have member : table.arms[index].label.ordinal ∈ table.arms.map (·.label.ordinal) :=
    List.mem_map.mpr ⟨table.arms[index],List.getElem_mem index.isLt,rfl⟩
  have bounded := List.mem_range.mp ((RuntimeSelectionArmTrace.ordinal_permutation table).mem_iff.mp member)
  obtain ⟨written,graph,incoming,outgoing,first,last,ordinal,ran,producedAt⟩ := each ⟨_,bounded⟩
  obtain ⟨original,_,unique⟩ := RuntimeSelectionArmTrace.arm_at_ordinal table _ bounded
  have sameIndex : written = index := (unique written ordinal).trans (unique index rfl).symm
  subst written
  have bound : index.val < (project final).length := count.symm ▸ index.isLt
  have sameMatrix := Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans actual)
  exact ⟨graph,incoming,outgoing,first,last,ran,sameMatrix ▸ producedAt⟩

#print axioms selectionNode_from_arms
#print axioms selectionNode_from_fold
#print axioms FromArms.at_ordinal
end Qleisli.RuntimeSelectionLogicalRead
