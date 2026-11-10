import Qleisli.RawEventLinear
import Qleisli.RuntimeNamedThreePackedInstrument
import Mathlib.Data.List.Forall2

/-! The original literal interpreter preserves weighted operator columns.
Every component runs the same ordinary choices and retains the same ordered
outcomes, including outcomes with a zero operator.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.ObservingAction
open QleisliKernel.Semantics.Observation (Event ClassicalPhi)
open QleisliKernel.Semantics.Finite (Dependency)
open Qleisli.Semantics.RawAction (combination event_combination erase_combination)
open Qleisli.RuntimeNamedThreePackedInstrument (advance)

structure WeightedHistory {Index : Type} (indices : List Index) (weight : Nat → Index → ℂ)
    (whole : History) (parts : Index → History) : Prop where
  values : ∀ index, (parts index).values = whole.values
  hidden : ∀ index, (parts index).hidden = whole.hidden
  operator : ∀ row col, whole.operator row col =
    combination indices (weight col) (fun index => (parts index).operator row col)

def WeightedResults {Index : Type} (indices : List Index) (weight : Nat → Index → ℂ)
    (whole : List History) (parts : Index → Option (List History)) : Prop :=
  ∃ family : List (Index → History),
    (∀ index, parts index = some (family.map (fun result => result index))) ∧
    List.Forall₂ (WeightedHistory indices weight) whole family

private theorem merge_weighted {Index : Type} {indices : List Index} {weight : Nat → Index → ℂ}
    (choice : Bool) (phis : List ClassicalPhi)
    {whole : History} {parts : Index → History} (agrees : WeightedHistory indices weight whole parts)
    {joined : History} (executed : merge choice phis whole = some joined) :
    ∃ family : Index → History, (∀ index, merge choice phis (parts index) = some (family index)) ∧
      WeightedHistory indices weight joined family := by
  let bindings := fun (values : List (Nat × Bool)) =>
    phis.mapM fun phi => do
      return (phi.output,← RawInstrument.value values (if choice then phi.thenId else phi.elseId))
  change (bindings whole.values >>= fun values => some {whole with values := whole.values++values}) = _ at executed
  obtain ⟨added,read,returned⟩ := Option.bind_eq_some_iff.mp executed
  cases Option.some.inj returned
  refine ⟨fun index => {parts index with values := (parts index).values++added},?_,?_⟩
  · intro index
    change (bindings (parts index).values >>= fun values =>
      some {parts index with values := (parts index).values++values}) = _
    rw [agrees.values index,read]
    simp only [bind,Option.bind,agrees.values index]
  · exact ⟨fun index => congrArg (· ++ added) (agrees.values index),agrees.hidden,agrees.operator⟩

private theorem merge_results_weighted {Index : Type} {indices : List Index} {weight : Nat → Index → ℂ}
    (choice : Bool) (phis : List ClassicalPhi) {whole : List History} {parts : List (Index → History)}
    (agrees : List.Forall₂ (WeightedHistory indices weight) whole parts)
    {joined : List History} (executed : whole.mapM (merge choice phis) = some joined) :
    WeightedResults indices weight joined (fun index => (parts.map (fun h => h index)).mapM (merge choice phis)) := by
  induction agrees generalizing joined with
  | nil =>
    cases Option.some.inj executed
    exact ⟨[],fun _ => rfl,.nil⟩
  | @cons wholeHead partHead wholeTail partTail agrees _ ih =>
    rw [List.mapM_cons] at executed
    obtain ⟨head,headRun,rest⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨tail,tailRun,done_⟩ := Option.bind_eq_some_iff.mp rest
    cases Option.some.inj done_
    obtain ⟨first,eachHead,headPaired⟩ := merge_weighted choice phis agrees headRun
    obtain ⟨later,eachTail,tailPaired⟩ := ih tailRun
    refine ⟨first::later,?_,.cons headPaired tailPaired⟩
    intro index
    simp only [List.map_cons,List.mapM_cons,eachHead index,eachTail index,bind,Option.bind,pure]

private theorem step_weighted {Index : Type} {indices : List Index} {weight : Nat → Index → ℂ}
    (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (child : ∀ (events : List Event) (whole : History) (parts : Index → History),
      WeightedHistory indices weight whole parts → ∀ {results}, recurse events whole = some results →
      WeightedResults indices weight results (fun index => recurse events (parts index)))
    (event : Event) {whole : History} {parts : Index → History}
    (agrees : WeightedHistory indices weight whole parts)
    {results : List History} (executed : step dependencies recurse event whole = some results) :
    WeightedResults indices weight results (fun index => step dependencies recurse event (parts index)) := by
  cases event with
  | pure operation =>
    let applied : History → History := fun history =>
      {history with operator := fun row col =>
        RawAction.event dependencies operation (fun input => history.operator input col) row}
    have same : [applied whole] = results := Option.some.inj executed
    subst results
    refine ⟨[fun index => applied (parts index)],fun _ => rfl,.cons ⟨agrees.values,agrees.hidden,?_⟩ .nil⟩
    intro row col
    change RawAction.event dependencies operation (fun input => whole.operator input col) row = _
    have input : (fun input => whole.operator input col) =
        fun input => combination indices (weight col) (fun index => (parts index).operator input col) :=
      funext fun input => agrees.operator input col
    rw [input]
    exact event_combination dependencies operation indices (weight col) _ row
  | erase bits axes output =>
    let result (history : History) (outcome : Nat) : History :=
      { values := output.elim history.values (fun id => history.values ++ [(id,outcome == 1)])
        hidden := history.hidden ++ [outcome]
        operator := fun row col => erase bits axes outcome (fun input => history.operator input col) row }
    let outcomes := List.range (2^axes.length)
    have same : outcomes.map (result whole) = results := by
      cases output <;> exact Option.some.inj executed
    rw [← same]
    refine ⟨outcomes.map (fun outcome index => result (parts index) outcome),?_,?_⟩
    · intro index
      have literal : step dependencies recurse (.erase bits axes output) (parts index) =
          some (outcomes.map (result (parts index))) := by
        cases output <;> rfl
      simpa only [List.map_map,Function.comp_def] using literal
    · rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
      apply List.forall₂_same.2
      intro outcome _
      refine ⟨?_,fun index => congrArg (· ++ [outcome]) (agrees.hidden index),?_⟩
      · intro index
        cases output <;> simp only [result,agrees.values index]
      · intro row col
        change erase bits axes outcome (fun input => whole.operator input col) row = _
        have input : (fun input => whole.operator input col) =
            fun input => combination indices (weight col) (fun index => (parts index).operator input col) :=
          funext fun input => agrees.operator input col
        rw [input]
        exact erase_combination bits axes outcome indices (weight col) _ row
  | classical expression output =>
    cases evaluated : RawInstrument.expression whole.values expression with
    | none => simp [step,evaluated] at executed
    | some value =>
      let result := fun (history : History) => {history with values := history.values++[(output,value)]}
      have same : [result whole] = results := by
        simpa [step,evaluated,result] using executed
      subst results
      refine ⟨[fun index => result (parts index)],?_,
        .cons ⟨fun index => congrArg (· ++ [(output,value)]) (agrees.values index),agrees.hidden,agrees.operator⟩ .nil⟩
      intro index
      simp [step,agrees.values index,evaluated,result]
  | branch condition left right phis =>
    cases selected : RawInstrument.value whole.values condition with
    | none => simp [step,selected] at executed
    | some choice =>
      let events := if choice then left else right
      have continued : (recurse events whole >>= fun branch => branch.mapM (merge choice phis)) = some results := by
        simpa only [step,selected,bind,Option.bind,events] using executed
      obtain ⟨before,ran,merged⟩ := Option.bind_eq_some_iff.mp continued
      obtain ⟨family,partsRun,paired⟩ := child events whole parts agrees ran
      obtain ⟨joined,partsMerged,related⟩ := merge_results_weighted choice phis paired merged
      refine ⟨joined,?_,related⟩
      intro index
      simpa only [step,agrees.values index,selected,events,partsRun index,bind,Option.bind] using partsMerged index

private theorem advance_weighted {Index : Type} {indices : List Index} {weight : Nat → Index → ℂ}
    (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (event : Event)
    (localLaw : ∀ {whole : History} {parts : Index → History}, WeightedHistory indices weight whole parts →
      ∀ {results}, step dependencies recurse event whole = some results →
      WeightedResults indices weight results (fun index => step dependencies recurse event (parts index)))
    {whole : List History} {parts : List (Index → History)}
    (agrees : List.Forall₂ (WeightedHistory indices weight) whole parts)
    {results : List History} (executed : advance dependencies recurse whole event = some results) :
    WeightedResults indices weight results (fun index =>
      advance dependencies recurse (parts.map (fun history => history index)) event) := by
  induction agrees generalizing results with
  | nil =>
    cases Option.some.inj executed
    exact ⟨[],fun _ => rfl,.nil⟩
  | @cons wholeHead partHead wholeTail partTail agrees _ ih =>
    change (do
      let groups ← (wholeHead::wholeTail).mapM (step dependencies recurse event)
      return groups.flatten) = _ at executed
    simp only [List.mapM_cons,bind_assoc,pure_bind] at executed
    obtain ⟨head,headRun,rest⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨tailGroups,tailRun,done_⟩ := Option.bind_eq_some_iff.mp rest
    have final : head ++ tailGroups.flatten = results := Option.some.inj done_
    subst results
    obtain ⟨first,eachHead,headPaired⟩ := localLaw agrees headRun
    have tailAdvanced : advance dependencies recurse wholeTail event = some tailGroups.flatten := by
      simp only [advance,tailRun,bind,Option.bind,pure]
    obtain ⟨later,eachTail,tailPaired⟩ := ih tailAdvanced
    refine ⟨first++later,?_,List.rel_append headPaired tailPaired⟩
    intro index
    have tailPart := eachTail index
    unfold advance at tailPart ⊢
    simp only [List.map_cons,List.mapM_cons,eachHead index,bind,Option.bind,pure,
      List.map_append]
    cases read : (partTail.map (fun history => history index)).mapM (step dependencies recurse event) with
    | none => simp [read] at tailPart
    | some groups =>
      simp only [read,bind,Option.bind,pure,Option.some.injEq] at tailPart
      change some ((first.map (fun history => history index)) ++ groups.flatten) = _
      rw [tailPart]

private theorem fold_weighted {Index : Type} {indices : List Index} {weight : Nat → Index → ℂ}
    (dependencies : List Dependency) (recurse : List Event → History → Option (List History))
    (child : ∀ (events : List Event) (whole : History) (parts : Index → History),
      WeightedHistory indices weight whole parts → ∀ {results}, recurse events whole = some results →
      WeightedResults indices weight results (fun index => recurse events (parts index)))
    (events : List Event) {whole : List History} {parts : List (Index → History)}
    (agrees : List.Forall₂ (WeightedHistory indices weight) whole parts)
    {results : List History} (executed : events.foldlM (advance dependencies recurse) whole = some results) :
    WeightedResults indices weight results (fun index =>
      events.foldlM (advance dependencies recurse) (parts.map (fun history => history index))) := by
  induction events generalizing whole parts with
  | nil =>
    cases Option.some.inj executed
    exact ⟨parts,fun _ => rfl,agrees⟩
  | cons event rest ih =>
    rw [List.foldlM_cons] at executed
    obtain ⟨middle,stepRead,tailRead⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨family,eachStep,stepPaired⟩ := advance_weighted dependencies recurse event
      (fun {_ _} pair {_} ran => step_weighted dependencies recurse child event pair ran) agrees stepRead
    obtain ⟨final,eachTail,finalPaired⟩ := ih stepPaired tailRead
    refine ⟨final,?_,finalPaired⟩
    intro index
    simpa only [List.foldlM_cons,eachStep index,bind,Option.bind] using eachTail index

/-- A successful literal execution distributes over finite weighted inputs
column by column, with the same complete result list in every component. -/
theorem run_weighted {Index : Type} (indices : List Index) (weight : Nat → Index → ℂ)
    (dependencies : List Dependency) (fuel : Nat) (events : List Event)
    (whole : History) (parts : Index → History) (agrees : WeightedHistory indices weight whole parts)
    {results : List History} (executed : run dependencies fuel events whole = some results) :
    WeightedResults indices weight results (fun index => run dependencies fuel events (parts index)) := by
  induction fuel generalizing events whole parts results with
  | zero => cases executed
  | succ fuel ih =>
    exact fold_weighted dependencies (run dependencies fuel) (fun events whole parts agrees {_} ran =>
      ih events whole parts agrees ran) events (.cons agrees .nil) executed

#print axioms run_weighted
end Qleisli.Semantics.ObservingAction
