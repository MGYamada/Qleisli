import Qleisli.RawInstrument
import Qleisli.RawDenotation
import Qleisli.RawProtectedEvaluation
import Qleisli.Semantics.RawInstrument

/-! Every actual observing evaluator step refines the independent original
instrument judgment, including all hidden histories and simultaneous phis.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.Instrument.Denotation
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Observation QleisliKernel.Raw.Instrument QleisliKernel.Finite
open Qleisli.Semantics.Exact
open Qleisli.Semantics.RawInstrument (ErasureMeaning Erased Action Run Actions ProgramMeaning)

def reference (history : History) : Qleisli.Semantics.RawInstrument.History :=
  ⟨history.values,history.hidden,history.operator⟩

private theorem map_relation {A B C D : Type} (step : A → WorkM B)
    (f : A → C) (g : B → D) (relation : C → D → Prop)
    (sound : ∀ a b work left, (step a).run work = (.ok b,left) → relation (f a) (g b))
    (xs : List A) (ys : List B) (work left : Nat)
    (ok : (xs.mapM step).run work = (.ok ys,left)) :
    List.Forall₂ relation (xs.map f) (ys.map g) := by
  induction xs generalizing ys work left with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst ys
    exact .nil
  | cons a xs ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨b,middle,hb,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨rest,after,hr,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst ys
    exact .cons (sound a b work middle hb) (ih rest middle after hr)

private theorem map_option {A B : Type} (step : A → WorkM B) (literal : A → Option B)
    (sound : ∀ a b work left, (step a).run work = (.ok b,left) → literal a = some b)
    (xs : List A) (ys : List B) (work left : Nat)
    (ok : (xs.mapM step).run work = (.ok ys,left)) : xs.mapM literal = some ys := by
  induction xs generalizing ys work left with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst ys
    rfl
  | cons a xs ih =>
    simp only [List.mapM_cons] at ok ⊢
    obtain ⟨b,middle,hb,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨rest,after,hr,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst ys
    simp [sound a b work middle hb,ih rest middle after hr]

theorem lookup_reference (values : Values) (id : Nat) (result : Bool) (work left : Nat)
    (ok : (lookup values id).run work = (.ok result,left)) :
    Qleisli.Semantics.RawInstrument.value values id = some result := by
  have found := (lift_success _ _ _ _ ok).1
  change readOption (Qleisli.Semantics.RawInstrument.value values id) = .ok result at found
  cases h : Qleisli.Semantics.RawInstrument.value values id with
  | none => rw [h] at found; cases found
  | some value =>
    rw [h] at found
    have same : value = result := Except.ok.inj found
    simp only [same]

theorem expression_reference (values : Values) (expr : Expr) (result : Bool) (work left : Nat)
    (ok : (expression values expr).run work = (.ok result,left)) :
    Qleisli.Semantics.RawInstrument.expression values expr = some result := by
  cases expr with
  | constant v =>
    have same := (pure_success _ _ _ _ ok).1
    subst result
    rfl
  | not input =>
    obtain ⟨a,middle,ha,h⟩ := bind_success _ _ _ _ _ ok
    have same := (pure_success _ _ _ _ h).1
    subst result
    simp [Qleisli.Semantics.RawInstrument.expression,lookup_reference _ _ _ _ _ ha]
  | xor a b | and a b =>
    obtain ⟨x,middle,hx,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨y,after,hy,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst result
    simp [Qleisli.Semantics.RawInstrument.expression,lookup_reference _ _ _ _ _ hx,lookup_reference _ _ _ _ _ hy]

theorem merge_reference (choice : Bool) (phis : List ClassicalPhi) (initial final : History)
    (work left : Nat) (ok : (mergeClassical choice phis initial).run work = (.ok final,left)) :
    Qleisli.Semantics.RawInstrument.merged choice phis (reference initial) = some (reference final) := by
  obtain ⟨values,middle,hv,h⟩ := bind_success _ _ _ _ _ ok
  have same := (pure_success _ _ _ _ h).1
  subst final
  have read := map_option _ (fun phi => do
    pure (phi.output,← Qleisli.Semantics.RawInstrument.value initial.values
      (if choice then phi.thenId else phi.elseId))) ?_ phis values work middle hv
  · unfold Qleisli.Semantics.RawInstrument.merged
    dsimp only [reference]
    rw [read]
    rfl
  · intro phi value work left success
    obtain ⟨v,middle,hv,h⟩ := bind_success _ _ _ _ _ success
    have same := (pure_success _ _ _ _ h).1
    subst value
    simp [lookup_reference _ _ _ _ _ hv]

theorem erase_reference (bits : Nat) (axes : List Nat) (outcome : Nat) (map : Matrix)
    (work left : Nat) (ok : (erase bits axes outcome).run work = (.ok map,left)) :
    ErasureMeaning bits axes outcome map := by
  have same := erase_value _ _ _ _ _ _ ok
  subst map
  dsimp only [ErasureMeaning]
  refine ⟨rfl,rfl,?_⟩
  intro row col hr hc
  let kept := (List.range bits).filter (fun axis => !axes.contains axis)
  have meaning : (((List.range (2^kept.length*2^bits)).map fun index =>
      if gather (index % 2^bits) axes == outcome && gather (index % 2^bits) kept == index / 2^bits
      then Scalar.one else Scalar.zero).map scalar) =
      (List.range (2^kept.length*2^bits)).map (fun index =>
        if gather (index % 2^bits) axes = outcome ∧ gather (index % 2^bits) kept = index / 2^bits
        then (1 : ℂ) else 0) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro index _
    simp only [Function.comp_apply,Bool.and_eq_true,beq_iff_eq]
    by_cases h : gather (index % 2^bits) axes = outcome ∧ gather (index % 2^bits) kept = index / 2^bits
    · simp only [h,and_self,if_true,Exact.scalar_one_meaning]
    · simp only [h,if_false,Exact.scalar_zero_meaning]
  have entryEq := Exact.matrix_entry_of_meanings _ _ _ _ row col hr hc meaning
  have positive : 0 < 2^bits := by positivity
  have divided : (row*2^bits+col) / 2^bits = row := by
    rw [Nat.add_comm,Nat.add_mul_div_right col row positive,Nat.div_eq_of_lt hc,Nat.zero_add]
  simpa only [divided,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hc] using entryEq

theorem apply_reference (initial final : History) (map : Matrix) (work left : Nat)
    (ok : (apply initial map).run work = (.ok final,left)) :
    final.values = initial.values ∧ final.hidden = initial.hidden ∧
    Qleisli.Semantics.Raw.Composition map initial.operator final.operator := by
  obtain ⟨actual,middle,hc,h⟩ := bind_success _ _ _ _ _ ok
  have same := (pure_success _ _ _ _ h).1
  subst final
  exact ⟨rfl,rfl,Exact.compose_meaning _ _ _ _ _ (exactWork_success _ _ _ _ hc)⟩

theorem step_reference (dependencies : List Dependency)
    (recurse : List Event → History → WorkM (List History))
    (sound : ∀ events initial final work left,
      (recurse events initial).run work = (.ok final,left) →
      Run dependencies events [reference initial] (final.map reference))
    (event : Event) (initial : History) (final : List History) (work left : Nat)
    (ok : (stepEvent dependencies recurse event initial).run work = (.ok final,left)) :
    Action dependencies event (reference initial) (final.map reference) := by
  obtain ⟨_,middle,_,h⟩ := bind_success _ _ _ _ _ ok
  cases event with
  | pure event =>
    obtain ⟨map,after,hm,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨next,last,hn,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst final
    have applied := apply_reference _ _ _ _ _ hn
    have data : reference next = {reference initial with operator := next.operator} := by
      simp [reference,applied.1,applied.2.1]
    rw [List.map_singleton,data]
    exact .pure _ _ _ _ (Qleisli.Raw.ProtectedEvaluation.event_denotes _ _ _ _ _ hm) applied.2.2
  | erase bits axes output =>
    obtain ⟨_,after,_,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,last,_,h⟩ := bind_success _ _ _ _ _ h
    apply Action.erase
    have localSound : ∀ (outcome : Nat) (next : History) (work left : Nat),
        (do
          let map ← erase bits axes outcome
          let actual ← apply initial map
          let values := recordValue initial.values output outcome
          pure {actual with values,hidden := initial.hidden ++ [outcome]} : WorkM History).run work = (.ok next,left) →
        Erased bits axes output (reference initial) outcome (reference next) := by
      intro outcome next work left accepted
      obtain ⟨map,w₁,hm,h⟩ := bind_success _ _ _ _ _ accepted
      obtain ⟨actual,w₂,ha,h⟩ := bind_success _ _ _ _ _ h
      have same := (pure_success _ _ _ _ h).1
      subst next
      have applied := apply_reference _ _ _ _ _ ha
      exact ⟨rfl,rfl,map,erase_reference _ _ _ _ _ _ hm,applied.2.2⟩
    simpa only [List.map_id] using map_relation _ id reference
      (Erased bits axes output (reference initial)) localSound _ _ _ _ h
  | classical expr output =>
    obtain ⟨value,after,hv,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst final
    exact .classical _ _ _ _ (expression_reference _ _ _ _ _ hv)
  | branch condition thenEvents elseEvents phis =>
    obtain ⟨choice,after,hc,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨next,last,hn,h⟩ := bind_success _ _ _ _ _ h
    exact .branch _ _ _ _ _ _ _ _ (lookup_reference _ _ _ _ _ hc)
      (sound _ _ _ _ _ hn) (map_relation _ reference reference _
        (fun a b work left success => merge_reference _ _ _ _ _ _ success) _ _ _ _ h)

private theorem fold_reference (dependencies : List Dependency)
    (recurse : List Event → History → WorkM (List History))
    (sound : ∀ events initial final work left,
      (recurse events initial).run work = (.ok final,left) →
      Run dependencies events [reference initial] (final.map reference))
    (events : List Event) (initial final : List History) (work left : Nat)
    (ok : (events.foldlM (fun (histories : List History) event => do
      let next ← histories.mapM (stepEvent dependencies recurse event)
      return next.flatten) initial).run work = (.ok final,left)) :
    Run dependencies events (initial.map reference) (final.map reference) := by
  induction events generalizing initial work with
  | nil =>
    have same := (pure_success _ _ _ _ ok).1
    subst final
    exact .nil _
  | cons event events ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,hn,h⟩ := bind_success _ _ _ _ _ ok
    obtain ⟨groups,after,hg,last⟩ := bind_success _ _ _ _ _ hn
    have same := (pure_success _ _ _ _ last).1
    subst next
    have actions := map_relation _ reference (List.map reference) _
      (fun a b work left success => step_reference dependencies recurse sound event a b work left success)
      _ _ _ _ hg
    have rest := ih _ middle h
    rw [List.map_flatten] at rest
    exact .cons _ _ _ _ _ (Actions.of_forall₂ _ _ _ _ actions) rest

theorem run_reference (dependencies : List Dependency) (fuel : Nat)
    (events : List Event) (initial : History) (final : List History) (work left : Nat)
    (ok : (runEvents dependencies fuel events initial).run work = (.ok final,left)) :
    Run dependencies events [reference initial] (final.map reference) := by
  induction fuel generalizing events initial final work left with
  | zero => cases ok
  | succ fuel ih => exact fold_reference _ _ (fun _ _ _ _ _ h => ih _ _ _ _ _ h) _ _ _ _ _ ok

theorem inspect_denotes (inputs : List QleisliKernel.Semantics.Function.Input)
    (bindings : List QleisliKernel.Semantics.Function.Binding) (program : Program)
    (classical : List Bool) (checked : Checked) (work left : Nat)
    (ok : (inspect inputs bindings program classical).run work = (.ok checked,left)) :
    ∃ receipts a b,
      (QleisliKernel.Raw.Function.checkAll inputs bindings).run a = (.ok receipts,b) ∧
      ProgramMeaning (receipts.map QleisliKernel.Semantics.Function.Receipt.dependency)
        program classical (checked.histories.map reference) := by
  rcases inspect_execution _ _ _ _ _ _ _ ok with
    ⟨receipts,initial,a,b,c,d,e,f,hf,hv,hi,he,_⟩
  have original := (QleisliKernel.Raw.Observation.verify_conditions _ _ _ _ _ hv).2.2
  have identity := Exact.identity_meaning _ _ hi
  refine ⟨receipts,a,b,hf,checked.structureCheck.prepared,initial,original,?_,run_reference _ _ _ _ _ _ _ he⟩
  exact ⟨identity.2.1,identity.2.2.1,fun row col hr hc => identity.2.2.2 row col
    (identity.2.1 ▸ hr) (identity.2.2.1 ▸ hc)⟩

end Qleisli.Raw.Instrument.Denotation
