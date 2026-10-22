import QleisliKernel.SourceTypes.NaturalPredicates
import QleisliKernel.Semantics.SourceNatural

/-! Symbolic existing Nat normalization with exact original-expression meaning.
Names/calls must be supplied by bound original readers; these parameters do not
give a producer lookup/template authority or grant source execution by themselves.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalNormalize
open Semantics.SourceNatural Semantics.SourceAffine NaturalAffine NaturalPredicates

structure Result (names : Valuation → Names) (calls : Calls) (meaning : Valuation → Prop)
    (fuel : Nat) (expression : Expr) where
  form : Form
  correct : ∀ values,meaning values → ∃ n,
    evaluate fuel (names values) calls expression = some n ∧ form.evaluate values = (n : Int)

theorem Result.value {names calls meaning fuel expression}
    (result : Result names calls meaning fuel expression) (values : Valuation)
    (held : meaning values) : ∃ n,Value (names values) calls expression n ∧
      result.form.evaluate values = (n : Int) := by
  obtain ⟨n,computed,same⟩ := result.correct values held
  exact ⟨n,evaluate_value _ _ _ _ _ computed,same⟩

structure Arguments (names : Valuation → Names) (calls : Calls) (meaning : Valuation → Prop)
    (fuel : Nat) (arguments : List Expr) where
  forms : List Form
  correct : ∀ values,meaning values → ∃ numbers,
    Related (fun e n => evaluate fuel (names values) calls e = some n) arguments numbers ∧
    Related (fun (form : Form) (n : Nat) => form.evaluate values = (n : Int)) forms numbers

structure Readers (names : Valuation → Names) (calls : Calls) (meaning : Valuation → Prop) where
  name : ∀ fuel path, WorkM (Result names calls meaning (fuel+1) (.name path))
  call : ∀ fuel path arguments, Arguments names calls meaning fuel arguments →
    WorkM (Result names calls meaning (fuel+1) (.call path arguments))

private def readArguments {names calls meaning fuel}
    (read : ∀ expression,WorkM (Result names calls meaning fuel expression)) :
    Nat → (arguments : List Expr) → WorkM (Arguments names calls meaning fuel arguments) :=
  Nat.rec (fun arguments => match arguments with
      | [] => pure ⟨[],fun _ _ => ⟨[],.nil,.nil⟩⟩
      | _ :: _ => throw .limit)
    (fun _ recurse arguments => do
      Finite.exactWork (Exact.charge 1)
      match arguments with
      | [] => return ⟨[],fun _ _ => ⟨[],.nil,.nil⟩⟩
      | first :: rest =>
        let head ← read first
        let tail ← recurse rest
        return ⟨head.form :: tail.forms,by
          intro values held
          obtain ⟨n,computed,same⟩ := head.correct values held
          obtain ⟨numbers,computedTail,sameTail⟩ := tail.correct values held
          exact ⟨n :: numbers,.cons computed computedTail,.cons same sameTail⟩⟩)

private def step {names calls meaning} (fuel variables : Nat) (context : Context meaning)
    (readers : Readers names calls meaning)
    (recurse : ∀ expression,WorkM (Result names calls meaning fuel expression))
    (expression : Expr) : WorkM (Result names calls meaning (fuel+1) expression) := do
  Finite.exactWork (Exact.charge 1)
  match expression with
  | .number n =>
    let result ← witness (constant variables n)
    return ⟨result.val,by
      intro values _held
      refine ⟨n,rfl,?_⟩
      obtain ⟨work,left,ok⟩ := result.property
      exact constant_meaning _ _ _ _ _ ok values⟩
  | .name path => readers.name fuel path
  | .call path arguments => do
    Finite.exactWork (Exact.charge (arguments.length+1))
    let args ← readArguments recurse (arguments.length+1) arguments
    readers.call fuel path arguments args
  | .add a b =>
    let first ← recurse a
    let second ← recurse b
    let result ← witness (add first.form second.form)
    return ⟨result.val,by
      intro values held
      obtain ⟨x,hx,px⟩ := first.correct values held
      obtain ⟨y,hy,py⟩ := second.correct values held
      refine ⟨x+y,?_,?_⟩
      · change (do return (← evaluate fuel (names values) calls a) +
          (← evaluate fuel (names values) calls b)) = some (x+y)
        simp only [hx,hy,Option.pure_def] <;> rfl
      · obtain ⟨work,left,ok⟩ := result.property
        rw [add_meaning _ _ _ _ _ ok,px,py]
        rfl⟩
  | .sub a b =>
    let first ← recurse a
    let second ← recurse b
    let nonnegative ← provesLe context second.form first.form
    let result ← witness (sub first.form second.form)
    return ⟨result.val,by
      intro values held
      obtain ⟨x,hx,px⟩ := first.correct values held
      obtain ⟨y,hy,py⟩ := second.correct values held
      have le : y ≤ x := by
        have bounded := nonnegative.proof values held
        rw [px,py] at bounded
        omega
      refine ⟨x-y,?_,?_⟩
      · change (do
          let x ← evaluate fuel (names values) calls a
          let y ← evaluate fuel (names values) calls b
          if y ≤ x then some (x-y) else none) = some (x-y)
        simp only [hx,hy]
        change (if y ≤ x then some (x-y) else none) = some (x-y)
        rw [if_pos le]
      · obtain ⟨work,left,ok⟩ := result.property
        rw [sub_meaning _ _ _ _ _ ok,px,py]
        omega⟩
  | .mul a b =>
    let first ← recurse a
    let second ← recurse b
    let result ← witness (multiply first.form second.form)
    return ⟨result.val,by
      intro values held
      obtain ⟨x,hx,px⟩ := first.correct values held
      obtain ⟨y,hy,py⟩ := second.correct values held
      refine ⟨x*y,?_,?_⟩
      · change (do return (← evaluate fuel (names values) calls a) *
          (← evaluate fuel (names values) calls b)) = some (x*y)
        simp only [hx,hy,Option.pure_def] <;> rfl
      · obtain ⟨work,left,ok⟩ := result.property
        rw [multiply_meaning _ _ _ _ _ ok,px,py]
        rfl⟩

/-- Every successful arithmetic step is tied to the independent evaluator and
Value relation. Generic original-reader obligations are deliberately explicit. -/
def normalize {names calls meaning} (variables : Nat) (context : Context meaning)
    (readers : Readers names calls meaning) :
    (fuel : Nat) → (expression : Expr) → WorkM (Result names calls meaning fuel expression) :=
  Nat.rec (fun _ => throw .limit) (fun fuel recurse => step fuel variables context readers recurse)

end QleisliKernel.SourceTypes.NaturalNormalize
