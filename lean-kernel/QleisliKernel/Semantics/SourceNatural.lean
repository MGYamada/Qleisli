import QleisliKernel.Semantics.SourceAffine

/-! Exact natural-expression meanings, independent of source parsing and checking.
Lookup/call interpretations are explicit parameters; this definition grants no
helper, source-preservation or accepted-handle authority by itself.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.SourceNatural

abbrev Path := List String

-- Recursive equality/printing derivation introduces partial generated helpers.
-- Keep the data plain and use total folds/recursors for executable operations.
inductive Expr where
  | number (value : Nat)
  | name (path : Path)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | call (path : Path) (arguments : List Expr)

abbrev Names := Path → Option Nat
abbrev Calls := Path → List Nat → Option Nat

/-- Pointwise correspondence of complete ordered lists, including their shape. -/
inductive Related {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Related relation [] []
  | cons {a b as bs} : relation a b → Related relation as bs → Related relation (a::as) (b::bs)

theorem Related.length_eq {α β : Type} {relation : α → β → Prop} {a : List α} {b : List β}
    (related : Related relation a b) : a.length = b.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons,Nat.add_right_cancel_iff] using ih

mutual
  /-- Exact arithmetic: subtraction requires its nonnegative premise. A call
  uses the stated interpretation, whose original helper binding is separate. -/
  inductive Value (names : Names) (calls : Calls) : Expr → Nat → Prop where
    | number (n) : Value names calls (.number n) n
    | name (path n) (found : names path = some n) : Value names calls (.name path) n
    | add (a b x y) (left : Value names calls a x) (right : Value names calls b y) :
        Value names calls (.add a b) (x+y)
    | sub (a b x y) (left : Value names calls a x) (right : Value names calls b y)
        (nonnegative : y ≤ x) : Value names calls (.sub a b) (x-y)
    | mul (a b x y) (left : Value names calls a x) (right : Value names calls b y) :
        Value names calls (.mul a b) (x*y)
    | call (path arguments values n) (args : Values names calls arguments values)
        (found : calls path values = some n) : Value names calls (.call path arguments) n

  inductive Values (names : Names) (calls : Calls) : List Expr → List Nat → Prop where
    | nil : Values names calls [] []
    | cons (a rest x xs) (head : Value names calls a x) (tail : Values names calls rest xs) :
        Values names calls (a::rest) (x::xs)
end

private def mapValues (read : Expr → Option Nat) (arguments : List Expr) : Option (List Nat) :=
  arguments.foldr (fun first remaining => do
    let value ← read first
    let values ← remaining
    return value :: values) (some [])

private theorem mapValues_cons (read : Expr → Option Nat) (first : Expr) (rest : List Expr) :
    mapValues read (first::rest) = (do
      let value ← read first
      let values ← mapValues read rest
      return value :: values) := rfl

private def evaluateStep (recurse : Names → Calls → Expr → Option Nat)
    (names : Names) (calls : Calls) (expression : Expr) : Option Nat :=
  match expression with
  | .number n => some n
  | .name path => names path
  | .add a b => do return (← recurse names calls a) + (← recurse names calls b)
  | .sub a b => do
    let x ← recurse names calls a
    let y ← recurse names calls b
    if y ≤ x then some (x-y) else none
  | .mul a b => do return (← recurse names calls a) * (← recurse names calls b)
  | .call path arguments => do calls path (← mapValues (recurse names calls) arguments)

/-- A bounded computation of the independent mathematical relation. No fixed
machine-integer bound is imposed by the meaning; checking imposes its own limits.
The callback interpretation must still be bound to actual checked helpers. -/
def evaluate : Nat → Names → Calls → Expr → Option Nat :=
  Nat.rec (fun _ _ _ => none) (fun _ recurse => evaluateStep recurse)

private theorem evaluate_succ (fuel : Nat) (names : Names) (calls : Calls) (e : Expr) :
    evaluate (fuel+1) names calls e = evaluateStep (evaluate fuel) names calls e := rfl

private theorem mapValues_sound (names : Names) (calls : Calls) (read : Expr → Option Nat)
    (sound : ∀ e n, read e = some n → Value names calls e n)
    (arguments : List Expr) (values : List Nat) (ok : mapValues read arguments = some values) :
    Values names calls arguments values := by
  induction arguments generalizing values with
  | nil =>
    simp only [mapValues] at ok
    cases ok
    exact .nil
  | cons first rest ih =>
    cases head : read first with
    | none => simp [mapValues_cons,head] at ok
    | some value =>
      cases tail : mapValues read rest with
      | none => simp [mapValues_cons,head,tail] at ok
      | some remaining =>
        simp only [mapValues_cons,head,tail,Option.pure_def] at ok
        cases ok
        exact .cons first rest value remaining (sound first value head) (ih remaining tail)

theorem evaluate_value (fuel : Nat) (names : Names) (calls : Calls) (expression : Expr) (n : Nat)
    (ok : evaluate fuel names calls expression = some n) : Value names calls expression n := by
  induction fuel generalizing expression n with
  | zero => simp [evaluate] at ok
  | succ fuel ih =>
    cases expression with
    | number value =>
      simp only [evaluate_succ,evaluateStep] at ok
      cases ok
      exact .number _
    | name path => exact .name path n ok
    | add a b =>
      cases ha : evaluate fuel names calls a with
      | none => simp [evaluate_succ,evaluateStep,ha] at ok
      | some x =>
        cases hb : evaluate fuel names calls b with
        | none => simp [evaluate_succ,evaluateStep,ha,hb] at ok
        | some y =>
          simp only [evaluate_succ,evaluateStep,ha,hb,Option.pure_def] at ok
          cases ok
          exact .add a b x y (ih a x ha) (ih b y hb)
    | sub a b =>
      cases ha : evaluate fuel names calls a with
      | none => simp [evaluate_succ,evaluateStep,ha] at ok
      | some x =>
        cases hb : evaluate fuel names calls b with
        | none => simp [evaluate_succ,evaluateStep,ha,hb] at ok
        | some y =>
          by_cases nonnegative : y ≤ x
          · simp only [evaluate_succ,evaluateStep,ha,hb] at ok
            change (if y ≤ x then some (x-y) else none) = some n at ok
            rw [if_pos nonnegative] at ok
            cases ok
            exact .sub a b x y (ih a x ha) (ih b y hb) nonnegative
          · simp [evaluate_succ,evaluateStep,ha,hb,nonnegative] at ok
    | mul a b =>
      cases ha : evaluate fuel names calls a with
      | none => simp [evaluate_succ,evaluateStep,ha] at ok
      | some x =>
        cases hb : evaluate fuel names calls b with
        | none => simp [evaluate_succ,evaluateStep,ha,hb] at ok
        | some y =>
          simp only [evaluate_succ,evaluateStep,ha,hb,Option.pure_def] at ok
          cases ok
          exact .mul a b x y (ih a x ha) (ih b y hb)
    | call path arguments =>
      cases args : mapValues (evaluate fuel names calls) arguments with
      | none => simp [evaluate_succ,evaluateStep,args] at ok
      | some values =>
        simp only [evaluate_succ,evaluateStep,args] at ok
        exact .call path arguments values n (mapValues_sound names calls _ ih arguments values args) ok

/-- Explicit argument correspondence for callers of the independent evaluator.
The call interpretation is still an assumption requiring original-source binding. -/
theorem evaluate_call (fuel : Nat) (names : Names) (calls : Calls) (path : Path)
    (arguments : List Expr) (values : List Nat) (n : Nat)
    (args : Related (fun expression value => evaluate fuel names calls expression = some value)
      arguments values) (found : calls path values = some n) :
    evaluate (fuel+1) names calls (.call path arguments) = some n := by
  have all : mapValues (evaluate fuel names calls) arguments = some values := by
    clear found
    induction args with
    | nil => rfl
    | cons head _ ih => simp only [mapValues_cons,head,ih,Option.pure_def]; rfl
  simpa only [evaluate_succ,evaluateStep,all] using found

structure Predicate where
  left : Expr
  comparison : SourceAffine.Comparison
  right : Expr

/-- Original predicate computations, independent of produced affine rows. -/
def Predicate.Truth (fuel : Nat) (names : Names) (calls : Calls) (predicate : Predicate) : Prop :=
  ∃ a b,evaluate fuel names calls predicate.left = some a ∧
    evaluate fuel names calls predicate.right = some b ∧
    predicate.comparison.Relation (a : Int) (b : Int)

def PredicatesTruth (fuel : Nat) (names : Names) (calls : Calls) (predicates : List Predicate) : Prop :=
  ∀ predicate ∈ predicates,predicate.Truth fuel names calls

theorem predicates_append (fuel : Nat) (names : Names) (calls : Calls) (a b : List Predicate) :
    PredicatesTruth fuel names calls (a ++ b) ↔
      PredicatesTruth fuel names calls a ∧ PredicatesTruth fuel names calls b := by
  simp only [PredicatesTruth,List.mem_append,or_imp,forall_and]

theorem predicates_singleton (fuel : Nat) (names : Names) (calls : Calls) (p : Predicate) :
    PredicatesTruth fuel names calls [p] ↔ p.Truth fuel names calls := by
  simp only [PredicatesTruth,List.mem_singleton,forall_eq]

def Predicate.check (fuel : Nat) (names : Names) (calls : Calls) (predicate : Predicate) : Option Unit := do
  let a ← evaluate fuel names calls predicate.left
  let b ← evaluate fuel names calls predicate.right
  if predicate.comparison.test (a : Int) (b : Int) then some () else none

theorem Predicate.check_of_truth (fuel : Nat) (names : Names) (calls : Calls) (p : Predicate)
    (truth : p.Truth fuel names calls) : p.check fuel names calls = some () := by
  obtain ⟨a,b,ha,hb,related⟩ := truth
  have compared := (SourceAffine.Comparison.test_relation _ _ _).mpr related
  simp only [check,ha,hb]
  change (if p.comparison.test (a : Int) (b : Int) then some () else none) = some ()
  rw [compared]
  rfl

/-- Original helper syntax and a specified formal assignment. This reference
executes original predicates/body; it never reads an affine template. Original
declaration, formal and dependency binding remain duties of its source adapter. -/
structure Definition where
  arity : Nat
  assignment : List Nat → Names
  premises : List Predicate
  body : Expr

def Definition.execute (definition : Definition) (calls : Calls) (arguments : List Nat) : Option Nat := do
  if arguments.length != definition.arity then none
  else
    let names := definition.assignment arguments
    if definition.premises.all (fun p => (p.check 128 names calls).isSome) then
      evaluate 128 names calls definition.body
    else none

theorem Definition.execute_of_body (definition : Definition) (calls : Calls)
    (arguments : List Nat) (n : Nat) (arity : arguments.length = definition.arity)
    (premises : PredicatesTruth 128 (definition.assignment arguments) calls definition.premises)
    (body : evaluate 128 (definition.assignment arguments) calls definition.body = some n) :
    definition.execute calls arguments = some n := by
  have all : definition.premises.all (fun p => (p.check 128 (definition.assignment arguments) calls).isSome) = true := by
    apply List.all_eq_true.mpr
    intro p member
    rw [Predicate.check_of_truth _ _ _ _ (premises p member)]
    rfl
  simpa only [execute,arity,bne_self_eq_false,Bool.false_eq_true,if_false,all,if_true] using body

end QleisliKernel.Semantics.SourceNatural
