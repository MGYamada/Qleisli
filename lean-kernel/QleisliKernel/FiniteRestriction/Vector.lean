import QleisliKernel.FiniteRestriction.Contributions

/-! Embedded sector vectors commute with the actual accumulator and applyStep.
Exact additions keep their original order; disabled sectors are identity.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.FiniteRestriction
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Exact

def block (selector low : Nat) (value : Scalar) : List Scalar :=
  List.replicate low Scalar.zero ++ value :: List.replicate (2^selector-low-1) Scalar.zero

def liftVector (selector low : Nat) (values : List Scalar) : List Scalar :=
  values.foldr (fun value rest => block selector low value ++ rest) []

theorem liftVector_cons (selector low : Nat) (value : Scalar) (rest : List Scalar) :
    liftVector selector low (value :: rest) =
      block selector low value ++ liftVector selector low rest := rfl

theorem block_length (selector low : Nat) (value : Scalar) (bound : low < 2^selector) :
    (block selector low value).length = 2^selector := by
  simp only [block, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem block_get (selector low : Nat) (value : Scalar) :
    (block selector low value)[low]? = some value := by
  simp [block]

theorem block_set (selector low : Nat) (value replacement : Scalar) :
    (block selector low value).set low replacement = block selector low replacement := by
  simp [block]

theorem pack_succ (selector low high : Nat) :
    pack selector low (high+1) = 2^selector + pack selector low high := by
  simp only [pack, Nat.mul_succ]
  omega

theorem liftVector_length (selector low : Nat) (values : List Scalar) (bound : low < 2^selector) :
    (liftVector selector low values).length = 2^selector * values.length := by
  induction values with
  | nil => simp [liftVector]
  | cons value rest ih =>
    simp only [liftVector_cons, List.length_append, block_length selector low value bound,
      ih, List.length_cons, Nat.mul_succ]
    omega

theorem liftVector_get (selector low : Nat) (values : List Scalar) (label : Nat)
    (bound : low < 2^selector) :
    (liftVector selector low values)[pack selector low label]? = values[label]? := by
  induction values generalizing label with
  | nil => simp [liftVector]
  | cons value rest ih =>
    have width := block_length selector low value bound
    cases label with
    | zero =>
      rw [liftVector_cons, show pack selector low 0 = low by simp [pack]]
      rw [List.getElem?_append_left (by rw [width]; exact bound)]
      exact block_get selector low value
    | succ label =>
      rw [liftVector_cons, pack_succ]
      rw [List.getElem?_append_right (by rw [width]; omega)]
      simpa [width] using ih label

theorem liftVector_set (selector low : Nat) (values : List Scalar) (label : Nat)
    (replacement : Scalar) (bound : low < 2^selector) :
    (liftVector selector low values).set (pack selector low label) replacement =
      liftVector selector low (values.set label replacement) := by
  induction values generalizing label with
  | nil => simp [liftVector]
  | cons value rest ih =>
    have width := block_length selector low value bound
    cases label with
    | zero => simp [liftVector_cons, pack, width, bound, block_set]
    | succ label =>
      rw [liftVector_cons, pack_succ]
      rw [List.set_append_right _ _ (by rw [width]; omega)]
      simp [width, ih label, liftVector_cons]

/-- Dense accumulator updates preserve both original coefficients and errors.
No reassociation or reordering of exact additions is used. -/
theorem addAt_lift (selector low : Nat) (values : List Scalar) (label : Nat)
    (coefficient : Scalar) (bound : low < 2^selector) :
    QleisliKernel.Finite.addAt (liftVector selector low values) (pack selector low label,coefficient) =
      (QleisliKernel.Finite.addAt values (label,coefficient)).map (liftVector selector low) := by
  cases previous : values[label]? with
  | none =>
    simp [QleisliKernel.Finite.addAt, liftVector_get selector low values label bound,
      previous, QleisliKernel.Finite.readOption, bind, Except.bind, Except.map]
  | some value =>
    cases added : QleisliKernel.Exact.Scalar.add value coefficient with
    | error error =>
      simp [QleisliKernel.Finite.addAt, liftVector_get selector low values label bound,
        previous, QleisliKernel.Finite.readOption, QleisliKernel.Finite.arithmetic,
        added, bind, Except.bind, Except.mapError, Except.map]
    | ok result =>
      simp [QleisliKernel.Finite.addAt, liftVector_get selector low values label bound,
        previous, QleisliKernel.Finite.readOption, QleisliKernel.Finite.arithmetic,
        added, liftVector_set selector low values label result bound,
        bind, Except.bind, pure, Except.pure, Except.mapError, Except.map]

theorem scalar_zero_add (value : Scalar) :
    QleisliKernel.Exact.Scalar.add Scalar.zero value = .ok value := by rfl

/-- Preserve the literal accumulation order, including failure of a later term. -/
theorem foldTerms_lift (selector low : Nat) (terms : List (Nat × Scalar))
    (values : List Scalar) (bound : low < 2^selector) :
    (packTerms selector low terms).foldlM QleisliKernel.Finite.addAt
        (liftVector selector low values) =
      (terms.foldlM QleisliKernel.Finite.addAt values).map (liftVector selector low) := by
  induction terms generalizing values with
  | nil => rfl
  | cons term rest ih =>
    simp only [packTerms, List.map_cons, List.foldlM_cons]
    rw [addAt_lift selector low values term.1 term.2 bound]
    cases added : QleisliKernel.Finite.addAt values term with
    | error error => simp [Except.map, bind, Except.bind]
    | ok result => simpa [added, Except.map, bind, Except.bind] using ih result

/-- Abbreviation of the actual `applyStep` fold function. -/
def visit (dependencies : List Dependency) (step : Step)
    (values : List Scalar) (input : Scalar × Nat) : Except QleisliKernel.Finite.Error (List Scalar) := do
  let terms ← QleisliKernel.Finite.contributions dependencies step input.2 input.1
  terms.foldlM QleisliKernel.Finite.addAt values

def localVisit (dependencies : List Dependency) (step : Option Step)
    (values : List Scalar) (input : Scalar × Nat) : Except QleisliKernel.Finite.Error (List Scalar) := do
  let terms ← localContributions dependencies step input.2 input.1
  terms.foldlM QleisliKernel.Finite.addAt values

theorem visit_lift (dependencies : List Dependency) (original : Step)
    (selector low high : Nat) (value : Scalar) (values : List Scalar)
    (restricted : Option Step) (bound : low < 2^selector)
    (ran : restrictStep selector low original = some restricted) :
    visit dependencies original (liftVector selector low values) (value,pack selector low high) =
      (localVisit dependencies restricted values (value,high)).map (liftVector selector low) := by
  unfold visit localVisit
  rw [restrictStep_contributions dependencies original selector low high bound value restricted ran]
  cases terms : localContributions dependencies restricted high value with
  | error error => simp [Except.map, bind, Except.bind]
  | ok result =>
    simpa [terms, Except.map, bind, Except.bind] using foldTerms_lift selector low result values bound

theorem visit_zero (dependencies : List Dependency) (step : Step)
    (values : List Scalar) (label : Nat) :
    visit dependencies step values (Scalar.zero,label) = .ok values := by
  simp [visit, QleisliKernel.Finite.contributions, pure, Except.pure, bind, Except.bind]

theorem visit_zeros (dependencies : List Dependency) (step : Step)
    (values : List Scalar) (count start : Nat) :
    ((List.replicate count Scalar.zero).zipIdx start).foldlM
      (visit dependencies step) values = .ok values := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp [List.replicate_succ, List.zipIdx_cons, List.foldlM_cons, visit_zero,
      bind, Except.bind, ih]

theorem visit_block (dependencies : List Dependency) (step : Step)
    (values : List Scalar) (selector low start : Nat) (value : Scalar) :
    ((block selector low value).zipIdx start).foldlM (visit dependencies step) values =
      visit dependencies step values (value,start+low) := by
  simp only [block, List.zipIdx_append, List.length_replicate, List.foldlM_append,
    List.zipIdx_cons, List.foldlM_cons, visit_zeros]
  cases result : visit dependencies step values (value,start+low) <;>
    simp [result, bind, Except.bind]

/-- The actual input traversal differs only by zero entries between sectors.
The retained nonzero inputs and every accumulator update keep their order. -/
theorem visitVector_lift (dependencies : List Dependency) (step : Step)
    (selector low : Nat) (values next : List Scalar) (offset : Nat)
    (restricted : Option Step) (bound : low < 2^selector)
    (ran : restrictStep selector low step = some restricted) :
    ((liftVector selector low values).zipIdx (2^selector * offset)).foldlM
        (visit dependencies step) (liftVector selector low next) =
      ((values.zipIdx offset).foldlM (localVisit dependencies restricted) next).map
        (liftVector selector low) := by
  induction values generalizing next offset with
  | nil => rfl
  | cons value rest ih =>
    rw [liftVector_cons, List.zipIdx_append, List.foldlM_append, visit_block]
    have inputIndex : 2^selector * offset + low = pack selector low offset := by
      simp only [pack, Nat.add_comm]
    have nextIndex : 2^selector * offset + (block selector low value).length =
        2^selector * (offset+1) := by
      rw [block_length selector low value bound, Nat.mul_succ]
    rw [inputIndex, nextIndex,
      visit_lift dependencies step selector low offset value next restricted bound ran]
    simp only [List.zipIdx_cons, List.foldlM_cons]
    cases visited : localVisit dependencies restricted next (value,offset) with
    | error error => simp [Except.map, bind, Except.bind]
    | ok result =>
      simpa [Except.map, bind, Except.bind] using ih result (offset+1)

theorem block_zero (selector low : Nat) (bound : low < 2^selector) :
    block selector low Scalar.zero = List.replicate (2^selector) Scalar.zero := by
  rw [block, ← List.replicate_succ, List.replicate_append_replicate]
  congr 1
  omega

theorem liftVector_zeros (selector low count : Nat) (bound : low < 2^selector) :
    liftVector selector low (List.replicate count Scalar.zero) =
      List.replicate (2^selector * count) Scalar.zero := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.replicate_succ, liftVector_cons, block_zero selector low bound, ih,
      List.replicate_append_replicate]
    congr 1
    simp only [Nat.mul_succ, Nat.add_comm]

/-- Retains the same literal traversal for the disabled case until the
separate identity-vector lemma discharges it. Some steps are definitionally
the actual finite evaluator, not an alternative acceptance implementation. -/
def localApply (dependencies : List Dependency) (step : Option Step)
    (values : List Scalar) : Except QleisliKernel.Finite.Error (List Scalar) :=
  values.zipIdx.foldlM (localVisit dependencies step) (List.replicate values.length Scalar.zero)

theorem localApply_some (dependencies : List Dependency) (step : Step) (values : List Scalar) :
    localApply dependencies (some step) values =
      QleisliKernel.Finite.applyStep dependencies step values := rfl

/-- Successful step restriction commutes with the actual executable applyStep
on every embedded sector vector, retaining all errors. No validity, size gate
or producer success receipt is hidden in a premise. -/
theorem applyStep_lift (dependencies : List Dependency) (step : Step)
    (selector low : Nat) (values : List Scalar) (restricted : Option Step)
    (bound : low < 2^selector) (ran : restrictStep selector low step = some restricted) :
    QleisliKernel.Finite.applyStep dependencies step (liftVector selector low values) =
      (localApply dependencies restricted values).map (liftVector selector low) := by
  have actual := visitVector_lift dependencies step selector low values
    (List.replicate values.length Scalar.zero) 0 restricted bound ran
  simpa only [Nat.mul_zero, liftVector_zeros selector low values.length bound,
    localApply, QleisliKernel.Finite.applyStep, visit, liftVector_length selector low values bound]
    using actual

theorem localVisit_none_end (dependencies : List Dependency) (leading tail : List Scalar)
    (value : Scalar) :
    localVisit dependencies none (leading ++ Scalar.zero :: tail) (value,leading.length) =
      .ok (leading ++ value :: tail) := by
  cases zero : value == Scalar.zero with
  | true =>
    have same : value = Scalar.zero := eq_of_beq zero
    subst value
    simp [localVisit, localContributions, bind, Except.bind, pure, Except.pure]
  | false =>
    simp [localVisit, localContributions, zero, QleisliKernel.Finite.addAt,
      QleisliKernel.Finite.readOption, QleisliKernel.Finite.arithmetic, scalar_zero_add,
      bind, Except.bind, pure, Except.pure, Except.mapError]

/-- The disabled local step reconstructs the vector in the same input order.
Even noncanonical scalar values are copied without arithmetic normalization. -/
theorem identityFold (dependencies : List Dependency) (values leading : List Scalar) :
    (values.zipIdx leading.length).foldlM (localVisit dependencies none)
        (leading ++ List.replicate values.length Scalar.zero) = .ok (leading ++ values) := by
  induction values generalizing leading with
  | nil => simp [pure, Except.pure]
  | cons value rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipIdx_cons, List.foldlM_cons,
      localVisit_none_end]
    simpa [bind, Except.bind, List.append_assoc] using ih (leading ++ [value])

theorem localApply_none (dependencies : List Dependency) (values : List Scalar) :
    localApply dependencies none values = .ok values := by
  simpa only [List.length_nil, List.nil_append, localApply] using identityFold dependencies values []

end QleisliKernel.FiniteRestriction
