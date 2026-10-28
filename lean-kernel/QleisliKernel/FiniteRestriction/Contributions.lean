import QleisliKernel.FiniteRestriction.Coordinates

/-! Literal restriction of actual finite contributions, including exact phases,
dependency/adjoint selection and all errors. Selector-targeting actions refuse.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.FiniteRestriction
open QleisliKernel.Semantics.Finite
open QleisliKernel.Semantics.Exact

def packTerms (selector low : Nat) (terms : List (Nat × Scalar)) : List (Nat × Scalar) :=
  terms.map (fun term => (pack selector low term.1,term.2))

/-- A disabled selector predicate keeps the actual contribution unchanged;
no operation or arithmetic is performed, irrespective of the action tag. -/
theorem contributions_disabled_selector (dependencies : List Dependency) (step : Step)
    (selector low high : Nat) (bound : low < 2^selector) (value : Scalar)
    (disabled : enabled (selectorControls selector step.controls) low = false) :
    QleisliKernel.Finite.contributions dependencies step (pack selector low high) value =
      if value == Scalar.zero then .ok [] else .ok [(pack selector low high,value)] := by
  have control := enabled_pack selector low high bound step.controls
  rw [disabled, Bool.false_and] at control
  simp [QleisliKernel.Finite.contributions, control, pure, Except.pure, bind, Except.bind]

/-- The actual executable monomial contribution keeps its exact phase and
ordered target axes. Even malformed lookups or scalar errors agree exactly. -/
theorem contributions_monomial (dependencies : List Dependency) (controls : List Control)
    (selector low high : Nat) (bound : low < 2^selector) (value : Scalar)
    (axes permutation phases : List Nat) (after : ∀ axis ∈ axes, selector ≤ axis)
    (active : enabled (selectorControls selector controls) low = true) :
    QleisliKernel.Finite.contributions dependencies ⟨controls,.monomial axes permutation phases⟩
        (pack selector low high) value =
      (QleisliKernel.Finite.contributions dependencies
        ⟨targetControls selector controls,.monomial (axes.map (·-selector)) permutation phases⟩
        high value).map (packTerms selector low) := by
  have control := enabled_pack selector low high bound controls
  rw [active, Bool.true_and] at control
  have gathered := gather_pack selector low high bound axes after
  cases zero : value == Scalar.zero with
  | true => simp [QleisliKernel.Finite.contributions, zero, packTerms, pure, Except.pure, Except.map]
  | false =>
    cases localActive : enabled (targetControls selector controls) high with
    | false => simp [QleisliKernel.Finite.contributions, zero, control, localActive, packTerms,
        pure, Except.pure, Except.map, bind, Except.bind]
    | true =>
      cases output : permutation[gather high (axes.map (·-selector))]? with
      | none =>
        simp [QleisliKernel.Finite.contributions, zero, control, localActive, gathered,
          QleisliKernel.Finite.readOption, output, bind, Except.bind, Except.map, pure, Except.pure]
      | some outputLabel =>
        cases phase : phases[gather high (axes.map (·-selector))]? with
        | none =>
          simp [QleisliKernel.Finite.contributions, zero, control, localActive, gathered,
            QleisliKernel.Finite.readOption, output, phase, bind, Except.bind, Except.map, pure, Except.pure]
        | some phaseLabel =>
          cases scaled : QleisliKernel.Exact.Scalar.mul value (QleisliKernel.Exact.Scalar.phase phaseLabel) with
          | error error =>
            simp [QleisliKernel.Finite.contributions, zero, control, localActive, gathered,
              QleisliKernel.Finite.readOption, output, phase, QleisliKernel.Finite.arithmetic, scaled,
              bind, Except.bind, Except.mapError, Except.map, pure, Except.pure]
          | ok scaledValue =>
            simp [QleisliKernel.Finite.contributions, zero, control, localActive, gathered,
              QleisliKernel.Finite.readOption, output, phase, QleisliKernel.Finite.arithmetic,
              scaled, packTerms, scatter_pack selector low high outputLabel bound axes after,
              bind, Except.bind, Except.mapError, pure, Except.pure, Except.map]

theorem pack_injective (selector low left right : Nat) (bound : low < 2^selector) :
    pack selector low left = pack selector low right ↔ left = right := by
  constructor
  · intro same
    have projected := congrArg (fun label => label / 2^selector) same
    simpa only [pack_high selector low left bound, pack_high selector low right bound] using projected
  · intro same
    rw [same]

theorem low_pack (selector low high axis : Nat) (bound : low < 2^selector) :
    pack selector low high - bit (pack selector low high) (selector+axis) * 2^(selector+axis) =
      pack selector low (high - bit high axis * 2^axis) := by
  have actual := update_pack selector low high axis 0 0 bound
  simpa only [bit, Nat.zero_div, Nat.zero_mod, Nat.zero_mul, Nat.add_zero] using actual

theorem high_pack (selector low high axis : Nat) (bound : low < 2^selector) :
    pack selector low high - bit (pack selector low high) (selector+axis) * 2^(selector+axis)
      + 2^(selector+axis) = pack selector low (high - bit high axis * 2^axis + 2^axis) := by
  rw [low_pack selector low high axis bound, Nat.pow_add]
  simp only [pack, Nat.mul_add, Nat.add_assoc]

/-- Hadamard keeps both exact output terms and its input-dependent minus sign.
Arithmetic failures also agree; no density or phase quotient is substituted. -/
theorem contributions_hadamard (dependencies : List Dependency) (controls : List Control)
    (selector low high axis : Nat) (bound : low < 2^selector) (value : Scalar)
    (active : enabled (selectorControls selector controls) low = true) :
    QleisliKernel.Finite.contributions dependencies ⟨controls,.hadamard (selector+axis)⟩
        (pack selector low high) value =
      (QleisliKernel.Finite.contributions dependencies
        ⟨targetControls selector controls,.hadamard axis⟩ high value).map (packTerms selector low) := by
  have control := enabled_pack selector low high bound controls
  rw [active, Bool.true_and] at control
  have lowEq := low_pack selector low high axis bound
  have highEq := high_pack selector low high axis bound
  rw [lowEq] at highEq
  have signed : (pack selector low high ==
      pack selector low (high - bit high axis * 2^axis + 2^axis)) =
      (high == high - bit high axis * 2^axis + 2^axis) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, pack_injective selector low high _ bound]
  cases zero : value == Scalar.zero with
  | true => simp [QleisliKernel.Finite.contributions, zero, packTerms, pure, Except.pure, Except.map]
  | false =>
    cases localActive : enabled (targetControls selector controls) high with
    | false => simp [QleisliKernel.Finite.contributions, zero, control, localActive, packTerms,
        pure, Except.pure, Except.map, bind, Except.bind]
    | true =>
      cases scaled : QleisliKernel.Exact.Scalar.mul value QleisliKernel.Finite.halfRoot with
      | error error =>
        simp [QleisliKernel.Finite.contributions, zero, control, localActive,
          QleisliKernel.Finite.arithmetic, scaled, pure, Except.pure, bind, Except.bind,
          Except.mapError, Except.map]
      | ok scaledValue =>
        cases sign : high == high - bit high axis * 2^axis + 2^axis with
        | false =>
          simp [QleisliKernel.Finite.contributions, zero, control, localActive,
            QleisliKernel.Finite.arithmetic, scaled, lowEq, highEq, signed, sign, packTerms,
            pure, Except.pure, bind, Except.bind, Except.mapError, Except.map]
        | true =>
          cases negative : QleisliKernel.Exact.Scalar.neg scaledValue with
          | error error =>
            simp [QleisliKernel.Finite.contributions, zero, control, localActive,
              QleisliKernel.Finite.arithmetic, scaled, lowEq, highEq, signed, sign, negative,
              pure, Except.pure, bind, Except.bind, Except.mapError, Except.map]
          | ok negativeValue =>
            simp [QleisliKernel.Finite.contributions, zero, control, localActive,
              QleisliKernel.Finite.arithmetic, scaled, lowEq, highEq, signed, sign, negative, packTerms,
              pure, Except.pure, bind, Except.bind, Except.mapError, Except.map]

/-- The exact original dependency matrix, adjoint flag and output ordinal are
unchanged. Accumulated terms keep their original order and coefficients. -/
theorem contractContribution_pack (meaning : Matrix) (axes : List Nat) (adjoint : Bool)
    (selector low high : Nat) (bound : low < 2^selector) (value : Scalar)
    (terms : List (Nat × Scalar)) (output : Nat) (after : ∀ axis ∈ axes, selector ≤ axis) :
    QleisliKernel.Finite.contractContribution meaning axes adjoint (pack selector low high) value
        (packTerms selector low terms) output =
      (QleisliKernel.Finite.contractContribution meaning (axes.map (·-selector)) adjoint
        high value terms output).map (packTerms selector low) := by
  have gathered := gather_pack selector low high bound axes after
  cases coefficient : QleisliKernel.Finite.dependencyCoefficient meaning adjoint
      (gather high (axes.map (·-selector))) output with
  | error error =>
    simp [QleisliKernel.Finite.contractContribution, gathered, coefficient,
      bind, Except.bind, Except.map]
  | ok coeff =>
    cases zero : coeff == Scalar.zero with
    | true =>
      simp [QleisliKernel.Finite.contractContribution, gathered, coefficient, zero,
        bind, Except.bind, pure, Except.pure, Except.map]
    | false =>
      cases scaled : QleisliKernel.Exact.Scalar.mul value coeff with
      | error error =>
        simp [QleisliKernel.Finite.contractContribution, gathered, coefficient, zero,
          QleisliKernel.Finite.arithmetic, scaled, bind, Except.bind, Except.mapError, Except.map,
          pure, Except.pure]
      | ok scaledValue =>
        simp [QleisliKernel.Finite.contractContribution, gathered, coefficient, zero,
          QleisliKernel.Finite.arithmetic, scaled, bind, Except.bind, pure, Except.pure,
          Except.mapError, Except.map, packTerms, scatter_pack selector low high output bound axes after]

theorem contractFold_pack (meaning : Matrix) (axes : List Nat) (adjoint : Bool)
    (selector low high : Nat) (bound : low < 2^selector) (value : Scalar)
    (terms : List (Nat × Scalar)) (outputs : List Nat) (after : ∀ axis ∈ axes, selector ≤ axis) :
    outputs.foldlM (QleisliKernel.Finite.contractContribution meaning axes adjoint
        (pack selector low high) value) (packTerms selector low terms) =
      (outputs.foldlM (QleisliKernel.Finite.contractContribution meaning (axes.map (·-selector))
        adjoint high value) terms).map (packTerms selector low) := by
  induction outputs generalizing terms with
  | nil => simp [pure, Except.pure, Except.map]
  | cons output outputs ih =>
    simp only [List.foldlM_cons]
    rw [contractContribution_pack meaning axes adjoint selector low high bound value terms output after]
    cases actual : QleisliKernel.Finite.contractContribution meaning (axes.map (·-selector))
        adjoint high value terms output with
    | error error => simp [Except.map, bind, Except.bind]
    | ok next => simpa [actual, Except.map, bind, Except.bind] using ih next

/-- Contract steps use the same original dependency lookup and exact forward or
adjoint coefficients. The local restriction includes every produced term. -/
theorem contributions_contract (dependencies : List Dependency) (controls : List Control)
    (selector low high : Nat) (bound : low < 2^selector) (value : Scalar)
    (axes : List Nat) (index : Nat) (adjoint : Bool) (after : ∀ axis ∈ axes, selector ≤ axis)
    (active : enabled (selectorControls selector controls) low = true) :
    QleisliKernel.Finite.contributions dependencies ⟨controls,.contract axes index adjoint⟩
        (pack selector low high) value =
      (QleisliKernel.Finite.contributions dependencies
        ⟨targetControls selector controls,.contract (axes.map (·-selector)) index adjoint⟩
        high value).map (packTerms selector low) := by
  have control := enabled_pack selector low high bound controls
  rw [active, Bool.true_and] at control
  cases zero : value == Scalar.zero with
  | true => simp [QleisliKernel.Finite.contributions, zero, packTerms, pure, Except.pure, Except.map]
  | false =>
    cases localActive : enabled (targetControls selector controls) high with
    | false => simp [QleisliKernel.Finite.contributions, zero, control, localActive, packTerms,
        pure, Except.pure, Except.map, bind, Except.bind]
    | true =>
      cases dependency : dependencies[index]? with
      | none =>
        simp [QleisliKernel.Finite.contributions, zero, control, localActive,
          QleisliKernel.Finite.readOption, dependency, pure, Except.pure, bind, Except.bind, Except.map]
      | some actual =>
        have folded := contractFold_pack actual.meaning axes adjoint selector low high bound
          value [] (List.range actual.meaning.rows) after
        simpa [QleisliKernel.Finite.contributions, zero, control, localActive,
          QleisliKernel.Finite.readOption, dependency, pure, Except.pure, bind, Except.bind, packTerms]
          using folded

def restrictAction (selector : Nat) : Action → Action
  | .hadamard target => .hadamard (target-selector)
  | .monomial axes permutation phases => .monomial (axes.map (·-selector)) permutation phases
  | .contract axes index adjoint => .contract (axes.map (·-selector)) index adjoint

/-- Restrict the actual original step, first refusing every selector action.
Inactive selector predicates contribute identity, including scalar actions. -/
def restrictStep (selector label : Nat) (step : Step) : Option (Option Step) :=
  if (QleisliKernel.Finite.targets step.action).all (fun axis => selector ≤ axis) then
    if enabled (selectorControls selector step.controls) label then
      some (some ⟨targetControls selector step.controls,restrictAction selector step.action⟩)
    else some none
  else none

def localContributions (dependencies : List Dependency) (step : Option Step)
    (label : Nat) (value : Scalar) : Except QleisliKernel.Finite.Error (List (Nat × Scalar)) :=
  match step with
  | some step => QleisliKernel.Finite.contributions dependencies step label value
  | none => if value == Scalar.zero then .ok [] else .ok [(label,value)]

theorem contributions_active_step (dependencies : List Dependency) (step : Step)
    (selector low high : Nat) (bound : low < 2^selector) (value : Scalar)
    (after : ∀ axis ∈ QleisliKernel.Finite.targets step.action, selector ≤ axis)
    (active : enabled (selectorControls selector step.controls) low = true) :
    QleisliKernel.Finite.contributions dependencies step (pack selector low high) value =
      (QleisliKernel.Finite.contributions dependencies
        ⟨targetControls selector step.controls,restrictAction selector step.action⟩ high value).map
        (packTerms selector low) := by
  cases step with
  | mk controls action =>
    cases action with
    | hadamard target =>
      have targetBound : selector ≤ target := after target (by simp [QleisliKernel.Finite.targets])
      have actual := contributions_hadamard dependencies controls selector low high
        (target-selector) bound value active
      simpa only [restrictAction, Nat.add_sub_of_le targetBound] using actual
    | monomial axes permutation phases =>
      exact contributions_monomial dependencies controls selector low high bound value
        axes permutation phases after active
    | contract axes index adjoint =>
      exact contributions_contract dependencies controls selector low high bound value
        axes index adjoint after active

/-- A successful restriction of the original step commutes with its actual
executable contribution function, including every error and exact coefficient.
Circuit validity, input-vector embedding and full-root binding remain separate. -/
theorem restrictStep_contributions (dependencies : List Dependency) (step : Step)
    (selector low high : Nat) (bound : low < 2^selector) (value : Scalar)
    (restricted : Option Step) (ran : restrictStep selector low step = some restricted) :
    QleisliKernel.Finite.contributions dependencies step (pack selector low high) value =
      (localContributions dependencies restricted high value).map (packTerms selector low) := by
  cases allowed : (QleisliKernel.Finite.targets step.action).all (fun axis => selector ≤ axis) with
  | false => simp [restrictStep, allowed] at ran
  | true =>
    cases active : enabled (selectorControls selector step.controls) low with
    | false =>
      have same : restricted = none := by simpa [restrictStep, allowed, active] using ran.symm
      rw [same, contributions_disabled_selector dependencies step selector low high bound value active]
      cases zero : value == Scalar.zero <;> simp [localContributions, zero, packTerms, Except.map]
    | true =>
      have same : restricted = some ⟨targetControls selector step.controls,restrictAction selector step.action⟩ := by
        simpa [restrictStep, allowed, active] using ran.symm
      rw [same]
      have after : ∀ axis ∈ QleisliKernel.Finite.targets step.action, selector ≤ axis := by
        simpa only [List.all_eq_true, decide_eq_true_eq] using allowed
      exact contributions_active_step dependencies step selector low high bound value after active

end QleisliKernel.FiniteRestriction
