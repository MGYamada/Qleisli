import Qleisli.FiniteMatrixAction
import QleisliKernel.FiniteRestriction.Check

/-! Literal total-complex action on an actual successfully restricted sector.
Every original step is visited in order. Uncontrolled scaffolding is retained;
a disabled selector predicate is omitted only after proving its action is the
identity on the selected slice. No support, separability, normalization, bounded
availability, new selector policy or Gram-replacement claim is used here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.RawAction.Sector
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite
open QleisliKernel.FiniteRestriction

def slice (selector low : Nat) (values : Nat → ℂ) : Nat → ℂ :=
  fun high => values (pack selector low high)

theorem hadamard_pack (selector low high axis : Nat) (bound : low < 2^selector)
    (values : Nat → ℂ) :
    Protected.gate .h (selector+axis) values (pack selector low high) =
      Protected.gate .h axis (slice selector low values) high := by
  have lowEq := low_pack selector low high axis bound
  have highEq := high_pack selector low high axis bound
  rw [lowEq] at highEq
  simp only [Protected.gate, bit_target selector low high axis bound, slice]
  rw [lowEq, highEq]

theorem step_disabled (dependencies : List Dependency) (operation : Step)
    (selector low high : Nat) (bound : low < 2^selector) (values : Nat → ℂ)
    (disabled : enabled (selectorControls selector operation.controls) low = false) :
    step dependencies operation values (pack selector low high) = values (pack selector low high) := by
  have control := enabled_pack selector low high bound operation.controls
  rw [disabled, Bool.false_and] at control
  simp only [step, control, Bool.not_false, if_true]

theorem step_active (dependencies : List Dependency) (operation : Step)
    (selector low high : Nat) (bound : low < 2^selector) (values : Nat → ℂ)
    (after : ∀ axis ∈ QleisliKernel.Finite.targets operation.action, selector ≤ axis)
    (active : enabled (selectorControls selector operation.controls) low = true) :
    step dependencies operation values (pack selector low high) =
      step dependencies ⟨targetControls selector operation.controls, restrictAction selector operation.action⟩
        (slice selector low values) high := by
  have control := enabled_pack selector low high bound operation.controls
  rw [active, Bool.true_and] at control
  rcases operation with ⟨controls, action⟩
  cases action with
  | hadamard axis =>
    have axisBound : selector ≤ axis := after axis (List.mem_singleton_self axis)
    have localGate := hadamard_pack selector low high (axis-selector) bound values
    rw [Nat.add_sub_of_le axisBound] at localGate
    simp only [step, restrictAction, control, localGate, slice]
  | monomial axes permutation phases =>
    have gathered := gather_pack selector low high bound axes after
    have scattered (input : Nat) := scatter_pack selector low high input bound axes after
    simp only [step, restrictAction, control, gathered, scattered, slice]
  | contract axes dependency adjoint =>
    have gathered := gather_pack selector low high bound axes after
    have scattered (input : Nat) := scatter_pack selector low high input bound axes after
    simp only [step, restrictAction, control, gathered, scattered, slice]

/-- Success is exactly the existing reader's selector-target refusal and
predicate decision. The unchanged local step is read from that actual result. -/
theorem restrictStep_slice (dependencies : List Dependency) (operation : Step)
    (selector low : Nat) (bound : low < 2^selector) (restricted : Option Step)
    (ran : restrictStep selector low operation = some restricted) (values : Nat → ℂ) :
    slice selector low (step dependencies operation values) =
      circuit dependencies restricted.toList (slice selector low values) := by
  cases allowed : (QleisliKernel.Finite.targets operation.action).all (fun axis => selector ≤ axis) with
  | false => simp [restrictStep, allowed] at ran
  | true =>
    cases active : enabled (selectorControls selector operation.controls) low with
    | false =>
      have same : restricted = none := by simpa [restrictStep, allowed, active] using ran.symm
      rw [same]
      funext high
      exact step_disabled dependencies operation selector low high bound values active
    | true =>
      have same : restricted = some ⟨targetControls selector operation.controls,
          restrictAction selector operation.action⟩ := by
        simpa [restrictStep, allowed, active] using ran.symm
      rw [same]
      have after : ∀ axis ∈ QleisliKernel.Finite.targets operation.action, selector ≤ axis := by
        simpa only [List.all_eq_true, decide_eq_true_eq] using allowed
      funext high
      exact step_active dependencies operation selector low high bound values after active

/-- The slice is arbitrary on every target and reference coordinate. Neither
other selector amplitudes nor any untouched reference system are discarded. -/
theorem restrictSteps_slice (dependencies : List Dependency) (operations restricted : List Step)
    (selector low : Nat) (bound : low < 2^selector)
    (ran : restrictSteps selector low operations = some restricted) (values : Nat → ℂ) :
    slice selector low (circuit dependencies operations values) =
      circuit dependencies restricted (slice selector low values) := by
  induction operations generalizing values restricted with
  | nil =>
    have same : restricted = [] := by simpa [restrictSteps] using ran.symm
    subst restricted
    rfl
  | cons first rest ih =>
    cases headRan : restrictStep selector low first with
    | none => simp [restrictSteps_cons, headRan] at ran
    | some head =>
      cases tailRan : restrictSteps selector low rest with
      | none => simp [restrictSteps_cons, headRan, tailRan] at ran
      | some tail =>
        have tailMeaning : slice selector low (circuit dependencies rest (step dependencies first values)) =
            circuit dependencies tail (slice selector low (step dependencies first values)) := by
          apply ih
          exact tailRan
        have headMeaning := restrictStep_slice dependencies first selector low bound head headRan values
        cases head with
        | none =>
          have same : restricted = tail := by
            simpa [restrictSteps_cons, headRan, tailRan] using ran.symm
          subst restricted
          change slice selector low (circuit dependencies rest (step dependencies first values)) = _
          exact tailMeaning.trans (congrArg (circuit dependencies tail) headMeaning)
        | some localStep =>
          have same : restricted = localStep :: tail := by
            simpa [restrictSteps_cons, headRan, tailRan] using ran.symm
          subst restricted
          change slice selector low (circuit dependencies rest (step dependencies first values)) =
            circuit dependencies tail (step dependencies localStep (slice selector low values))
          exact tailMeaning.trans (congrArg (circuit dependencies tail) headMeaning)

/-- Use the same retained restriction and native reconstruction, without a
fresh matrix check or a proposed sector matrix. The existing Gram receipt stays
in the binding; this theorem does not replace it with a mathematical assertion. -/
theorem sector_binding_action {Reference : Type} (dependencies : List Dependency)
    (selector : Nat) (target : Basis) (operations : List Step) (label : Nat) (actual : Matrix)
    (binding : SectorEvaluationBinding dependencies selector target operations label actual)
    (joint : Nat → Reference → ℂ) (high : Nat) (reference : Reference) (bound : high < actual.rows) :
    circuit dependencies operations (fun input => joint input reference) (pack selector label high) =
      Qleisli.Semantics.Exact.action actual
        (fun input reference => joint (pack selector label input) reference) high reference := by
  obtain ⟨labelBound, restricted, before, after, _unitaryAfter, restrictedRead, reconstructed, _gram, _lift⟩ := binding
  have localMeaning := congrFun (restrictSteps_slice dependencies operations restricted selector label
    labelBound restrictedRead (fun input => joint input reference)) high
  have matrixMeaning := Qleisli.Finite.circuitMatrix_action dependencies ⟨target, restricted⟩
    actual before after reconstructed (fun input reference => joint (pack selector label input) reference)
    high reference bound
  exact localMeaning.trans matrixMeaning.symm

/-- Mapping an existing ordered receipt relation retains every label and its
own actual matrix, even when distinct occurrences have equal numerical values. -/
theorem sector_bindings_actions {Reference : Type} (dependencies : List Dependency)
    (selector : Nat) (target : Basis) (operations : List Step) (labels : List Nat) (actual : List Matrix)
    (bindings : QleisliKernel.Exact.ListRel (SectorEvaluationBinding dependencies selector target operations)
      labels actual) (joint : Nat → Reference → ℂ) :
    QleisliKernel.Exact.ListRel (fun (label : Nat) (matrix : Matrix) => ∀ reference high, high < matrix.rows →
      circuit dependencies operations (fun input => joint input reference) (pack selector label high) =
        Qleisli.Semantics.Exact.action matrix
          (fun input reference => joint (pack selector label input) reference) high reference) labels actual := by
  induction labels generalizing actual with
  | nil =>
    cases actual with
    | nil => trivial
    | cons matrix matrices => cases bindings
  | cons label labels ih =>
    cases actual with
    | nil => cases bindings
    | cons matrix matrices =>
      exact ⟨fun reference high bound => sector_binding_action dependencies selector target operations label matrix
        bindings.1 joint high reference bound, ih matrices bindings.2⟩

#print axioms restrictStep_slice
#print axioms restrictSteps_slice
#print axioms sector_binding_action
#print axioms sector_bindings_actions

end Qleisli.Semantics.RawAction.Sector
