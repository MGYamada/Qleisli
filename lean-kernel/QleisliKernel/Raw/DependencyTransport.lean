import QleisliKernel.Raw.BranchFunction

/-! Dependency transport for the actual finite computations. Only the entries
referenced by the original steps must agree; errors and remaining work agree too.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.DependencyTransport
open QleisliKernel QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact

def StepAgrees (left right : List Dependency) (step : Step) : Prop :=
  ∀ axes index adjoint, step.action = .contract axes index adjoint →
    left[index]? = right[index]?

def StepsAgree (left right : List Dependency) (steps : List Step) : Prop :=
  ∀ step, step ∈ steps → StepAgrees left right step

theorem fold_same {m : Type → Type} [Monad m] {α β : Type}
    (items : List α) (first second : β → α → m β)
    (same : ∀ item, item ∈ items → ∀ state, first state item = second state item)
    (initial : β) : items.foldlM first initial = items.foldlM second initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    change (first initial item >>= fun state => rest.foldlM first state) =
      (second initial item >>= fun state => rest.foldlM second state)
    rw [same item (by simp) initial]
    apply congrArg (fun continuation => second initial item >>= continuation)
    funext state
    exact ih (fun item member => same item (List.mem_cons_of_mem _ member)) state

theorem all_same {α : Type} (items : List α) (first second : α → Bool)
    (same : ∀ item, item ∈ items → first item = second item) :
    items.all first = items.all second := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.all_cons]
    rw [same item (by simp),ih (fun item member => same item (List.mem_cons_of_mem _ member))]

theorem step_valid {left right step} (same : StepAgrees left right step) (bits : Nat) :
    Finite.stepValid left bits step = Finite.stepValid right bits step := by
  cases action : step.action with
  | hadamard _ => simp only [Finite.stepValid,action]
  | monomial _ _ _ => simp only [Finite.stepValid,action]
  | contract axes index adjoint =>
    have lookup := same axes index adjoint action
    simp only [Finite.stepValid,action,lookup]

theorem step_cost {left right step} (same : StepAgrees left right step) :
    Finite.stepCost left step = Finite.stepCost right step := by
  cases action : step.action with
  | hadamard _ => simp only [Finite.stepCost,action]
  | monomial _ _ _ => simp only [Finite.stepCost,action]
  | contract axes index adjoint =>
    have lookup := same axes index adjoint action
    simp only [Finite.stepCost,action,lookup]

theorem contributions {left right step} (same : StepAgrees left right step)
    (label : Nat) (value : Scalar) :
    Finite.contributions left step label value = Finite.contributions right step label value := by
  cases action : step.action with
  | hadamard _ => simp only [Finite.contributions,action]
  | monomial _ _ _ => simp only [Finite.contributions,action]
  | contract axes index adjoint =>
    have lookup := same axes index adjoint action
    simp only [Finite.contributions,action,lookup]

theorem apply_step {left right step} (same : StepAgrees left right step) (values : List Scalar) :
    Finite.applyStep left step values = Finite.applyStep right step values := by
  unfold Finite.applyStep
  apply fold_same
  intro pair _ state
  rcases pair with ⟨value,label⟩
  dsimp only
  rw [contributions same]

theorem circuit_valid {left right circuit} (same : StepsAgree left right circuit.steps) :
    Finite.circuitValid left circuit = Finite.circuitValid right circuit := by
  unfold Finite.circuitValid
  rw [all_same circuit.steps _ _ (fun step member => step_valid (same step member) _)]

/-- Exact equality of the actual checker computation, not just of successful
test matrices. Unused entries may differ or be absent from either vector. -/
theorem circuit_matrix {left right circuit} (same : StepsAgree left right circuit.steps) :
    Finite.circuitMatrix left circuit = Finite.circuitMatrix right circuit := by
  have charges (dimension : Nat) :
      circuit.steps.foldlM (fun _ step =>
        Finite.exactWork (Exact.charge (dimension*dimension*Finite.stepCost left step))) () =
      circuit.steps.foldlM (fun _ step =>
        Finite.exactWork (Exact.charge (dimension*dimension*Finite.stepCost right step))) () := by
    apply fold_same
    intro step member state
    rw [step_cost (same step member)]
  have applications (values : List Scalar) :
      circuit.steps.foldlM (fun state step => Finite.applyStep left step state) values =
      circuit.steps.foldlM (fun state step => Finite.applyStep right step state) values := by
    apply fold_same
    intro step member state
    exact apply_step (same step member) state
  simp only [Finite.circuitMatrix,circuit_valid same,charges,applications]

end QleisliKernel.Raw.DependencyTransport
