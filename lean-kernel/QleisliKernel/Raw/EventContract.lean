import QleisliKernel.Raw.DependencyTransport

/-! Dependency transport for actual protected actions. Original source/event
correspondence and graph readiness remain separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.EventTransport
open QleisliKernel QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Raw.DependencyTransport

theorem contract_check {left right circuit} (same : StepsAgree left right circuit.steps)
    (claim required : Contract) :
    Finite.check left circuit claim required = Finite.check right circuit claim required := by
  simp only [Finite.check,circuit_matrix same]

theorem compute_agrees (left right : List Dependency) (source data ancilla : Nat) (table : List Nat) :
    StepAgrees left right (Raw.computeStep source data ancilla table) := by
  intro axes index adjoint impossible
  simp [Raw.computeStep,Semantics.Raw.computeStep] at impossible

end QleisliKernel.Raw.EventTransport
