import QleisliKernel.Raw.EventContract

/-! Dependency transport through the actual clean computation recipe. Matrix
computations stay opaque in this structural proof; no cleanup rule is changed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.EventTransport
open QleisliKernel QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Raw.DependencyTransport

theorem clean {left right : List Dependency} (source data ancilla : Nat) (table : List Nat)
    (uses logical : List Step) (useAgreement : StepsAgree left right uses)
    (logicalAgreement : StepsAgree left right logical) :
    Raw.clean left source data ancilla table uses logical =
      Raw.clean right source data ancilla table uses logical := by
  let compute := Raw.computeStep source data ancilla table
  let physicalCircuit := Raw.circuit (data+ancilla) ([compute] ++ uses ++ [compute])
  have physical : StepsAgree left right physicalCircuit.steps := by
    intro step member
    change step ∈ [compute] ++ uses ++ [compute] at member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with (same | member) | same
    · subst step; exact compute_agrees left right source data ancilla table
    · exact useAgreement step member
    · subst step; exact compute_agrees left right source data ancilla table
  let recipe : Finite.WorkM Matrix → (Contract → Contract → Finite.WorkM Matrix) →
      Finite.WorkM Matrix := fun logicalRead physicalRead => do
    Finite.guard (source ≤ data && data+ancilla ≤ 6) .limit
    Finite.guard (Raw.tableValid source ancilla table false)
    let logical ← logicalRead
    Finite.wholeSpace logical
    let encoding ← Raw.zeroEncoding data ancilla
    let contract : Contract := ⟨encoding,encoding,logical⟩
    let actual ← physicalRead contract contract
    Finite.wholeSpace actual
    return logical
  have first : Finite.circuitMatrix left (Raw.circuit data logical) =
      Finite.circuitMatrix right (Raw.circuit data logical) :=
    circuit_matrix (circuit := Raw.circuit data logical) logicalAgreement
  have second : Finite.check left physicalCircuit = Finite.check right physicalCircuit := by
    funext claim required
    exact contract_check physical claim required
  change recipe (Finite.circuitMatrix left (Raw.circuit data logical))
      (Finite.check left physicalCircuit) =
    recipe (Finite.circuitMatrix right (Raw.circuit data logical))
      (Finite.check right physicalCircuit)
  rw [first,second]

end QleisliKernel.Raw.EventTransport
