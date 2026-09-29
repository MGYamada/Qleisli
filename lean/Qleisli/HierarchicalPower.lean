import Qleisli.ControlledPowers
import QleisliKernel.Hierarchical.Power

/-! Actual hierarchical control/repeat binding to coherent operator equations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Provider interpretations/equations must come from independent evidence. The
pending projection does not validate them or enable an external schema. -/

namespace Qleisli.HierarchicalPower
open QleisliKernel.Hierarchical
open QleisliKernel.Hierarchical.Artifact
open scoped Matrix

variable {T R : Type} [Fintype T] [DecidableEq T]

/-- Partial interpretation of the actual control/repeat bodies. Reads no proof,
claimed exponent or duplicate circuit witness. Providers are interpreted by
an independently established environment. -/
noncomputable def implementationOperator (artifact : Artifact) (index : Nat)
    (operations : Nat → Matrix T T ℂ) : Option (Matrix (Bool × T) (Bool × T) ℂ) := do
  let stage ← Power.implementationStage artifact index
  return ControlledPowers.singleOperator operations stage

/-- Logical powers use the meaning bodies' own provider/count/polarity and the
independent matrix-power meaning, not the implementation's literal iteration. -/
noncomputable def meaningOperator (artifact : Artifact) (index : Nat)
    (meanings : Nat → Matrix T T ℂ) : Option (Matrix (Bool × T) (Bool × T) ℂ) := do
  let stage ← Power.meaningStage artifact index
  return ControlledPowers.block fun b : Bool =>
    if b = stage.polarity then (meanings stage.provider)^stage.count else 1

theorem inspect_operators (artifact : Artifact) (index exponent provider remaining : Nat)
    (pending : Power.Pending)
    (accepted : Power.inspect artifact index exponent provider remaining = .ok pending)
    (operations meanings : Nat → Matrix T T ℂ)
    (providerEquation : operations pending.providerProof.implementation = meanings pending.providerProof.meaning) :
    implementationOperator artifact pending.root.implementation operations =
      some (ControlledPowers.controlled ((meanings pending.logical.provider)^(2^exponent))) ∧
    meaningOperator artifact pending.root.meaning meanings =
      some (ControlledPowers.controlled ((meanings pending.logical.provider)^(2^exponent))) := by
  obtain ⟨_,_,_,physical,logical,shape,_,_,_⟩ :=
    Power.inspect_binding artifact index exponent provider remaining pending accepted
  obtain ⟨implementation,meaning,count,polarity⟩ :=
    Power.shape_provider artifact pending.root pending.providerProof pending.actual pending.logical shape
  have checked := Power.inspect_stage artifact index exponent provider remaining pending accepted
  have stage : pending.actual = ⟨0,provider,2^exponent,true⟩ := by
    simp only [QleisliKernel.ControlledPowers.checkSingle, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.2
  have equation : operations provider = meanings pending.logical.provider := by
    simpa only [implementation,meaning,stage] using providerEquation
  have actual := ControlledPowers.checked_single_operator operations exponent provider pending.actual checked
  have logicalCount : pending.logical.count = 2^exponent := by simpa only [stage] using count.symm
  have logicalPolarity : pending.logical.polarity = true := by simpa only [stage] using polarity.symm
  constructor
  · simp [implementationOperator,physical,actual,equation]
  · simp [meaningOperator,logical,logicalCount,logicalPolarity,ControlledPowers.controlled]

theorem inspect_unitary (artifact : Artifact) (index exponent provider remaining : Nat)
    (pending : Power.Pending)
    (accepted : Power.inspect artifact index exponent provider remaining = .ok pending)
    (operations : Nat → Matrix T T ℂ)
    (providerIsometry : (operations pending.providerProof.implementation)ᴴ *
      operations pending.providerProof.implementation = 1) :
    ∃ U, implementationOperator artifact pending.root.implementation operations = some U ∧
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
  obtain ⟨_,_,_,physical,_,shape,_,_,_⟩ :=
    Power.inspect_binding artifact index exponent provider remaining pending accepted
  obtain ⟨implementation,_,_,_⟩ :=
    Power.shape_provider artifact pending.root pending.providerProof pending.actual pending.logical shape
  have checked := Power.inspect_stage artifact index exponent provider remaining pending accepted
  have stage : pending.actual = ⟨0,provider,2^exponent,true⟩ := by
    simp only [QleisliKernel.ControlledPowers.checkSingle, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.2
  have isometry : (operations provider)ᴴ * operations provider = 1 := by
    simpa only [implementation,stage] using providerIsometry
  have unitary := ControlledPowers.checked_single_unitary operations exponent provider pending.actual checked isometry
  exact ⟨_,by simp [implementationOperator,physical],unitary⟩

/-- temporary (TP-002), importance P2: projection-only entry wrapper. Retire once the
constructed derivation entry supplies the independently requested coherent
power conclusion, with public-API compatibility review. The whole-artifact entry additionally establishes all structural checks,
entry identity and the aggregate budget. The same provider premise remains. -/
theorem inspectEntry_equation (artifact : Artifact) (order : Array Nat) (exponent provider : Nat)
    (result : Power.Inspection)
    (accepted : Power.inspectEntry artifact order exponent provider = .ok result)
    (operations meanings : Nat → Matrix T T ℂ)
    (providerEquation : operations result.pending.providerProof.implementation =
      meanings result.pending.providerProof.meaning) :
    ∃ U, implementationOperator artifact artifact.entry.implementation operations = some U ∧
      meaningOperator artifact result.pending.root.meaning meanings = some U := by
  obtain ⟨_,localCheck,entry,_,_⟩ := Power.inspectEntry_binding artifact order exponent provider result accepted
  have equations := inspect_operators artifact artifact.entry.proof exponent provider _ result.pending
    localCheck operations meanings providerEquation
  exact ⟨_,by simpa only [entry] using equations.1,equations.2⟩

/-- temporary (TP-002), importance P2: projection-only reference wrapper. Retire with
`inspectEntry_equation` after the constructed entry bridge and public-API
review. Compare entire residual joint maps, retaining every control/reference
coherence. This is not a comparison of basis probabilities. -/
theorem inspectEntry_reference [Fintype R] [DecidableEq R]
    (artifact : Artifact) (order : Array Nat) (exponent provider : Nat)
    (result : Power.Inspection)
    (accepted : Power.inspectEntry artifact order exponent provider = .ok result)
    (operations meanings : Nat → Matrix T T ℂ)
    (providerEquation : operations result.pending.providerProof.implementation =
      meanings result.pending.providerProof.meaning)
    (U M : Matrix (Bool × T) (Bool × T) ℂ)
    (physical : implementationOperator artifact artifact.entry.implementation operations = some U)
    (logical : meaningOperator artifact result.pending.root.meaning meanings = some M)
    (rho : Matrix ((Bool × T) × R) ((Bool × T) × R) ℂ) :
    Qpe.outcomeMap U rho = Qpe.outcomeMap M rho := by
  obtain ⟨actual,hu,hm⟩ := inspectEntry_equation artifact order exponent provider result accepted
    operations meanings providerEquation
  have sameU := Option.some.inj (physical.symm.trans hu)
  have sameM := Option.some.inj (logical.symm.trans hm)
  rw [sameU,sameM]

end Qleisli.HierarchicalPower
