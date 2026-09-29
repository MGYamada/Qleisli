import Qleisli.QftUnitary
import Qleisli.ControlledPowers
import QleisliKernel.Schema

/-! Semantic consequences of the actual closed component dispatcher.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
External IR projection, provider evidence and transport remain separate. -/

namespace Qleisli.Schema
open scoped BigOperators Matrix

/-- temporary (TP-005), importance P1: Current pinned QFT component theorem. Replacement: full
hierarchical Fourier acceptance including actual reversal, H binding, exact
phase and both inverse laws. Retire only after QPE callers and the exported
registry type migrate, with public API compatibility review. Keep this theorem
built/audited and the external schema disabled until its binding gates pass. -/
theorem qft_sound (width : Nat) (proposal : QleisliKernel.Schema.Proposal)
    (receipt : QleisliKernel.Schema.Receipt)
    (accepted : QleisliKernel.Schema.check (.qft width) proposal = some receipt)
    (definitions : List QleisliKernel.QftGraph.Definition) (entry : Nat)
    (binding : proposal.witness = .qft definitions entry) :
    ∃ actual : QleisliKernel.QftGraph.Action,
      QleisliKernel.QftGraph.denote definitions entry = some actual ∧
      (QftGraph.matrix width actual)ᴴ * QftGraph.matrix width actual = 1 ∧
      QftGraph.matrix width actual * (QftGraph.matrix width actual)ᴴ = 1 ∧
      ∀ input output : Fin width → Bool,
        QftGraph.coefficient width actual input output =
          Complex.exp (2 * Real.pi * Complex.I * Qft.value width (Qft.finiteBits input) *
            Qft.value width (Qft.finiteBits output) / (2 : ℂ)^width) /
            (Real.sqrt ((2 : ℝ)^width) : ℂ) := by
  obtain ⟨actualDefs, actualEntry, circuit, projected, _, checked⟩ :=
    QleisliKernel.Schema.check_qft width proposal receipt accepted
  have same := QleisliKernel.Schema.Witness.qft.inj (projected.symm.trans binding)
  obtain ⟨sameDefs, sameEntry⟩ := same
  subst actualDefs
  subst actualEntry
  have meaning := (QleisliKernel.QftGraph.check_sound definitions entry width circuit checked).2.1
  have unitary := QftGraph.check_unitary definitions entry width circuit checked _ meaning
  exact ⟨_, meaning, unitary.1, unitary.2,
    QftGraph.check_fourier definitions entry width circuit checked _ meaning⟩

/-- temporary (TP-003), importance P2: legacy basis-conditioned dispatcher conclusion.
The registry already uses `power_coherent_sound`; retire this wrapper after
public-API compatibility review. Keep the underlying action lemmas used by QPE. -/
theorem power_sound {S : Type} (operation : Nat → S → S)
    (exponent provider : Nat) (proposal : QleisliKernel.Schema.Proposal)
    (receipt : QleisliKernel.Schema.Receipt)
    (accepted : QleisliKernel.Schema.check (.power exponent provider) proposal = some receipt)
    (stage : QleisliKernel.ControlledPowers.Stage)
    (binding : proposal.witness = .power stage) (bits : QleisliKernel.Interference.Bits)
    (state : S) :
    QleisliKernel.ControlledPowers.applyStage operation bits state stage =
      if bits 0 then QleisliKernel.ControlledPowers.iterate (operation provider)
        (2^exponent) state else state := by
  obtain ⟨actualStage, projected, _, checked⟩ :=
    QleisliKernel.Schema.check_power exponent provider proposal receipt accepted
  have same := QleisliKernel.Schema.Witness.power.inj (projected.symm.trans binding)
  subst actualStage
  exact QleisliKernel.ControlledPowers.checkSingle_action operation exponent provider stage checked bits state

/-- The registry's controlled-power conclusion concerns the full coherent
operator and actual native amplitude action, not a classical-control slice. -/
theorem power_coherent_sound {T R : Type} [Fintype T] [DecidableEq T]
    [Fintype R] [DecidableEq R] (operations : Nat → Matrix T T ℂ)
    (exponent provider : Nat) (proposal : QleisliKernel.Schema.Proposal)
    (receipt : QleisliKernel.Schema.Receipt)
    (accepted : QleisliKernel.Schema.check (.power exponent provider) proposal = some receipt)
    (stage : QleisliKernel.ControlledPowers.Stage)
    (binding : proposal.witness = .power stage)
    (providerIsometry : (operations provider)ᴴ * operations provider = 1) :
    ControlledPowers.singleOperator operations stage =
      ControlledPowers.controlled ((operations provider)^(2^exponent)) ∧
    (ControlledPowers.singleOperator operations stage)ᴴ *
      ControlledPowers.singleOperator operations stage = 1 ∧
    ControlledPowers.singleOperator operations stage *
      (ControlledPowers.singleOperator operations stage)ᴴ = 1 ∧
    (∀ (amplitude : Bool × T → ℂ) (b : Bool) (i : T),
      QleisliKernel.ControlledPowers.coherentStage (fun p v => operations p *ᵥ v)
        (fun bit axis => axis == 0 && bit) (fun bit j => amplitude (bit,j)) stage b i =
        (ControlledPowers.singleOperator operations stage *ᵥ amplitude) (b,i)) ∧
    (∀ rho : Matrix ((Bool × T) × R) ((Bool × T) × R) ℂ,
      Qpe.outcomeMap (ControlledPowers.singleOperator operations stage) rho =
        Qpe.outcomeMap (ControlledPowers.controlled ((operations provider)^(2^exponent))) rho) := by
  obtain ⟨actualStage, projected, _, checked⟩ :=
    QleisliKernel.Schema.check_power exponent provider proposal receipt accepted
  have same := QleisliKernel.Schema.Witness.power.inj (projected.symm.trans binding)
  subst actualStage
  have unitary := ControlledPowers.checked_single_unitary operations exponent provider stage checked providerIsometry
  exact ⟨ControlledPowers.checked_single_operator operations exponent provider stage checked,
    unitary.1, unitary.2,
    ControlledPowers.checked_single_native operations exponent provider stage checked,
    ControlledPowers.checked_single_reference operations exponent provider stage checked⟩

/-- temporary (TP-006), importance P1: Current pinned QPE component theorem. Replacement: full
hierarchical instrument acceptance binding actual preparation, verified
provider/control access, inverse QFT and measurement, with the same branches,
complete trace/reference result and boundary/freshness obligations. Retire only
after callers and the exported registry type migrate, with public API review.
Keep this theorem built/audited and the external schema disabled until its
binding gates pass. -/
theorem qpe_sound {R : Type} [Fintype R] [DecidableEq R]
    (targetWidth precision provider : Nat)
    (operations : Nat → Matrix (Fin (2^targetWidth)) (Fin (2^targetWidth)) ℂ)
    (proposal : QleisliKernel.Schema.Proposal) (receipt : QleisliKernel.Schema.Receipt)
    (accepted : QleisliKernel.Schema.check (.qpe targetWidth precision provider) proposal = some receipt)
    (plan : QleisliKernel.Qpe.Plan) (binding : proposal.witness = .qpe plan)
    (isometry : (operations provider)ᴴ * operations provider = 1) :
    ∃ actual : QleisliKernel.QftGraph.Action,
      QleisliKernel.QftGraph.denote plan.fourier plan.fourierEntry = some actual ∧
      plan.boundary = QleisliKernel.Qpe.header targetWidth precision ∧
      plan.precisionInitial = List.replicate precision false ∧
      Kraus.Complete (Qpe.branch precision plan.preparation plan.powers operations actual) ∧
      ∀ rho : Matrix (Fin (2^targetWidth) × R) (Fin (2^targetWidth) × R) ℂ,
        (∀ outcome : Fin precision → Bool,
          Qpe.outcomeMap (Qpe.branch precision plan.preparation plan.powers operations actual outcome) rho =
            Qpe.outcomeMap (Qpe.kraus precision (operations provider)
              (Qft.value precision (Qft.finiteBits outcome))) rho) ∧
        (∑ outcome : Fin precision → Bool,
          Matrix.trace (Qpe.outcomeMap
            (Qpe.branch precision plan.preparation plan.powers operations actual outcome) rho)) =
          Matrix.trace rho := by
  obtain ⟨actualPlan, circuit, projected, _, checked⟩ :=
    QleisliKernel.Schema.check_qpe targetWidth precision provider proposal receipt accepted
  have same := QleisliKernel.Schema.Witness.qpe.inj (projected.symm.trans binding)
  subst actualPlan
  exact Qpe.accepted_plan targetWidth precision provider operations plan circuit checked isometry

end Qleisli.Schema
