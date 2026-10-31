import QleisliKernel.Qirf.RawTrace

/-! Test-only frozen prepared-root checker before header reservation refinement.
No runtime caller imports this alternate metering baseline.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RawTraceMeterContinuity
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.SourceOwners
open QleisliKernel.Qirf.RawTrace

def legacyCheck {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (positions : List Position) : WorkM (Checked source dependencies program positions) := do
  exactWork (Exact.charge (32*(positions.length+source.result.events.length+1)^2))
  guard (positions.length == source.result.events.length) .request
  let prepared ← Qirf.PureInterval.Many.prepare dependencies program
  let whole ← Qirf.PureInterval.readSlice program 0 program.operations.length
  let boundaries ← QleisliKernel.Raw.OwnerBoundaries.check (Qirf.SourceInterval.parameterOwners source.signature)
    program.inputs whole.operations
  if effect : Qirf.SourceInterval.effectMatches source.signature.original.parsedHeader.effect program.effect then
    if noClassical : program.classicalInputs = [] ∧ program.classicalOutputs = [] then
      if widths : Qirf.SourceInterval.inputWidths program
          (Qirf.SourceInterval.parameterOwners source.signature) = true then
        let allOwners ← Raw.OwnerFlow.check (Qirf.SourceInterval.parameterOwners source.signature)
          (valueOwners source.result.value) ⟨program.inputs,whole.operations,program.outputs,.unitary⟩
        if complete : Qirf.SourceSequence.covers program.operations.length positions = true then
          let sites ← readSites source dependencies program whole prepared boundaries source.result.events positions
          return ⟨prepared.whole,whole,boundaries,effect,noClassical,widths,allOwners.down,complete,sites⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request


/-- Paying a reservation leaves the actual continuation's computation, including
all subsequent failures and remaining work, unchanged. -/
theorem afterReservation {α : Type} (amount remaining : Nat) (action : WorkM α) :
    ((do exactWork (Exact.charge amount); action) : WorkM α).run (amount+remaining) =
      action.run remaining := by
  have paid : (exactWork (Exact.charge amount)).run (amount+remaining) =
      (.ok (),remaining) := by
    unfold exactWork Exact.charge
    simp only [ExceptT.run, arithmetic,
      show ¬ amount > amount+remaining from Nat.not_lt_of_ge (Nat.le_add_right amount remaining),
      ↓reduceIte, Nat.add_sub_cancel_left]
    rfl
  simp only [ExceptT.run, bind, ExceptT.bind, StateT.bind, ExceptT.mk]
  simp only [ExceptT.run] at paid
  rw [paid]
  rfl


/-- The metering change preserves the complete actual checker once each exact
header reservation is funded. This does not equate their starting budgets. -/
theorem funded_refinement {sources owner name} (source : Source sources owner name)
    (dependencies : List Semantics.Finite.Dependency) (program : Semantics.Observation.Program)
    (positions : List Position) (remaining : Nat) :
    (QleisliKernel.Qirf.RawTrace.check source dependencies program positions).run
      (headerWork source program positions+remaining) =
    (legacyCheck source dependencies program positions).run
      (32*(positions.length+source.result.events.length+1)^2+remaining) := by
  unfold QleisliKernel.Qirf.RawTrace.check legacyCheck
  rw [afterReservation,afterReservation]

end QleisliKernel.Tests.RawTraceMeterContinuity
