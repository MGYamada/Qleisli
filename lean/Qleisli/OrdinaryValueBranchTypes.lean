import Qleisli.Semantics.OrdinaryValueBranch

/-! Exact public type probe: no output Represents, successful checker, source
faithfulness or normalized operator premise may be silently added.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.OrdinaryValue.BranchTypes
open QleisliKernel.Semantics
open QleisliKernel.Semantics.OrdinaryValue
open RawInstrument

theorem branch_contract :
    ∀ (dependencies : List Finite.Dependency)
      (condition : Nat) (thenEvents elseEvents : List Observation.Event)
      (phis : List Observation.ClassicalPhi)
      (inputBasis outputBasis : FiniteCarrier.Basis)
      (inputStorage target : Storage) (armStorage : Bool → Storage)
      (meaning : Bool → Value → Value → Prop) (ready : History → Prop)
      (initial : History) (input : Value) (choice : Bool) (next : List History),
      ready initial → Represents initial.values inputBasis input inputStorage →
      Represents initial.values [.bit] (.bit choice) (.bit condition) →
      (∀ selected, ArmRunPreserves dependencies
        (if selected then thenEvents else elseEvents) ready
        inputBasis inputStorage outputBasis (armStorage selected) (meaning selected)) →
      (∀ selected, StorageTransport (KeptOrPhiEdge selected phis) (armStorage selected) target) →
      (∀ (selected : Bool) (middle : List History),
        Run dependencies (if selected then thenEvents else elseEvents) [initial] middle →
        ∀ before ∈ middle, ∀ phi ∈ phis, lookup before.values phi.output = none) →
      (phis.map Observation.ClassicalPhi.output).Nodup →
      Action dependencies (.branch condition thenEvents elseEvents phis) initial next →
      ∃ middle,
        Run dependencies (if choice then thenEvents else elseEvents) [initial] middle ∧
        List.Forall₂ (fun before after => ∃ result,
          meaning choice input result ∧ Represents after.values outputBasis result target ∧
          after.hidden = before.hidden ∧ after.operator = before.operator) middle next :=
  @branch_transports_of_run_preservation

end Qleisli.Semantics.OrdinaryValue.BranchTypes
