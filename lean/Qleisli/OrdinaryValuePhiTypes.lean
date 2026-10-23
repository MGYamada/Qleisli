import Qleisli.Semantics.OrdinaryValuePhi

/-! Exact statement assertions for the transport lemmas. Their explicit binders
exclude an extra target-representation, successful-checker or source-faithfulness
premise.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.Semantics.OrdinaryValue.PhiTypes
open QleisliKernel.Semantics
open QleisliKernel.Semantics.OrdinaryValue

theorem generic_transport_contract :
    ∀ {relation : Nat → Nat → Prop} {before after : Valuation}
      {basis : FiniteCarrier.Basis} {logical : Value} {source : Storage},
      Represents before basis logical source → LookupAlong relation before after →
      ∀ {target : Storage}, StorageTransport relation source target →
        Represents after basis logical target := @Represents.transport

theorem actual_merge_contract :
    ∀ {basis : FiniteCarrier.Basis} {logical : Value} {source target : Storage}
      (before after : RawInstrument.History) (choice : Bool)
      (phis : List Observation.ClassicalPhi),
      Represents before.values basis logical source →
      StorageTransport (PhiEdge choice phis) source target →
      RawInstrument.merged choice phis before = some after →
      (∀ phi ∈ phis, lookup before.values phi.output = none) →
      (phis.map Observation.ClassicalPhi.output).Nodup →
      Represents after.values basis logical target ∧
        after.hidden = before.hidden ∧ after.operator = before.operator := @merged_transports

theorem actual_kept_merge_contract :
    ∀ {basis : FiniteCarrier.Basis} {logical : Value} {source target : Storage}
      (before after : RawInstrument.History) (choice : Bool)
      (phis : List Observation.ClassicalPhi),
      Represents before.values basis logical source →
      StorageTransport (KeptOrPhiEdge choice phis) source target →
      RawInstrument.merged choice phis before = some after →
      (∀ phi ∈ phis, lookup before.values phi.output = none) →
      (phis.map Observation.ClassicalPhi.output).Nodup →
      Represents after.values basis logical target ∧
        after.hidden = before.hidden ∧ after.operator = before.operator := @merged_transports_kept

end Qleisli.Semantics.OrdinaryValue.PhiTypes
