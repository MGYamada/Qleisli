import QleisliKernel.Raw.ObservationReferences
import QleisliKernel.Raw.BranchFunction

/-! Transport the original program interpretation between dependency snapshots.
No fresh reconstruction, accepted receipt or source-body meaning is assumed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.ObservationAgreement
open QleisliKernel QleisliKernel.Semantics.Finite
open QleisliKernel.Raw.EventTransport

theorem prepared_events (left right : List Dependency) (program : Semantics.Observation.Program)
    (prepared : Semantics.Observation.Prepared)
    (original : Semantics.Observation.read program = some prepared)
    (same : ∀ index, index ∈ Semantics.ObservingFunction.references 65 program.operations →
      left[index]? = right[index]?) : EventsAgree left right 65 prepared.events := by
  obtain ⟨⟨state,events⟩,first,finish⟩ := Option.bind_eq_some_iff.mp original
  have equal := Option.some.inj finish
  subst prepared
  apply events_append 65 events
  · exact read_ops left right 65 _ program.operations
      (of_references left right 65 program.operations same) ⟨state,events⟩ first
  · exact reorder left right 65 state.frame.length _

theorem execution_same (left right : List Dependency) (program : Semantics.Observation.Program)
    (prepared : Semantics.Observation.Prepared)
    (original : Semantics.Observation.read program = some prepared)
    (same : ∀ index, index ∈ Semantics.ObservingFunction.references 65 program.operations →
      left[index]? = right[index]?) (initial : Raw.Instrument.History) :
    Raw.Instrument.runEvents left 65 prepared.events initial =
      Raw.Instrument.runEvents right 65 prepared.events initial :=
  run_events left right 65 prepared.events (prepared_events left right program prepared original same) initial

/-- The original successful check supplies the reader and execution witnesses.
The same computation then runs under the final snapshot with identical exact
operator, complete history and remaining work. Unused slots may differ. -/
theorem reconstructed_execution (left right : List Dependency)
    (program : Semantics.Observation.Program) (actual : Semantics.Exact.Matrix)
    (work rest : Nat)
    (original : (Raw.BranchFunction.reconstruct left program).run work = (.ok actual,rest))
    (same : ∀ index, index ∈ Semantics.ObservingFunction.references 65 program.operations →
      left[index]? = right[index]?) :
    ∃ prepared initial history before after,
      Semantics.Observation.read program = some prepared ∧
      Exact.Matrix.identity (2^prepared.inputBits) = .ok initial ∧
      (Raw.Instrument.runEvents right 65 prepared.events ⟨[],[],initial⟩).run before = (.ok [history],after) ∧
      history.operator = actual ∧ history.hidden = [] := by
  obtain ⟨checked,initial,history,a,b,c,d,verified,identity,ran,meaning,hidden⟩ :=
    Raw.BranchFunction.reconstruct_execution left program actual work rest original
  have reader := (Raw.Observation.verify_conditions left program checked a b verified).2.2
  refine ⟨checked.prepared,initial,history,c,d,reader,identity,?_,meaning,hidden⟩
  rw [← execution_same left right program checked.prepared reader same]
  exact ran

end QleisliKernel.Raw.ObservationAgreement
