import QleisliKernel.SourceTypes.SourceBasisBindings

/-! The same original guarded port closure used by coherent basis events,
applied to computed scopes without changing source identities or premises.
This closes no predicate, injection, native logical or clean-release equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceComputedBindings
open Finite

def port {sources} (obligation : GenericTypeTrace.ComputedObligation sources) :
    GenericTypeTrace.BasisObligation sources :=
  ⟨obligation.owner,obligation.name,obligation.offset,obligation.state,obligation.input,obligation.input⟩

abbrev Checked {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligations : List (GenericTypeTrace.ComputedObligation sources)) :=
  SourceBasisBindings.Checked instantiation (obligations.map port)

def prepare {sources owner name original}
    (instantiation : @StaticInstantiation.Checked sources owner name original)
    (obligations : List (GenericTypeTrace.ComputedObligation sources)) : WorkM (Checked instantiation obligations) :=
  SourceBasisBindings.prepare instantiation (obligations.map port)

def originalIndex {sources owner name original}
    {instantiation : @StaticInstantiation.Checked sources owner name original}
    {obligations : List (GenericTypeTrace.ComputedObligation sources)} {offset : Nat}
    (active : @SourceBasisBindings.ActiveAt sources owner name original instantiation
      (obligations.map port) offset) : Fin obligations.length :=
  ⟨active.index.val,by simpa only [List.length_map] using active.index.isLt⟩

theorem originalMember {sources owner name original}
    {instantiation : @StaticInstantiation.Checked sources owner name original}
    {obligations : List (GenericTypeTrace.ComputedObligation sources)} {offset : Nat}
    (active : @SourceBasisBindings.ActiveAt sources owner name original instantiation
      (obligations.map port) offset) :
    obligations[originalIndex active] ∈ obligations := List.getElem_mem (originalIndex active).isLt

end QleisliKernel.SourceTypes.SourceComputedBindings
