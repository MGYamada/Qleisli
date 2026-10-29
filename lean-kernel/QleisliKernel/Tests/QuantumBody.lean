import QleisliKernel.SourceTypes.QuantumBody

/-! Small complete-return reductions. Original-source and actual native checks
remain separate from these structural invariants; no maximum-size case is used.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.QuantumBody
open Semantics.SourceOwners SourceTypes.QuantumBody

private def selector : Owner := ⟨0,[.unit]⟩
private def target : Owner := ⟨1,[.unit]⟩
private def observed (pattern : Option (List String)) (suffix : List String) :=
  (finish pattern selector target [] suffix).map fun result => (result.value,result.remaining)

-- Distinct zero-width owners retain their identities in both return orders.
theorem direct_return : observed none [] = .ok ([.tuple 2,.owner selector,.owner target],[]) := by cbv

theorem renamed_return :
    observed (some ["pair"]) [";","let","(","a",",","b",")","=","pair",";","(","a",",","b",")"] =
      .ok ([.tuple 2,.owner selector,.owner target],[]) := by cbv

theorem reordered_return :
    observed (some ["(","a",",","b",")"]) [";","(","b",",","a",")"] =
      .ok ([.tuple 2,.owner target,.owner selector],[]) := by cbv

theorem grouped_return :
    observed (some ["(","a",",","b",")"]) [";","(","(","a",")",",","b",")"] =
      .ok ([.tuple 2,.owner selector,.owner target],[]) := by cbv

theorem repeated_return_refuses :
    (observed (some ["(","a",",","b",")"]) [";","(","a",",","a",")"] matches .error _) = true := by decide +kernel

theorem wildcard_cannot_drop_empty_owner :
    (observed (some ["(","_",",","b",")"]) [";","b"] matches .error _) = true := by decide +kernel

theorem missing_result_refuses :
    (observed (some ["pair"]) [";"] matches .error _) = true := by decide +kernel

theorem missing_terminator_refuses :
    (observed (some ["pair"]) ["pair"] matches .error _) = true := by decide +kernel

theorem direct_suffix_cannot_be_ignored :
    (observed none [";","(","q",",","s",")"] matches .error _) = true := by decide +kernel

theorem unknown_observation_refuses :
    (observed (some ["pair"]) [";","measure_z","(","pair",")"] matches .error _) = true := by decide +kernel

theorem unknown_discard_refuses :
    (observed (some ["(","a",",","b",")"]) [";","discard","(","a",")",";","b"] matches .error _) = true := by decide +kernel

theorem result_owner_is_not_tuple :
    resultShape (.owner []) [.tuple 2,.owner selector,.owner target] = false := by decide +kernel

theorem result_tuple_is_not_atomic_owner :
    resultShape (.tuple [[],[]]) [.owner ⟨0,[.tuple 2,.unit,.unit]⟩] = false := by decide +kernel

theorem result_tuple_arity_is_exact :
    resultShape (.tuple [[],[]]) [.tuple 1,.owner selector,.owner target] = false := by decide +kernel

theorem nested_result_is_not_flat_tuple :
    resultShape (.tuple [[],[]]) [.tuple 2,.tuple 1,.owner selector,.owner target] = false := by decide +kernel

theorem pending_binding_is_retained :
    pendingBinding ["let","x","=","q",";","let","(","a",",","b",")","="] =
      .ok (some ["(","a",",","b",")"]) := by cbv

theorem unknown_pending_expression_refuses :
    (pendingBinding ["unknown","("] matches .error _) = true := by decide +kernel

end QleisliKernel.Tests.QuantumBody
