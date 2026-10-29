import QleisliKernel.Semantics.RawOwnerFlow

/-! Exact small logical-owner transport controls. Operator/code-space validity
is independently checked by the enclosing Raw/sector gates, not inferred here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RawOwnerFlow
open Semantics Semantics.SourceOwners Semantics.Raw

private def selector : Owner := ⟨0,[.unit]⟩
private def target : Owner := ⟨1,[.unit]⟩
private def unitProgram (operations : List Op) (outputs : List Nat) : Program :=
  ⟨[⟨10,[],0⟩,⟨11,[],0⟩],operations,outputs,.unitary⟩
private def joined : List Op := [.join 10 11 12,.applyUnitary 12 13 [],.split 13 14 15 0]
private def result (program : Program) := Semantics.RawOwnerFlow.run [selector,target] program

theorem direct_distinct_empty_owners :
    result (unitProgram [] [10,11]) = some [selector,target] := by decide +kernel

theorem direct_reorder_is_retained :
    result (unitProgram [] [11,10]) = some [target,selector] := by decide +kernel

theorem joined_unitary_split_preserves_both_roles :
    result (unitProgram joined [14,15]) = some [selector,target] := by decide +kernel

theorem reversed_zero_width_outputs_do_not_become_canonical :
    (result (unitProgram joined [15,14]) == some [selector,target]) = false := by decide +kernel

theorem reversed_output_role_order_is_exact :
    result (unitProgram joined [15,14]) = some [target,selector] := by decide +kernel

theorem reversed_join_is_not_erased_by_zero_width :
    result (unitProgram [.join 11 10 12,.split 12 14 15 0] [14,15]) = some [target,selector] := by decide +kernel

theorem two_structural_round_trips_keep_role_order :
    result (unitProgram (joined ++ [.join 14 15 16,.split 16 17 18 0]) [17,18]) =
      some [selector,target] := by decide +kernel

theorem different_raw_token_numbers_do_not_change_source_roles :
    Semantics.RawOwnerFlow.run [selector,target]
      ⟨[⟨100,[],0⟩,⟨201,[],0⟩],[.join 100 201 9,.split 9 7 8 0],[7,8],.unitary⟩ =
      some [selector,target] := by decide +kernel

theorem duplicate_return_refuses : result (unitProgram joined [14,14]) = none := by decide +kernel
theorem omitted_empty_owner_refuses : result (unitProgram joined [14]) = none := by decide +kernel
theorem repeated_join_operand_refuses :
    result (unitProgram [.join 10 10 12] [12,11]) = none := by decide +kernel
theorem live_output_overwrite_refuses :
    result (unitProgram [.applyUnitary 10 11 []] [11]) = none := by decide +kernel

theorem original_empty_owner_cannot_be_finished_and_replaced :
    result (unitProgram [.unpackUnit 10,.packUnit 12] [12,11]) = none := by decide +kernel

theorem source_quantum_product_is_an_atomic_role :
    Semantics.RawOwnerFlow.run [⟨0,[.tuple 2,.unit,.unit]⟩,target]
      (unitProgram [.split 10 12 13 0,.join 12 13 14] [14,11]) = none := by decide +kernel

theorem split_uses_the_actual_join_child_width :
    Semantics.RawOwnerFlow.run [⟨0,[.bit]⟩,target]
      ⟨[⟨10,[7],1⟩,⟨11,[],0⟩],[.join 10 11 12,.split 12 14 15 0],[14,15],.unitary⟩ = none := by decide +kernel

theorem cnot_returns_each_original_role :
    Semantics.RawOwnerFlow.run [⟨0,[.bit]⟩,⟨1,[.bit]⟩]
      ⟨[⟨10,[7],1⟩,⟨11,[8],1⟩],[.cnot 10 11 12 13],[12,13],.unitary⟩ =
      some [⟨0,[.bit]⟩,⟨1,[.bit]⟩] := by decide +kernel

theorem quantum_if_returns_each_original_role :
    Semantics.RawOwnerFlow.run [⟨0,[.bit]⟩,target]
      ⟨[⟨10,[7],1⟩,⟨11,[],0⟩],[.quantumIf 10 11 12 13 [] []],[12,13],.unitary⟩ =
      some [⟨0,[.bit]⟩,target] := by decide +kernel

theorem protected_targets_are_moved_simultaneously :
    Semantics.RawOwnerFlow.run [⟨0,[.bit]⟩,⟨1,[.bit]⟩]
      ⟨[⟨10,[7],1⟩,⟨11,[8],1⟩],[.computeUseUncompute 10 12 [⟨11,13⟩] [] [] []],
        [12,13],.unitary⟩ = some [⟨0,[.bit]⟩,⟨1,[.bit]⟩] := by decide +kernel

end QleisliKernel.Tests.RawOwnerFlow
