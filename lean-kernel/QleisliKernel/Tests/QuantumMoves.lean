import QleisliKernel.SourceTypes.QuantumMoves

/-! Small structural source ownership reductions, separate from full source
typing, native execution and the retained runtime operand counterexamples.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.QuantumMoves
open Semantics.SourceOwners SourceTypes.QuantumMoves

def selector : Owner := ⟨0,[.bit]⟩
def target : Owner := ⟨1,[.unit]⟩
def frame : Environment := [⟨"s",[.owner selector]⟩,⟨"q",[.owner target]⟩]

theorem zero_width_move :
    ((take "q" frame).toOption == some ([.owner target],[⟨"s",[.owner selector]⟩])) = true := by decide +kernel

theorem repeated_owner_refuses :
    (eval ["(","s",",","s",")"] frame matches .error _) = true := by decide +kernel

theorem undefined_owner_refuses :
    (eval ["unknown"] frame matches .error _) = true := by decide +kernel

theorem ordinary_tuple_groups_separate_owners :
    ((eval ["(","s",",","q",")"] frame).toOption ==
      some ([.tuple 2,.owner selector,.owner target],[])) = true := by decide +kernel

theorem grouped_expression_preserves_owner_shape :
    ((parse 65 ["(","q",")"]).toOption == some [.name "q"]) = true := by decide +kernel

theorem singleton_tuple_preserves_its_shape :
    ((parse 65 ["(","q",",",")"]).toOption == some [.tuple 1,.name "q"]) = true := by decide +kernel

theorem quantum_product_owner_is_atomic :
    (bind ["(","a",",","b",")"] [.owner ⟨2,[.tuple 2,.bit,.unit]⟩] [] matches .error _) = true := by decide +kernel

theorem wildcard_cannot_discard_zero_width_owner :
    (bind ["_"] [.owner target] [] matches .error _) = true := by decide +kernel

theorem consumed_name_refuses :
    (replay 129 frame ["let","p","=","q",";","let","a","=","q",";"] matches .error _) = true := by decide +kernel

theorem live_quantum_shadow_refuses :
    (replay 129 frame ["let","s","=","q",";"] matches .error _) = true := by decide +kernel

theorem simultaneous_tuple_rebinding :
    ((replay 129 frame ["let","(","a",",","b",")","=","(","s",",","q",")",";"]).toOption ==
      some [⟨"b",[.owner target]⟩,⟨"a",[.owner selector]⟩]) = true := by decide +kernel

theorem consumed_name_can_be_rebound :
    ((replay 129 frame ["let","q","=","q",";"]).toOption ==
      some [⟨"q",[.owner target]⟩,⟨"s",[.owner selector]⟩]) = true := by decide +kernel

end QleisliKernel.Tests.QuantumMoves
