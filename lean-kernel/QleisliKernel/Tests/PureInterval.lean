import QleisliKernel.Qirf.PureInterval

/-! Small literal-interval checks with independent whole-root counterexamples.
No source occurrence is bound here and no maximum-size case is generated.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.PureInterval
open Semantics Semantics.Raw Qirf.PureInterval

private def first : Port := ⟨0,[0],1⟩
private def second : Port := ⟨1,[1],1⟩
private def empty : Port := ⟨2,[],0⟩
private def bitRoles : List SourceOwners.Owner := [⟨0,[.bit]⟩,⟨1,[.bit]⟩]
private def emptyRoles : List SourceOwners.Owner := [⟨0,[.unit]⟩,⟨1,[.unit]⟩]

private def surrounding : Observation.Program :=
  ⟨[first,second,empty],[],[.pure (.gate .h 1 3),.pure (.cnot 0 3 4 5),
    .pure (.gate .h 5 6)],[4,6,2],[],.unitary⟩
private def observeAfter : Observation.Program :=
  {surrounding with
    operations := [.pure (.gate .h 1 3),.pure (.cnot 0 3 4 5),.measure 5 0],
    outputs := [4,2],classicalOutputs := [0],effect := .observe}
private def observeBefore : Observation.Program :=
  ⟨[first,second,empty,⟨3,[2],1⟩],[],[.measure 3 0,.pure (.cnot 0 1 4 5)],
    [4,5,2],[0],.observe⟩
private def zeroOwners : Observation.Program :=
  ⟨[⟨0,[],0⟩,⟨1,[],0⟩,empty],[],[.pure (.join 0 1 3),.pure (.split 3 4 5 0)],
    [4,5,2],[],.unitary⟩
private def reused : Observation.Program :=
  {surrounding with
    operations := [.pure (.gate .h 1 3),.pure (.cnot 0 3 1 5),.pure (.gate .h 5 6)],
    outputs := [1,6,2]}

private def accepted (program : Observation.Program) (start count : Nat)
    (inputs outputs : List Nat) (roles : List SourceOwners.Owner := bitRoles) : Bool :=
  match (check [] program start count inputs outputs roles).run 100000 with
  | (.ok _,_) => true | _ => false

private def isolated (inputs : List Port) (operations : List Op) (outputs : List Nat) : Bool :=
  match (QleisliKernel.Raw.Pure.verify [] ⟨inputs,operations,outputs,.unitary⟩).run 100000 with
  | (.ok _,_) => true | _ => false

theorem prefix_suffix_and_empty_spectator : accepted surrounding 1 1 [0,3] [4,5] = true := by decide +kernel
theorem observe_suffix_retains_root : accepted observeAfter 1 1 [0,3] [4,5] = true := by decide +kernel
theorem observe_prefix_retains_root : accepted observeBefore 1 1 [0,1] [4,5] = true := by decide +kernel
theorem false_pure_root_refuses :
    accepted {observeAfter with effect := .unitary} 1 1 [0,3] [4,5] = false := by decide +kernel
theorem observing_interval_refuses : accepted observeAfter 1 2 [0,3] [4,5] = false := by decide +kernel
theorem consumed_input_refuses : accepted surrounding 1 1 [0,1] [4,5] = false := by decide +kernel
theorem wrong_return_roles_refuse : accepted surrounding 1 1 [0,3] [5,4] = false := by decide +kernel
theorem missing_empty_owner_refuses :
    accepted {surrounding with outputs := [4,6]} 1 1 [0,3] [4,5] = false := by decide +kernel
theorem incomplete_range_refuses : accepted surrounding 1 4 [0,3] [4,5] = false := by decide +kernel
theorem zero_width_roles_remain_distinct : accepted zeroOwners 0 2 [0,1] [4,5] emptyRoles = true := by decide +kernel
theorem swapped_zero_width_roles_refuse : accepted zeroOwners 0 2 [0,1] [5,4] emptyRoles = false := by decide +kernel
theorem global_consumed_token_reuse_refuses : accepted reused 1 1 [0,3] [1,5] = false := by decide +kernel

-- An isolated valid body does not establish either global freshness or source roles.
theorem isolated_reuse_is_insufficient :
    isolated [first,⟨3,[1],1⟩] [.cnot 0 3 1 5] [1,5] = true := by decide +kernel
theorem isolated_zero_swap_is_insufficient :
    isolated [⟨0,[],0⟩,⟨1,[],0⟩] [.join 0 1 3,.split 3 4 5 0] [5,4] = true := by decide +kernel

-- This remains valid IR; it is not the qmatch operation in the source study.
-- The enclosing source-occurrence gate must supply the missing association.
theorem shifted_interval_does_not_establish_source_binding :
    accepted surrounding 0 1 [0,1] [0,3] = true := by decide +kernel

end QleisliKernel.Tests.PureInterval
