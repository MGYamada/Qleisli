import QleisliKernel.RuntimeStorage

/-! Small kernel reductions of full storage shape and original owner roles.
No source execution or code-space preservation follows from these tests.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStorage
open Semantics.RuntimeStorage Semantics.RuntimeType

private def accepted (expected : Tree) (stored : Value) : Bool :=
  ((QleisliKernel.RuntimeStorage.read expected stored).run 100000).1.isOk

private def q : Semantics.CarrierInterface.Owner := ⟨⟨0,[],0⟩,[.unit]⟩

theorem ordinary_unit_is_retained : accepted (ordinary [.unit]) [.ordinary [.unit] .unit] = true :=
  by decide +kernel
theorem quantum_unit_is_retained : accepted (owner [.unit]) [.quantum q] = true := by decide +kernel
theorem empty_storage_is_not_unit : accepted (ordinary [.unit]) [] = false := by decide +kernel
theorem ordinary_unit_is_not_quantum : accepted (owner [.unit]) [.ordinary [.unit] .unit] = false :=
  by decide +kernel
theorem quantum_unit_is_not_ordinary : accepted (ordinary [.unit]) [.quantum q] = false :=
  by decide +kernel
theorem mixed_tuple_keeps_shape :
    accepted (tuple 2 [ordinary [.unit],owner [.unit]])
      [.tuple 2,.ordinary [.unit] .unit,.quantum q] = true := by decide +kernel
theorem swapping_ordinary_and_owner_refuses :
    accepted (tuple 2 [ordinary [.unit],owner [.unit]])
      [.tuple 2,.quantum q,.ordinary [.unit] .unit] = false := by decide +kernel
theorem incomplete_storage_cannot_borrow_a_neighbor :
    accepted (tuple 2 [ordinary [.unit],ordinary [.unit]])
      [.ordinary [.pair] .unit,.ordinary [.unit] .unit,.ordinary [.unit] .unit] = false := by decide +kernel
theorem owner_wires_match_logical_basis_width :
    accepted (owner [.bit]) [.quantum ⟨⟨0,[],0⟩,[.bit]⟩] = false := by decide +kernel
theorem bits_zero_is_not_unit : accepted (owner [.unit])
    [.quantum ⟨q.port,[.bits 0]⟩] = false := by decide +kernel
theorem tuple_of_owners_is_not_one_owner :
    accepted (owner [.pair,.unit,.unit]) [.tuple 2,.quantum q,.quantum {q with port.token := 1}] = false :=
  by decide +kernel
theorem no_budget_refuses :
    ((QleisliKernel.RuntimeStorage.read (owner [.unit]) [.quantum q]).run 0).1.isOk = false := by decide +kernel

end QleisliKernel.Tests.RuntimeStorage
