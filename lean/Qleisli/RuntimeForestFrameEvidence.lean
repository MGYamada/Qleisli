import QleisliKernel.Qirf.RuntimeForestFactorization

/-! Mathematical sparse-frame existence from the original per-owner receipts.
The independent forest parser uses its own exact tensor fold. Reference layouts
occur only in erased existence proofs; no joined code is evaluated here. This
does not claim a successful readFrame invocation or sufficient remaining work.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeForestFrameEvidence
open QleisliKernel QleisliKernel.Qirf
open Semantics.FiniteCarrier
open RuntimeForestCode

/-- Each complete original owner tree pushes its actual layout over the same
continuation. No owner can borrow a neighbouring owner's prefix nodes. -/
theorem owner_stack {bindings : RuntimeOwnerMap.Map} (owners : OwnerCodes bindings) :
    ∃ layouts : List Layout, layouts.length = bindings.length ∧
      ∀ suffix, (bindings.flatMap (fun binding => binding.owner.basis)).foldr
        layoutStep (some suffix) = some (layouts ++ suffix) := by
  induction owners with
  | nil => exact ⟨[],rfl,fun _ => rfl⟩
  | @cons binding bindings first rest ih =>
    obtain ⟨layouts,count,original⟩ := ih
    refine ⟨first.layout :: layouts,congrArg Nat.succ count,?_⟩
    intro suffix
    simp only [List.flatMap_cons,List.foldr_append]
    rw [original suffix]
    exact layout_continuation binding.owner.basis first.layout first.reference.1 (layouts ++ suffix)

/-- The actual forest has a complete independent interpretation. For three or
more owners the result is exactly the parser's left tensor fold, without any
reassociation or equality supplied by the caller. Every Unit remains an owner. -/
theorem forest_layout {bindings : RuntimeOwnerMap.Map} (owners : OwnerCodes bindings) :
    ∃ layout, Semantics.FiniteCarrier.layout (forestBasis bindings) = some layout := by
  cases owners with
  | nil => exact ⟨Semantics.FiniteCarrier.singleton,rfl⟩
  | @cons firstBinding firstBindings first rest =>
    cases rest with
    | nil =>
      refine ⟨first.layout,?_⟩
      simpa only [forestBasis,carrierOwners,List.map_cons,List.map_nil,
        Semantics.CarrierInterface.forest] using first.reference.1
    | @cons secondBinding secondBindings second tail =>
      cases tail with
      | nil =>
        refine ⟨tensor first.layout second.layout,?_⟩
        simpa only [forestBasis,carrierOwners,List.map_cons,List.map_nil,
          Semantics.CarrierInterface.forest] using
          layout_pair_reference firstBinding.owner.basis secondBinding.owner.basis
            first.layout second.layout first.reference.1 second.reference.1
      | @cons thirdBinding bindings third rest =>
        let all : OwnerCodes (firstBinding :: secondBinding :: thirdBinding :: bindings) :=
          .cons first (.cons second (.cons third rest))
        obtain ⟨layouts,count,original⟩ := owner_stack all
        have shape : forestBasis (firstBinding :: secondBinding :: thirdBinding :: bindings) =
            .tuple (firstBinding :: secondBinding :: thirdBinding :: bindings).length ::
              (firstBinding :: secondBinding :: thirdBinding :: bindings).flatMap
                (fun binding => binding.owner.basis) := by
          simp only [forestBasis,carrierOwners,List.map_cons,Semantics.CarrierInterface.forest,
            List.length_cons,List.length_map,List.flatMap_map,List.flatMap_cons]
        have stack : ((firstBinding :: secondBinding :: thirdBinding :: bindings).flatMap
            (fun binding => binding.owner.basis)).foldr layoutStep (some []) = some layouts := by
          simpa only [List.append_nil] using original []
        have root : layoutStep (.tuple (firstBinding :: secondBinding :: thirdBinding :: bindings).length)
            (some layouts) = some [layouts.foldl tensor Semantics.FiniteCarrier.singleton] := by
          rw [← count]
          simp only [layoutStep,children,bind,Option.bind,Nat.lt_irrefl,if_false,
            List.take_length,List.drop_length]
        refine ⟨layouts.foldl tensor Semantics.FiniteCarrier.singleton,?_⟩
        simp only [Semantics.FiniteCarrier.layout,shape,List.foldr_cons,stack,root,
          bind,Option.bind,pure]

/-- Original per-owner evidence supplies a mathematical Frame for this same
complete checked map. Nonempty performs no runtime extraction from Prop; no
new reader invocation or public work-counter sufficiency follows. -/
theorem of_ownerCodes {roles state} (checked : RuntimeOwnerMap.Checked roles state)
    (available : Nonempty (OwnerCodes checked.bindings)) : Nonempty (Frame checked) := by
  obtain ⟨owners⟩ := available
  obtain ⟨layout,reference⟩ := forest_layout owners
  obtain ⟨code,original,_same⟩ := sparseLayout_complete (forestBasis checked.bindings) layout reference
  exact ⟨⟨owners,code,original⟩⟩

#print axioms owner_stack
#print axioms forest_layout
#print axioms of_ownerCodes

end Qleisli.RuntimeForestFrameEvidence
