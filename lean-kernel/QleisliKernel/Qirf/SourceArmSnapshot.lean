import QleisliKernel.Qirf.ReceiptEntryPrefix
import QleisliKernel.Qirf.SourceArm
import QleisliKernel.Qirf.SelectionContract

/-! Bind an actual source-arm receipt to its historical snapshot in the same
successful root computation. Only original referenced slots must agree.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.ReceiptTransport
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.ObservingFunction
open QleisliKernel.Qirf.PureInterval

theorem root_receipts {artifact order extra roots} (root : Validity.Root) (work left : Nat)
    (ok : (Validity.checkRootFromRoots artifact order extra roots).run work = (.ok root,left)) :
    ∃ after, (checkGraphReceiptsFromRoots artifact order extra roots).run work =
      (.ok root.receipts,after) := by
  obtain ⟨receipts,a,hg,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,b,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨program,c,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,d,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst root
  exact ⟨a,hg⟩

/-- The retained entry and root share their actual computation; a receipt from
another graph or an arbitrary final vector cannot provide the premise. -/
theorem realized_snapshot {artifact order extra roots owner selector target}
    (root : Witness (Validity.checkRootFromRoots artifact order extra roots))
    (bound : SourceArm.Bound artifact owner selector target)
    (checked : SourceArm.Realized artifact root.val.receipts bound) :
    ∃ previous a b c d,
      (input artifact bound.binding.entry).run a = (.ok checked.receipt.input,b) ∧
      (Raw.BranchFunction.checkEntry (before previous)
        checked.receipt.input checked.receipt.input).run c = (.ok checked.receipt,d) ∧
      ready previous checked.receipt.input.implementation = true ∧
      ready previous checked.receipt.input.specification = true ∧
      Extends previous root.val.receipts ∧
      ∀ dependency,
        dependency ∈ references 65 checked.receipt.input.implementation.operations ++
          references 65 checked.receipt.input.specification.operations →
        ((before previous).map Receipt.dependency)[dependency]? = root.val.dependencies[dependency]? := by
  obtain ⟨work,left,ran⟩ := root.property
  obtain ⟨after,graph⟩ := root_receipts root.val work left ran
  obtain ⟨entry,actual,previous,a,b,c,d,found,decoded,verified,original,
    impl,spec,extension⟩ := successful_entry_origin graph checked.present
  have same : entry = bound.binding.entry :=
    Option.some.inj (found.symm.trans bound.binding.original)
  subst entry
  rw [← original] at decoded verified impl spec
  refine ⟨previous,a,b,c,d,decoded,verified,impl,spec,extension,?_⟩
  intro dependency member
  have dependencies := (Validity.checkRootFromRoots_postcondition _ _ _ _ _ _ _ ran).dependencyBinding
  rw [dependencies]
  rcases List.mem_append.mp member with implementation | specification
  · exact ready_dependency_agreement extension impl dependency implementation
  · exact ready_dependency_agreement extension spec dependency specification

end QleisliKernel.Qirf.ReceiptTransport
