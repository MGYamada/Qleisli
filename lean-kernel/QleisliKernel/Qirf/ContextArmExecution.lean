import QleisliKernel.Qirf.ContextSector
import QleisliKernel.Qirf.SourceArmExecution

/-! Original named-arm entries execute under the same checked context root.
The ordered relation retains every original arm binding and its actual receipt;
it does not assert preservation of the original source body or native runtime.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.ContextSector
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite

/-- Every original arm of this selection retains its actual entry and executes
both original IR bodies with the final root's dependencies. No whole-vector
equality, fresh replacement body or producer-selected history is assumed. -/
theorem Local.arm_executions {artifact owner name requests order positions}
    {headers : Headers artifact owner name requests}
    {body : Body order headers positions} (site : Local body) :
    QleisliKernel.Exact.ListRel (fun bound result =>
      result.bound = bound ∧
      artifact.programs[bound.binding.entry.implementation]? =
        some result.checked.receipt.input.implementation ∧
      (bound.binding.function.provider.moduleName,bound.signature.original.source) ∈
        result.checked.receipt.input.identity.sources ∧
      ReceiptTransport.Executes body.root.val.dependencies result.checked.receipt.input.implementation
        result.checked.receipt.meaning ∧
      ReceiptTransport.Executes body.root.val.dependencies result.checked.receipt.input.specification
        result.checked.receipt.meaning)
      site.header.bindings.val site.checked.prepared.entries.val := by
  obtain ⟨before,after,ran⟩ := site.checked.prepared.entries.property
  apply FiniteRestriction.mapM_relation _ _ _ _ _ before after ran
  intro bound result work left ok
  have same := SourceSector.readEntry_bound artifact body.root.val.receipts bound
    (SelectionContract.rootFresh body.root) result work left ok
  cases result with
  | mk actual checked =>
    dsimp only at same ⊢
    subst actual
    exact ⟨rfl,ReceiptTransport.realized_execution body.root bound checked⟩

end QleisliKernel.Qirf.ContextSector
