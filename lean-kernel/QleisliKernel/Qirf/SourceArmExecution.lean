import QleisliKernel.Qirf.SourceArmSnapshot
import QleisliKernel.Raw.ObservationExecution

/-! The same freshly checked root supplies the original arm IR and its exact
execution under the final dependency snapshot. Original source-body meaning
and native runtime correspondence remain separate obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.ReceiptTransport
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.ObservingFunction
open QleisliKernel.Qirf.PureInterval

def Executes (dependencies : List Semantics.Finite.Dependency)
    (program : Semantics.Observation.Program) (meaning : Semantics.Exact.Matrix) : Prop :=
  ∃ prepared initial history work left,
    Semantics.Observation.read program = some prepared ∧
    Exact.Matrix.identity (2^prepared.inputBits) = .ok initial ∧
    (Raw.Instrument.runEvents dependencies 65 prepared.events ⟨[],[],initial⟩).run work = (.ok [history],left) ∧
    history.operator = meaning ∧ history.hidden = []

/-- Source identity and original IR lookup belong to the same realized entry.
Both implementation and specification use the final root's actual dependencies;
no independent root, matrix cache or producer-selected history can substitute. -/
theorem realized_execution {artifact order extra roots owner selector target profile}
    (root : Witness (Validity.checkRootFromRoots artifact order extra roots profile))
    (bound : SourceArm.Bound artifact owner selector target)
    (checked : SourceArm.Realized artifact root.val.receipts bound) :
    artifact.programs[bound.binding.entry.implementation]? = some checked.receipt.input.implementation ∧
    (bound.binding.function.provider.moduleName,bound.signature.original.source) ∈
      checked.receipt.input.identity.sources ∧
    Executes root.val.dependencies checked.receipt.input.implementation checked.receipt.meaning ∧
    Executes root.val.dependencies checked.receipt.input.specification checked.receipt.meaning := by
  obtain ⟨previous,a,b,c,d,decoded,verified,readyImpl,readySpec,extension,agreement⟩ :=
    realized_snapshot root bound checked
  obtain ⟨_,_,_,_,_,_,_,_,p,q,r,s,t,u,impl,spec,whole⟩ :=
    Raw.BranchFunction.checkEntry_conditions _ _ _ _ _ _ verified
  refine ⟨checked.inputBinding.2.2,checked.sourceRow,?_,?_⟩
  · exact QleisliKernel.Raw.ObservationAgreement.reconstructed_execution
      ((before previous).map Receipt.dependency) root.val.dependencies
      checked.receipt.input.implementation checked.receipt.meaning p q impl
      (fun index member => agreement index (List.mem_append.mpr (Or.inl member)))
  · exact QleisliKernel.Raw.ObservationAgreement.reconstructed_execution
      ((before previous).map Receipt.dependency) root.val.dependencies
      checked.receipt.input.specification checked.receipt.meaning r s spec
      (fun index member => agreement index (List.mem_append.mpr (Or.inr member)))

end QleisliKernel.Qirf.ReceiptTransport
