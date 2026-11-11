import Qleisli.RuntimePureProviderLogicalAction
import QleisliKernel.Qirf.RuntimeOperationTree

/-! Recover the provider value consumed at the actual operation-tree
occurrence, without searching by equal description index.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeProviderOccurrenceAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite QleisliKernel.SourceTypes
open Semantics.Exact (Matrix)

private theorem provider_value {sources} (metadata : StaticOperation.Result sources)
    (moduleName declarationName : String) (bases : List (String × Semantics.FiniteCarrier.Basis))
    (naturals operations : List (String × Nat)) (children providers : List Matrix)
    (value : Matrix) (used work left : Nat)
    (read : (OperationIRMeaning.readNode metadata (.provider moduleName declarationName bases naturals operations)
      children providers 0).run work = (.ok (value,used),left)) : providers[0]? = some value := by
  unfold OperationIRMeaning.readNode at read
  obtain ⟨⟨matrix,count⟩,middle,calculated,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,returned⟩ := bind_success _ _ _ _ _ rest
  have same : value = matrix := congrArg Prod.fst (pure_success _ _ _ _ returned).1
  change (do
    let provider ← lift (readOption providers[0]?)
    pure (provider,1) : WorkM (Matrix × Nat)).run work = (.ok (matrix,count),middle) at calculated
  obtain ⟨provider,_,readProvider,paired⟩ := bind_success _ _ _ _ _ calculated
  have entry := (lift_success _ _ _ _ readProvider).1
  have found : providers[0]? = some provider := by
    cases lookup : providers[0]? with
    | none => simp [readOption,lookup] at entry
    | some original => simpa [readOption,lookup] using congrArg some entry
  have selected : matrix = provider := congrArg Prod.fst (pure_success _ _ _ _ paired).1
  rw [same,selected]
  exact found

/-- A provider leaf must consume this exact occurrence's native provider
action. The source-evaluation theorem can then be instantiated on its body. -/
theorem provider_node {artifact catalogue context description graph order occurrence root demand before}
    (step : @RuntimeOperationTree.Step artifact catalogue context description graph order occurrence root demand before)
    (moduleName declarationName : String) (bases : List (String × Semantics.FiniteCarrier.Basis))
    (naturals operations : List (String × Nat))
    (written : step.node = .provider moduleName declarationName bases naturals operations) :
    ∃ (provider : RuntimePreparedOperation.Provider artifact graph occurrence.index) (original : occurrence.provider = some provider)
      (checked : RuntimeProviderAction.Checked provider.header root demand)
      (consumed : RuntimeInterval.Computed (RuntimeProviderAction.read provider.header root demand) checked),
      step.provider = .present provider original checked consumed ∧ step.value = checked.action := by
  obtain ⟨work,left,computed⟩ := step.calculated
  have lookup : step.provider.actions[0]? = some step.value :=
    provider_value occurrence.result moduleName declarationName bases naturals operations _ _ _ _ _ _
      (by simpa only [← written] using computed)
  cases receipt : step.provider with
  | absent _ => simp [receipt,RuntimeOperationTree.Provider.actions] at lookup
  | present provider original checked consumed =>
    have same : checked.action = step.value := by
      simpa only [receipt,RuntimeOperationTree.Provider.actions,List.getElem?_cons_zero,Option.some.injEq] using lookup
    exact ⟨provider,original,checked,consumed,rfl,same.symm⟩

#print axioms provider_node
end Qleisli.RuntimeProviderOccurrenceAction
