import QleisliKernel.Raw.Function
import Qleisli.RawDenotation
import Qleisli.RawProtectedEvaluation
import Qleisli.Semantics.RawFunction

/-! Full retained function binding and fresh dependency-graph semantics.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.Function
open scoped Matrix
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open QleisliKernel.Semantics.Function QleisliKernel.Raw QleisliKernel.Raw.Function
open QleisliKernel.Finite Qleisli.Semantics.Raw

theorem checkEntry_semantics (before : List Receipt) (input : Input) (binding : Binding)
    (receipt : Receipt) (work left : Nat)
    (ok : (checkEntry before input binding).run work = (.ok receipt,left)) :
    receipt.input = input ∧ input = binding ∧ EntryMeaning before receipt := by
  rcases checkEntry_conditions _ _ _ _ _ _ ok with
    ⟨bindingEq,_,_,_,inputEq,_,height,implementation,specification,a,b,c,d,e,f,g,h,i,j,hi,hs,he,hse,ha,hsa,hu⟩
  have impl := ProtectedEvaluation.reconstruct_denotes _ _ _ _ _ ha
  have spec := ProtectedEvaluation.reconstruct_denotes _ _ _ _ _ hsa
  have unitary := Finite.wholeSpace_unitary _ _ _ hu
  have actualCount := boundedExpansion_reference _ _ _ _ _ he
  have specCount := boundedExpansion_reference _ _ _ _ _ hse
  refine ⟨inputEq,bindingEq,?_⟩
  unfold EntryMeaning
  rw [inputEq]
  exact ⟨impl,spec,unitary.1,unitary.2,height,actualCount.2,
    implementation.reference,specification.reference,d,prepare_reference _ _ _ hi,prepare_reference _ _ _ hs,
    actualCount.1,specCount.1,specCount.2⟩

theorem chain_semantics (before final : List Receipt) (pairs : List (Input × Binding))
    (chain : CheckedChain before pairs final) (initial : GraphMeaning before) : GraphMeaning final := by
  induction chain with
  | nil => exact initial
  | cons before input binding rest receipt final work left checked remaining ih =>
    exact ih (.snoc _ _ initial (checkEntry_semantics _ _ _ _ _ _ checked).2.2)

theorem checkAll_semantics (inputs : List Input) (bindings : List Binding) (receipts : List Receipt)
    (work left : Nat) (ok : (checkAll inputs bindings).run work = (.ok receipts,left)) :
    GraphMeaning receipts ∧ receipts.map (·.input) = inputs ∧ inputs = bindings := by
  rcases checkAll_fresh _ _ _ _ _ ok with ⟨lengthEq,chain⟩
  have leftZip : (inputs.zip bindings).map Prod.fst = inputs := by
    exact List.map_fst_zip (Nat.le_of_eq lengthEq)
  have rightZip : (inputs.zip bindings).map Prod.snd = bindings := by
    exact List.map_snd_zip (Nat.le_of_eq lengthEq.symm)
  exact ⟨chain_semantics _ _ _ chain .nil,by simpa [leftZip] using chain.inputs,
    leftZip.symm.trans (chain.bindings.trans rightZip)⟩

theorem inspect_semantics (inputs : List Input) (bindings : List Binding) (program : Program)
    (required actual : Matrix) (work left : Nat)
    (ok : (inspect inputs bindings program required).run work = (.ok actual,left)) :
    actual = required ∧ ∃ receipts,
      GraphMeaning receipts ∧ receipts.map (·.input) = inputs ∧ inputs = bindings ∧
      ProgramMeaning (receipts.map Receipt.dependency) program actual := by
  rcases inspect_fresh _ _ _ _ _ _ _ ok with ⟨same,receipts,a,b,c,d,hc,hp⟩
  rcases checkAll_semantics _ _ _ _ _ hc with ⟨graph,identities,bindings⟩
  exact ⟨same,receipts,graph,identities,bindings,ProtectedEvaluation.reconstruct_denotes _ _ _ _ _ hp⟩

end Qleisli.Raw.Function
