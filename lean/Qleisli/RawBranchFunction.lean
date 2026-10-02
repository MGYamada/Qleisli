import QleisliKernel.Raw.BranchFunction
import Qleisli.RawInstrumentDenotation
import Qleisli.Semantics.ObservingFunction

/-! Actual retained classical-branch functions refine independent full original
body semantics. A checked prefix is reconstructed from no trusted receipts.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw.BranchFunction
open QleisliKernel.Semantics.ObservingFunction QleisliKernel.Semantics.Observation
open QleisliKernel.Semantics.Exact QleisliKernel.Raw.BranchFunction QleisliKernel.Finite
open Qleisli.Semantics.ObservingFunction

theorem reconstruct_denotes (dependencies : List QleisliKernel.Semantics.Finite.Dependency)
    (program : Program) (closed : program.classicalInputs = []) (actual : Matrix)
    (work left : Nat) (ok : (reconstruct dependencies program).run work = (.ok actual,left)) :
    BodyMeaning dependencies program actual := by
  rcases reconstruct_execution _ _ _ _ _ ok with ⟨checked,initial,history,a,b,c,d,hv,hi,he,hm,hh⟩
  have original := (QleisliKernel.Raw.Observation.verify_conditions _ _ _ _ _ hv).2.2
  have identity := Qleisli.Exact.identity_meaning _ _ hi
  have run := Instrument.Denotation.run_reference _ _ _ _ _ _ _ he
  rw [List.map_singleton] at run
  refine ⟨history.values,checked.prepared,initial,original,?_,?_⟩
  · exact ⟨identity.2.1,identity.2.2.1,fun row col hr hc => identity.2.2.2 row col
      (identity.2.1 ▸ hr) (identity.2.2.1 ▸ hc)⟩
  · simpa [Instrument.Denotation.reference,closed,hm,hh] using run

theorem checkEntry_semantics (before : List Receipt) (input : Input) (binding : Binding)
    (receipt : Receipt) (work left : Nat)
    (ok : (checkEntry before input binding).run work = (.ok receipt,left)) :
    receipt.input = input ∧ input = binding ∧ EntryMeaning before receipt := by
  rcases checkEntry_conditions _ _ _ _ _ _ ok with
    ⟨bindingEq,inputEq,hp,hs,_,_,height,count,a,b,c,d,e,f,hi,hsp,hu⟩
  have ci : input.implementation.classicalInputs = [] := by
    simp only [preflight,Bool.and_eq_true,List.isEmpty_iff] at hp
    exact hp.1.1.1.2
  have cs : input.specification.classicalInputs = [] := by
    simp only [preflight,Bool.and_eq_true,List.isEmpty_iff] at hs
    exact hs.1.1.1.2
  have impl := reconstruct_denotes _ _ ci _ _ _ hi
  have spec := reconstruct_denotes _ _ cs _ _ _ hsp
  have unitary := Finite.wholeSpace_unitary _ _ _ hu
  refine ⟨inputEq,bindingEq,?_⟩
  unfold EntryMeaning
  rw [inputEq]
  exact ⟨impl,spec,unitary.1,unitary.2,height,count⟩

theorem chain_semantics {before final : List Receipt} {pairs : List (Input × Binding)}
    (chain : CheckedChain before pairs final) (initial : GraphMeaning before) : GraphMeaning final := by
  induction chain with
  | nil => exact initial
  | cons before input binding rest receipt final work left checked remaining ih =>
    exact ih (.snoc _ _ initial (checkEntry_semantics _ _ _ _ _ _ checked).2.2)

theorem checkAll_semantics (inputs : List Input) (bindings : List Binding) (receipts : List Receipt)
    (work left : Nat) (ok : (checkAll inputs bindings).run work = (.ok receipts,left)) :
    GraphMeaning receipts ∧ receipts.map (·.input) = inputs ∧ inputs = bindings := by
  rcases checkAll_fresh _ _ _ _ _ ok with ⟨lengthEq,chain⟩
  have leftZip : (inputs.zip bindings).map Prod.fst = inputs := List.map_fst_zip (Nat.le_of_eq lengthEq)
  have rightZip : (inputs.zip bindings).map Prod.snd = bindings := List.map_snd_zip (Nat.le_of_eq lengthEq.symm)
  exact ⟨chain_semantics chain .nil,by simpa [leftZip] using chain.inputs,
    leftZip.symm.trans (chain.bindings.trans rightZip)⟩

end Qleisli.Raw.BranchFunction
