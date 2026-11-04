import Qleisli.RuntimeOwnerFlowExtension

/-! Leaf provenance through the original logical-owner flow.
Joins preserve complete ordered child trees and splits recover those same
children. This erased predicate tracks original owner identities and widths;
it does not identify physical wires or establish code/action equations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOwnerLeafOrigins
open QleisliKernel.Semantics
open Qleisli.RuntimeOwnerFlowExtension (take_partition)

inductive Supported (allowed : SourceOwners.Owner → Nat → Prop) : RawOwnerFlow.Tree → Prop where
  | leaf {owner bits} (original : allowed owner bits) : Supported allowed (.owner owner bits)
  | pair {first second bits} (left : Supported allowed first) (right : Supported allowed second) :
      Supported allowed (.pair first second bits)

abbrev Supports (allowed : SourceOwners.Owner → Nat → Prop) (frame : RawOwnerFlow.Frame) : Prop :=
  ∀ cell ∈ frame, Supported allowed cell.2

theorem owner_value {allowed owner bits} (original : Supported allowed (.owner owner bits)) :
    allowed owner bits := by
  cases original with
  | leaf value => exact value

private theorem supports_cons {allowed token tree frame}
    (head : Supported allowed tree) (tail : Supports allowed frame) :
    Supports allowed ((token,tree) :: frame) := by
  intro cell member
  rcases List.mem_cons.mp member with same | later
  · subst cell; exact head
  · exact tail cell later

theorem take_supported {allowed token before tree after}
    (original : Supports allowed before)
    (ran : RawOwnerFlow.take token before = some (tree,after)) :
    Supported allowed tree ∧ Supports allowed after := by
  have partition := take_partition ran
  constructor
  · exact original (token,tree) (partition.mem_iff.mpr List.mem_cons_self)
  · intro cell member
    exact original cell (partition.mem_iff.mpr (List.mem_cons_of_mem _ member))

private theorem put_supported {allowed token tree before after}
    (head : Supported allowed tree) (original : Supports allowed before)
    (ran : RawOwnerFlow.put token tree before = some after) : Supports allowed after := by
  unfold RawOwnerFlow.put at ran
  split at ran
  · cases ran
  · have same : after = (token,tree) :: before := (Option.some.inj ran).symm
    rw [same]
    exact supports_cons head original

private theorem move_supported {allowed input output before after}
    (original : Supports allowed before)
    (ran : RawOwnerFlow.move input output before = some after) : Supports allowed after := by
  unfold RawOwnerFlow.move at ran
  obtain ⟨⟨tree,remaining⟩,taken,inserted⟩ := Option.bind_eq_some_iff.mp ran
  have facts := take_supported original taken
  exact put_supported facts.1 facts.2 inserted

private theorem takeMany_supported (targets : List Raw.Target)
    {allowed values before result after}
    (valuesOriginal : Supports allowed values) (original : Supports allowed before)
    (ran : targets.foldlM (fun (values,current) target => do
      let (tree,remaining) ← RawOwnerFlow.take target.input current
      pure ((target.output,tree) :: values,remaining)) (values,before) = some (result,after)) :
    Supports allowed result ∧ Supports allowed after := by
  induction targets generalizing values before result after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    exact ⟨valuesOriginal,original⟩
  | cons target targets ih =>
    rw [List.foldlM_cons] at ran
    obtain ⟨⟨nextValues,nextFrame⟩,head,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨⟨tree,remaining⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp head
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj returned)
    have facts := take_supported original taken
    exact ih (supports_cons facts.1 valuesOriginal) facts.2 tail

private theorem putMany_supported (values : RawOwnerFlow.Frame) {allowed before after}
    (valuesOriginal : Supports allowed values) (original : Supports allowed before)
    (ran : values.foldlM (fun current cell => RawOwnerFlow.put cell.1 cell.2 current) before = some after) :
    Supports allowed after := by
  induction values generalizing before after with
  | nil =>
    have same : before = after := Option.some.inj ran
    exact same ▸ original
  | cons cell values ih =>
    rw [List.foldlM_cons] at ran
    obtain ⟨next,inserted,tail⟩ := Option.bind_eq_some_iff.mp ran
    have nextOriginal := put_supported (valuesOriginal cell List.mem_cons_self) original inserted
    exact ih (fun value member => valuesOriginal value (List.mem_cons_of_mem _ member)) nextOriginal tail

private theorem moveMany_supported (targets : List Raw.Target) {allowed before after}
    (original : Supports allowed before)
    (ran : RawOwnerFlow.moveMany targets before = some after) : Supports allowed after := by
  unfold RawOwnerFlow.moveMany at ran
  obtain ⟨⟨values,remaining⟩,taken,inserted⟩ := Option.bind_eq_some_iff.mp ran
  have facts := takeMany_supported targets (fun _ member => by cases member) original taken
  exact putMany_supported values facts.1 facts.2 inserted

/-- Every successful original constructor retains the same owner/width leaf
provenance. New allocation and release are not accepted by this owner flow. -/
theorem step_supported (operation : Raw.Op) {allowed before after}
    (original : Supports allowed before) (ran : RawOwnerFlow.step before operation = some after) :
    Supports allowed after := by
  cases operation with
  | gate value input output => exact move_supported original ran
  | applyUnitary input output steps => exact move_supported original ran
  | certifiedCompute input output ancilla function uses logical => exact move_supported original ran
  | liftBasis input output wires table =>
    simp only [RawOwnerFlow.step] at ran
    obtain ⟨⟨tree,remaining⟩,taken,tail⟩ := Option.bind_eq_some_iff.mp ran
    split at tail
    · cases tail
    · have facts := take_supported original taken
      exact put_supported facts.1 facts.2 tail
  | cnot control target controlOut targetOut =>
    exact moveMany_supported [⟨control,controlOut⟩,⟨target,targetOut⟩] original ran
  | quantumIf control target controlOut targetOut zero one =>
    exact moveMany_supported [⟨control,controlOut⟩,⟨target,targetOut⟩] original ran
  | toffoli a b target aOut bOut targetOut =>
    exact moveMany_supported [⟨a,aOut⟩,⟨b,bOut⟩,⟨target,targetOut⟩] original ran
  | computeUseUncompute input output targets ancilla function uses =>
    exact moveMany_supported (⟨input,output⟩ :: targets) original ran
  | join left right output =>
    simp only [RawOwnerFlow.step] at ran
    obtain ⟨⟨first,afterFirst⟩,firstRead,tail⟩ := Option.bind_eq_some_iff.mp ran
    obtain ⟨⟨second,remaining⟩,secondRead,inserted⟩ := Option.bind_eq_some_iff.mp tail
    have firstFacts := take_supported original firstRead
    have secondFacts := take_supported firstFacts.2 secondRead
    exact put_supported (.pair firstFacts.1 secondFacts.1) secondFacts.2 inserted
  | split input left right leftBits =>
    simp only [RawOwnerFlow.step] at ran
    obtain ⟨⟨tree,remaining⟩,taken,tail⟩ := Option.bind_eq_some_iff.mp ran
    cases tree with
    | owner owner bits => cases tail
    | pair first second bits =>
      have facts := take_supported original taken
      have children : Supported allowed first ∧ Supported allowed second := by
        cases facts.1 with
        | pair left right => exact ⟨left,right⟩
      by_cases width : (first.width != leftBits) = true
      · simp only [width,ite_true] at tail
        cases tail
      · simp only [width] at tail
        obtain ⟨middle,leftPut,rightPut⟩ := Option.bind_eq_some_iff.mp tail
        exact put_supported children.2 (put_supported children.1 facts.2 leftPut) rightPut
  | init0 output wire => cases ran
  | packUnit output => cases ran
  | unpackUnit input => cases ran

/-- The same literal operation fold preserves only original leaves. This
does not assume that an equal-width leaf is the same original source owner. -/
theorem fold_supported (operations : List Raw.Op) {allowed before after}
    (original : Supports allowed before)
    (ran : operations.foldlM RawOwnerFlow.step before = some after) : Supports allowed after := by
  induction operations generalizing before after with
  | nil =>
    have same : before = after := Option.some.inj ran
    exact same ▸ original
  | cons operation operations ih =>
    rw [List.foldlM_cons] at ran
    obtain ⟨next,head,tail⟩ := Option.bind_eq_some_iff.mp ran
    exact ih (step_supported operation original head) tail

#print axioms step_supported
#print axioms fold_supported

end Qleisli.RuntimeOwnerLeafOrigins
