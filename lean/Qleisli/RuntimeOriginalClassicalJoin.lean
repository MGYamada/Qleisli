import Qleisli.RuntimeOriginalBranch
import Qleisli.Semantics.OrdinaryValuePhi
import Mathlib.Data.List.Forall2

/-! The original conditional's classical merge reads the selected arm's
actual history and supplies the checked parent SSA expressions. It retains
the full quantum operator and the existing hidden outcomes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalClassicalJoin
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Finite
open QleisliKernel.Semantics.OrdinaryValue (lookup append_extends)
open Qleisli.Semantics.ObservingAction (History merge)
open Qleisli.Semantics.OrdinaryValue (phiBindings phiBindings_cons phiBindings_lookup lookup_append_absent)
open RuntimeOrdinarySSA (Agreement Valuation Values bitValue)
open RuntimeOrdinaryPhis (Phi)

private theorem lookup_unissued {values : Values} {id : Nat}
    (absent : id ∉ values.map Prod.fst) : lookup values id = none := by
  unfold lookup
  cases found : values.find? (fun pair => pair.1 == id) with
  | none => rfl
  | some pair =>
    have name := beq_iff_eq.mp (List.find?_some (p := fun pair : Nat × Bool => pair.1 == id) found)
    exact (absent (List.mem_map.mpr ⟨pair,List.mem_of_find?_eq_some found,name⟩)).elim

private theorem lookup_native {values : Values} {id : Nat} {bit : Bool}
    (found : lookup values id = some bit) :
    (Raw.Instrument.lookup values id).run 0 = (.ok bit,0) := by
  change (lift (readOption (lookup values id)) : WorkM Bool).run 0 = _
  rw [found]
  rfl

private theorem bindings_exist (choice : Bool) (phis : List Phi) (values : Values)
    (present : ∀ phi ∈ phis, ∃ bit, lookup values (if choice then phi.thenId else phi.elseId) = some bit) :
    ∃ added, phiBindings choice phis values = some added := by
  induction phis with
  | nil => exact ⟨[],rfl⟩
  | cons first rest ih =>
    obtain ⟨bit,found⟩ := present first List.mem_cons_self
    obtain ⟨added,read⟩ := ih (fun phi member => present phi (List.mem_cons_of_mem _ member))
    refine ⟨(first.output,bit)::added,?_⟩
    rw [phiBindings_cons,found]
    change (do
      let tail ← phiBindings choice rest values
      pure ((first.output,bit)::tail)) = _
    rw [read]
    rfl

/-- For an actual selected-arm result, every merged SSA expression agrees
with the original interpreter's appended values. Destinations are fresh by
the parent Raw check and the selected history's issued identities. -/
theorem original_merge_agrees {sources rootOwner rootName caller name dependencies program block offset
    path event source actual before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name dependencies program block offset
      path event source actual before left right ordinary leftOrdinary rightOrdinary)
    (reference : Valuation) (choice : Bool) (history : History)
    (condition : Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice))
    (kept : Agreement reference history.values ordinary.table)
    (selected : Agreement reference history.values (if choice then leftOrdinary.table else rightOrdinary.table))
    (issued : history.values.map Prod.fst ⊆
      (if choice then actual.thenState else actual.elseState).classical.map Prod.fst) :
    ∃ after : History, merge choice actual.classical history = some after ∧
      after.hidden = history.hidden ∧ after.operator = history.operator ∧
      Agreement reference after.values action.ordinaryAfter.table := by
  have inputs : ∀ phi ∈ actual.classical,
      ∃ bit, lookup history.values (if choice then phi.thenId else phi.elseId) = some bit := by
    intro phi member
    obtain ⟨one⟩ := action.ordinaryPhis.bothOperands phi member
    cases choice with
    | false =>
      obtain ⟨bit,found,_computed⟩ := selected _ _ one.elseValue.member
      exact ⟨bit,found⟩
    | true =>
      obtain ⟨bit,found,_computed⟩ := selected _ _ one.thenValue.member
      exact ⟨bit,found⟩
  obtain ⟨added,merged⟩ := bindings_exist choice actual.classical history.values inputs
  let after := {history with values := history.values++added}
  refine ⟨after,?_,rfl,rfl,?_⟩
  · change (phiBindings choice actual.classical history.values >>= fun values =>
        some {history with values := history.values++values}) = some after
    rw [merged]
    rfl
  · intro id expression member
    rw [action.ordinaryRead] at member
    change (id,expression) ∈ action.ordinaryVisible.table at member
    rw [action.ordinaryVisible.original] at member
    have onTable : (id,expression) ∈ RuntimeBranchAction.mergedTable action.ordinaryPhis action.condition.required :=
      List.mem_of_mem_filter member
    rcases List.mem_append.mp onTable with old | joined
    · obtain ⟨bit,found,evaluated⟩ := kept id expression old
      exact ⟨bit,append_extends _ _ _ _ found,evaluated⟩
    · obtain ⟨pair,present,same⟩ := List.mem_map.mp joined
      cases same
      have rawPhi : pair.1 ∈ actual.classical :=
        action.ordinaryPhis.everyRaw ▸ List.mem_map_of_mem present
      obtain ⟨bit,found⟩ := inputs pair.1 rawPhi
      have fresh := RuntimeOriginalBranch.original_branch_outputs_fresh actual pair.1 rawPhi
      have missing : lookup history.values pair.1.output = none := by
        apply lookup_unissued
        intro present
        have used := issued present
        cases choice
        · exact fresh.2 used
        · exact fresh.1 used
      refine ⟨bit,?_,pair.2.sound action.condition.required choice bit 0 0 condition selected (lookup_native found)⟩
      change lookup (history.values++added) pair.1.output = some bit
      rw [lookup_append_absent _ _ _ missing,phiBindings_lookup merged action.ordinaryPhis.distinct rawPhi]
      exact found

theorem merge_family (choice : Bool) (phis : List Phi) (histories : List History)
    (transport : History → History)
    (relates : History → History → Prop)
    (each : ∀ history ∈ histories, ∃ after, merge choice phis (transport history) = some after ∧ relates history after) :
    ∃ results, (histories.map transport).mapM (merge choice phis) = some results ∧ List.Forall₂ relates histories results := by
  induction histories with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons first rest ih =>
    obtain ⟨result,merged,related⟩ := each first List.mem_cons_self
    obtain ⟨results,allMerged,allRelated⟩ := ih (fun item member => each item (List.mem_cons_of_mem _ member))
    refine ⟨result::results,?_,.cons related allRelated⟩
    rw [List.map_cons,List.mapM_cons,merged,allMerged]
    rfl

/-- Once the original selected arm has supplied its returned histories and
SSA agreement, the literal parent branch produces one matching merged
history per arm result, in order. -/
theorem original_branch_classical_join {sources rootOwner rootName caller name dependencies program block offset
    path event source actual before left right ordinary leftOrdinary rightOrdinary}
    (action : @RuntimeBranchAction.Checked sources rootOwner rootName caller name dependencies program block offset
      path event source actual before left right ordinary leftOrdinary rightOrdinary)
    (trace : RuntimeOriginalBranch.Trace actual)
    (recurse : List Semantics.Observation.Event → History → Option (List History))
    (input : List Nat) (member : input ∈ action.condition.inputs.rows) (bits : List Bool)
    (width : bits.length = ordinary.measurements.length) (history : History) :
    let reference := RuntimeBranchCondition.reference input ordinary.measurements bits
    Agreement reference history.values ordinary.table →
    (∀ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) →
      ∀ finished,
        recurse (trace.armEvents choice) history = some finished →
        ∀ result ∈ finished,
          Agreement reference result.values ordinary.table ∧
          Agreement reference result.values (if choice then leftOrdinary.table else rightOrdinary.table) ∧
          result.values.map Prod.fst ⊆ (if choice then actual.thenState else actual.elseState).classical.map Prod.fst) →
    ∃ choice,
      Semantics.SourceOrdinary.evaluate reference action.condition.required = some (bitValue choice) ∧
      ∀ finished, recurse (trace.armEvents choice) history = some finished →
        ∃ results, Qleisli.Semantics.ObservingAction.step dependencies recurse
            (RuntimeOriginalBranch.branchEvent actual trace.left trace.right) history = some results ∧
          List.Forall₂ (fun arm joined =>
            joined.hidden = arm.hidden ∧ joined.operator = arm.operator ∧
            Agreement reference joined.values action.ordinaryAfter.table) finished results := by
  intro reference agrees armProof
  obtain ⟨choice,computed,actualStep⟩ :=
    RuntimeOriginalBranch.original_branch_step action.condition trace recurse input member bits width history agrees
  refine ⟨choice,computed,?_⟩
  intro finished ran
  have each := armProof choice computed finished ran
  obtain ⟨results,merged,related⟩ := merge_family choice actual.classical finished id
    (fun arm joined => joined.hidden = arm.hidden ∧ joined.operator = arm.operator ∧
      Agreement reference joined.values action.ordinaryAfter.table)
    (fun item present =>
      let proof := each item present
      original_merge_agrees action reference choice item computed proof.1 proof.2.1 proof.2.2)
  refine ⟨results,?_,related⟩
  rw [actualStep,ran]
  simpa only [List.map_id] using merged

#print axioms original_merge_agrees
#print axioms original_branch_classical_join
end Qleisli.RuntimeOriginalClassicalJoin
