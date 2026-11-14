import Qleisli.RawReconstructedAction
import QleisliKernel.Qirf.RuntimeWorkspace
import QleisliKernel.Raw.Protected
import QPTL.Clean
import Mathlib.CategoryTheory.Types.Basic

/-! Lift the actual checked workspace body to arbitrary reference amplitudes.
The ordered data axes are the low axes and the scratch Bit is the high axis.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeWorkspaceRestoration
open QleisliKernel QleisliKernel.Finite Semantics.Exact Semantics.Finite
open Qleisli.Semantics.Exact
open Qleisli.Raw.ReconstructedAction (promoted_action)

private theorem allocation_action {bits outputBits : Nat} {actual : Matrix}
    (mapped : Semantics.Raw.MapMeaning bits outputBits (List.range (2^bits)) actual)
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (r : R) (bounded : row < actual.rows) :
    action actual joint row r = if row < 2^bits then joint row r else 0 := by
  unfold action
  rw [mapped.2.1]
  have term (col : Nat) (inRange : col ∈ List.range (2^bits)) :
      entry actual row col * joint col r = (if row = col then joint col r else 0) := by
    have small := List.mem_range.mp inRange
    rw [mapped.2.2 row col bounded (mapped.2.1.symm ▸ small),List.getElem?_range small]
    by_cases same : row = col
    · subst col
      simp
    · have different : col ≠ row := Ne.symm same
      simp [same,different]
  rw [List.map_congr_left term]
  split
  · exact Qleisli.Exact.range_delta_sum _ _ _ (by assumption)
  · apply List.sum_eq_zero
    intro value member
    obtain ⟨col,h,rfl⟩ := List.mem_map.mp member
    have different : row ≠ col := fun same => (by assumption : ¬row < 2^bits) (same ▸ List.mem_range.mp h)
    simp [different]

private theorem cleanContract {bits work left : Nat} {logical : Matrix} {contract : Contract}
    (ok : (Raw.Workspace.required false bits logical).run work = (.ok contract,left)) :
    ∃ encoding first last, (Raw.zeroEncoding bits 1).run first = (.ok encoding,last) ∧
      contract = ⟨encoding,encoding,logical⟩ := by
  unfold Raw.Workspace.required at ok
  obtain ⟨_,first,_,rest⟩ := bind_success _ _ _ _ _ ok
  simp only [Bool.false_eq_true,if_false] at rest
  obtain ⟨encoding,last,encoded,ret⟩ := bind_success _ _ _ _ _ rest
  exact ⟨encoding,first,last,encoded,(pure_success _ _ _ _ ret).1⟩

private theorem dirtyContract {bits work left : Nat} {logical : Matrix} {contract : Contract}
    (ok : (Raw.Workspace.required true bits logical).run work = (.ok contract,left)) :
    ∃ identity promoted first middle last,
      (Raw.mapping (bits+1) (bits+1) (List.range (2^(bits+1)))).run first = (.ok identity,middle) ∧
      (Raw.promote (bits+1) (List.range bits) logical).run middle = (.ok promoted,last) ∧
      contract = ⟨⟨Raw.registerBasis (bits+1),Raw.registerBasis (bits+1),identity⟩,
        ⟨Raw.registerBasis (bits+1),Raw.registerBasis (bits+1),identity⟩,promoted⟩ := by
  unfold Raw.Workspace.required at ok
  obtain ⟨_,first,_,rest⟩ := bind_success _ _ _ _ _ ok
  simp only [if_true] at rest
  obtain ⟨identity,middle,mapped,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨promoted,last,promotedRead,ret⟩ := bind_success _ _ _ _ _ rest
  exact ⟨identity,promoted,first,middle,last,mapped,promotedRead,(pure_success _ _ _ _ ret).1⟩

private theorem accepted {deps : List Dependency} {dirty : Bool} {bits work left : Nat}
    {steps : List Step} {logical actual : Matrix}
    (ok : (Raw.Workspace.check deps dirty bits steps logical).run work = (.ok actual,left)) :
    ∃ contract middle,
      (Raw.Workspace.required dirty bits logical).run work = (.ok contract,middle) ∧
      (QleisliKernel.Finite.check deps (Raw.circuit (bits+1) steps) contract contract).run middle =
        (.ok actual,left) := by
  obtain ⟨contract,middle,required,checked⟩ := bind_success _ _ _ _ _ ok
  exact ⟨contract,middle,required,checked⟩

/-- The literal body acts on the canonical zero input with the exact requested
live phase. Every dirty scratch row is zero for arbitrary reference columns. -/
theorem clean_action {deps : List Dependency} {bits work left : Nat} {steps : List Step}
    {logical actual : Matrix} (ok : (Raw.Workspace.check deps false bits steps logical).run work = (.ok actual,left))
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (r : R) (bound : row < 2^(bits+1)) :
    Qleisli.Semantics.RawAction.circuit deps steps
      (fun col => if col < 2^bits then joint col r else 0) row =
      if row < 2^bits then action logical joint row r else 0 := by
  obtain ⟨contract,middle,required,checked⟩ := accepted ok
  obtain ⟨encoding,first,last,encoded,rfl⟩ := cleanContract required
  obtain ⟨_,_,mapWork,mapLeft,mapRead⟩ := Raw.zeroEncoding_value _ _ _ _ _ encoded
  have mapping := Qleisli.Raw.mapping_denotes _ _ _ _ mapWork mapLeft mapRead
  obtain ⟨_,cols,_,rows,_,_⟩ := Qleisli.Finite.check_encoded _ _ _ _ _ _ _ checked
  have physicalBound : row < actual.rows := rows.symm ▸ mapping.1.symm ▸ bound
  obtain ⟨_,_,_,_,_,_,circuitWork,circuitLeft,_,_,_,_,circuitRead,_,_,_⟩ :=
    QleisliKernel.Finite.check_conditions _ _ _ _ _ _ _ checked
  let padded := fun col ref => if col < 2^bits then joint col ref else 0
  have input : action actual padded row r = action actual (fun col ref => action encoding.map joint col ref) row r := by
    unfold action
    apply Qleisli.Exact.sum_map_congr
    intro col member
    change entry actual row col * padded col r = entry actual row col * action encoding.map joint col r
    rw [allocation_action mapping joint col r (cols ▸ List.mem_range.mp member)]
  calc
    _ = action actual padded row r :=
      (Qleisli.Finite.circuitMatrix_action _ _ _ circuitWork circuitLeft circuitRead padded row r physicalBound).symm
    _ = _ := input
    _ = action encoding.map (fun col ref => action logical joint col ref) row r :=
      Qleisli.Finite.check_reference _ _ _ _ _ _ _ checked joint row r physicalBound
    _ = _ := allocation_action mapping _ row r (rows ▸ physicalBound)

/-- The literal dirty body applies only to the data axes. The high scratch
coordinate and the reference coordinate can be correlated arbitrarily. -/
theorem dirty_action {deps : List Dependency} {bits work left : Nat} {steps : List Step}
    {logical actual : Matrix} (ok : (Raw.Workspace.check deps true bits steps logical).run work = (.ok actual,left))
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (r : R) (bound : row < 2^(bits+1)) :
    Qleisli.Semantics.RawAction.circuit deps steps (fun col => joint col r) row =
      action logical (fun col ref => joint (scatter row (List.range bits) col) ref)
        (gather row (List.range bits)) r := by
  obtain ⟨contract,middle,required,checked⟩ := accepted ok
  obtain ⟨identity,promoted,first,mapLeft,promoteLeft,mapped,promotedRead,rfl⟩ := dirtyContract required
  have mapping := Qleisli.Raw.mapping_denotes _ _ _ _ first mapLeft mapped
  obtain ⟨_,cols,_,rows,_,_⟩ := Qleisli.Finite.check_encoded _ _ _ _ _ _ _ checked
  have physicalBound : row < actual.rows := rows.symm ▸ mapping.1.symm ▸ bound
  obtain ⟨_,_,_,_,_,_,circuitWork,circuitLeft,_,_,_,_,circuitRead,_,_,_⟩ :=
    QleisliKernel.Finite.check_conditions _ _ _ _ _ _ _ checked
  have input : action actual joint row r = action actual (fun col ref => action identity joint col ref) row r := by
    unfold action
    apply Qleisli.Exact.sum_map_congr
    intro col member
    change entry actual row col * joint col r = entry actual row col * action identity joint col r
    have inIdentity : col < identity.rows := cols ▸ List.mem_range.mp member
    rw [allocation_action mapping joint col r inIdentity,if_pos (mapping.1 ▸ inIdentity)]
  calc
    _ = action actual joint row r :=
      (Qleisli.Finite.circuitMatrix_action _ _ _ circuitWork circuitLeft circuitRead joint row r physicalBound).symm
    _ = _ := input
    _ = action identity (fun col ref => action promoted joint col ref) row r :=
      Qleisli.Finite.check_reference _ _ _ _ _ _ _ checked joint row r physicalBound
    _ = action promoted joint row r := by
      rw [allocation_action mapping _ row r (rows ▸ physicalBound),if_pos bound]
    _ = _ := promoted_action mapLeft promoteLeft promotedRead joint row r
      ((Qleisli.Raw.promote_denotes _ _ _ _ _ _ promotedRead).1.symm ▸ bound)

/-- Replacing the data coordinates in the dirty equation leaves the scratch
coordinate unchanged in every contributing input column. -/
theorem dirty_scratch_coordinate (bits row col : Nat) :
    bit (scatter row (List.range bits) col) bits = bit row bits :=
  Qirf.RuntimeScatterTransport.scatter_outside row col bits (List.range bits) (by simp)

/-- The restoration law applies to the steps read from the original checked
Raw interval, with the logical matrix and body read from the original source. -/
theorem literal_action {sources caller deps program block start count before events}
    {event : SourceTypes.SourceRuntimeContext.WorkspaceEvent sources caller}
    {original : Qirf.RuntimeWorkspace.Original event events}
    {interval : @Qirf.RuntimeInterval.Checked deps program block start count}
    (literal : Qirf.RuntimeWorkspace.Literal original interval before)
    {R : Type} (joint : Nat → R → ℂ) (row : Nat) (r : R)
    (bound : row < 2^(original.layout.bits+1)) :
    let bits := original.layout.bits
    if event.fresh then
      Qleisli.Semantics.RawAction.circuit deps literal.emitted.steps
        (fun col => if col < 2^bits then joint col r else 0) row =
        if row < 2^bits then action original.logical.matrix joint row r else 0
    else
      Qleisli.Semantics.RawAction.circuit deps literal.emitted.steps (fun col => joint col r) row =
        action original.logical.matrix (fun col ref => joint (scatter row (List.range bits) col) ref)
          (gather row (List.range bits)) r := by
  obtain ⟨work,left,checked⟩ := literal.equation.checked
  obtain ⟨_,after,restored⟩ := Raw.Workspace.checkOriginal_bound _ _ _ _ _ _ _ work left checked
  cases fresh : event.fresh
  · simp only [fresh,Bool.not_false] at restored
    simpa only [fresh,Bool.false_eq_true,if_false] using dirty_action restored joint row r bound
  · simp only [fresh,Bool.not_true] at restored
    simpa only [fresh,if_true] using clean_action restored joint row r bound

open CategoryTheory

abbrev Live (R : Type) : Type := Nat → R → ℂ
abbrev Physical (bits : Nat) (R : Type) : Type := Fin (2^(bits+1)) → R → ℂ

/-- Embed the live amplitudes at scratch zero. -/
def zeroImage (bits : Nat) (R : Type) : Live R ⟶ Physical bits R :=
  TypeCat.ofHom (fun joint row r => if row.val < 2^bits then joint row.val r else 0)

/-- Denote the original physical steps on the full finite workspace. -/
noncomputable def bodyAction (deps : List Dependency) (bits : Nat) (steps : List Step)
    (R : Type) : Physical bits R ⟶ Physical bits R :=
  TypeCat.ofHom (fun joint row r => Qleisli.Semantics.RawAction.circuit deps steps
    (fun col => if h : col < 2^(bits+1) then joint ⟨col,h⟩ r else 0) row.val)

/-- Denote the requested live operator on each reference column. -/
noncomputable def logicalAction (logical : Matrix) (R : Type) : Live R ⟶ Live R :=
  TypeCat.ofHom (fun joint row r => action logical joint row r)

/-- Each accepted clean body yields an exact square with the same zero
encoding before and after. QPTL can compose this square with adjacent exact
scope proofs without rechecking a larger dense operator. -/
theorem clean_square {deps : List Dependency} {bits work left : Nat} {steps : List Step}
    {logical actual : Matrix} (ok : (Raw.Workspace.check deps false bits steps logical).run work = (.ok actual,left))
    (R : Type) : CommSq (logicalAction logical R) (zeroImage bits R) (zeroImage bits R)
      (bodyAction deps bits steps R) := by
  refine ⟨?_⟩
  apply ConcreteCategory.hom_ext
  intro joint
  funext row r
  change (if row.val < 2^bits then action logical joint row.val r else 0) =
    Qleisli.Semantics.RawAction.circuit deps steps
      (fun col => if h : col < 2^(bits+1) then (if col < 2^bits then joint col r else 0) else 0) row.val
  have padded : (fun col => if _h : col < 2^(bits+1) then (if col < 2^bits then joint col r else 0) else 0) =
      (fun col => if col < 2^bits then joint col r else 0) := by
    funext col
    by_cases h : col < 2^bits
    · have larger : col < 2^(bits+1) := Nat.lt_trans h (by
        rw [Nat.pow_succ]
        have := Nat.two_pow_pos bits
        omega)
      simp [h,larger]
    · simp [h]
  exact (congrArg (fun values => Qleisli.Semantics.RawAction.circuit deps steps values row.val) padded).trans
    (clean_action ok joint row.val r row.isLt) |>.symm

/-- Two independently accepted clean bodies compose on the same live and
scratch interface, retaining the full reference and the order of the bodies. -/
theorem clean_sequence {deps : List Dependency} {bits w₁ l₁ w₂ l₂ : Nat}
    {first second : List Step} {logical₁ logical₂ actual₁ actual₂ : Matrix}
    (accepted₁ : (Raw.Workspace.check deps false bits first logical₁).run w₁ = (.ok actual₁,l₁))
    (accepted₂ : (Raw.Workspace.check deps false bits second logical₂).run w₂ = (.ok actual₂,l₂))
    (R : Type) : CommSq (logicalAction logical₁ R ≫ logicalAction logical₂ R)
      (zeroImage bits R) (zeroImage bits R) (bodyAction deps bits first R ≫ bodyAction deps bits second R) :=
  (clean_square accepted₁ R).horiz_comp (clean_square accepted₂ R)

#print axioms clean_action
#print axioms dirty_action
#print axioms dirty_scratch_coordinate
#print axioms literal_action
#print axioms clean_square
#print axioms clean_sequence
end Qleisli.RuntimeWorkspaceRestoration

namespace Qleisli.RuntimeComputedResources
open QleisliKernel Qirf
open Raw.WorkspaceResources (Counts readCounts)

/-- The actual protected constructor accounts for one private qubit, the
forward and inverse predicate passes, and every use in the emitted interval.
The peak includes the whole caller frame, even when only one owner is used. -/
theorem protected_counts {sources caller deps program block start count before}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {prepared : RuntimeComputedUse.Prepared event}
    {interval : @RuntimeInterval.Checked deps program block start count}
    (checked : RuntimeComputedUse.Checked prepared interval before) :
    ∃ result, Raw.dispatch (deps.map (·.signature)) interval.before.quantum checked.literal.operation = .ok result ∧
      Semantics.RawTrace.interval interval.before.quantum.reference [checked.literal.operation] =
        some ⟨result.state.reference,result.events,interval.before.quantum.frame.length⟩ ∧
      readCounts interval.before.quantum.frame.length result.events =
        ⟨interval.before.quantum.frame.length+1,1,1,2,checked.literal.uses.length,0⟩ := by
  obtain ⟨result,ran⟩ := checked.literal.dispatch
  obtain ⟨_,_,_,_,_,events⟩ := Raw.dispatch_protected_conditions _ _ _ _ _ _ _ _ result ran
  have traced := Raw.dispatch_reference _ _ _ _ ran
  refine ⟨result,ran,?_,?_⟩
  · simp only [Semantics.RawTrace.interval,Semantics.RawTrace.advance,List.foldlM_cons,
      List.foldlM_nil,traced]
    rfl
  · rw [events]
    simp [readCounts,Raw.WorkspaceResources.Counts.then_,Raw.WorkspaceResources.eventCounts]

/-- The certified form has the same preparation and inverse obligations.
Its checked logical witness adds no physical operation to the emitted body. -/
theorem certified_counts {sources caller deps program block start count before}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {prepared : RuntimeCertifiedComputed.Prepared event}
    {interval : @RuntimeInterval.Checked deps program block start count}
    (checked : RuntimeCertifiedComputed.Checked prepared interval before)
    {receipts : List Semantics.ObservingFunction.Receipt}
    (resource : Raw.WorkspaceResources.Checked receipts interval.before.quantum.reference
      interval.after.quantum.reference [checked.literal.operation]) :
    resource.counts = ⟨interval.before.quantum.frame.length+1,1,1,2,checked.literal.useSteps.length,0⟩ :=
  resource.clean

/-- The accepted certified equation uses the emitted use word between one
forward predicate and one inverse predicate. XOR computation is its own
inverse. The logical witness is reconstructed in a separate checker call. -/
theorem certified_physical_word {sources caller deps program block start count before}
    {event : SourceTypes.SourceRuntimeContext.ComputedEvent sources caller}
    {prepared : RuntimeCertifiedComputed.Prepared event}
    {interval : @RuntimeInterval.Checked deps program block start count}
    (checked : RuntimeCertifiedComputed.Checked prepared interval before) :
    let literal := checked.literal
    let bits := literal.input.port.bits
    let predicate := Raw.computeStep bits bits 1 literal.table
    ∃ encoding physical,
      let contract : Semantics.Finite.Contract := ⟨encoding,encoding,checked.logical.emitted⟩
      RuntimeInterval.Computed
        (QleisliKernel.Finite.check deps (Raw.circuit (bits+1) ([predicate] ++ literal.useSteps ++ [predicate]))
          contract contract) physical := by
  obtain ⟨work,left,ran⟩ := checked.logical.emittedRead
  obtain ⟨encoding,physical,_,_,_,_,checkWork,checkLeft,_,_,accepted⟩ :=
    Raw.clean_conditions _ _ _ _ _ _ _ _ work left ran
  exact ⟨encoding,physical,checkWork,checkLeft,accepted⟩

#print axioms protected_counts
#print axioms certified_counts
#print axioms certified_physical_word
end Qleisli.RuntimeComputedResources
