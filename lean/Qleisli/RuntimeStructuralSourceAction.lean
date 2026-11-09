import Qleisli.RuntimeStructuralWires
import Qleisli.RuntimeStructuralSemanticLayouts
import Qleisli.RuntimeNamedBlockEncoding

/-! The original structural operations preserve the complete physical operator.
The exact result uses the original checked source owner order and the
independent reference forest layout.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeStructuralSourceAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open Semantics.FiniteCarrier (Layout layout tensor)
open RuntimeOwnerMap (Map Binding Owner)
open RuntimeForestCode
open RuntimeOwnerCodeReindex
open Qleisli.RuntimeForestOrderedProduct
open Qleisli.RuntimeForestProduct (referenceAction)
open Qleisli.RuntimeForestRegroup (sourceDimension dimensionAt_source)
open Qleisli.RuntimeNamedBlockEncoding (append)
open Qleisli.RuntimeStructuralLayoutEvidence (SemanticOwnerLayout)
open Qleisli.Semantics.Exact (scalar)

def spectators {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before) : Map :=
  before.bindings.filter (fun binding => !action.inputRoles.contains binding.owner)

private def produced {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before) : Map :=
  (action.outputRoles.zip action.outputs).map fun (owner,port) => ⟨owner,port⟩

private theorem zipped_carriers (roles : List Owner) (ports : List Semantics.Raw.Port) :
    carrierOwners ((roles.zip ports).map fun (owner,port) => ⟨owner,port⟩) =
      RuntimeStructuralAction.owners ports roles := by
  induction roles generalizing ports with
  | nil => cases ports <;> rfl
  | cons first rest ih =>
    cases ports with
    | nil => rfl
    | cons port ports =>
      change ⟨port,first.basis⟩ :: carrierOwners ((rest.zip ports).map fun (owner,port) => ⟨owner,port⟩) =
        ⟨port,first.basis⟩ :: RuntimeStructuralAction.owners ports rest
      rw [ih]

/-- The original source operand read fixes the order and the complementary
spectators. Source identity follows the exact tokens at every width. -/
theorem original_partition {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before) :
    ∃ selected : Map, selected.map Binding.owner = action.inputRoles ∧
      selected.map Binding.port = action.inputs ∧
      (spectators action ++ selected).Perm before.bindings := by
  obtain ⟨work,left,read⟩ := action.inputRead
  obtain ⟨selected,middle,ordered,returned⟩ := bind_success _ _ _ _ _ read
  have ports : selected.map Binding.port = action.inputs := (pure_success _ _ _ _ returned).1.symm
  obtain ⟨subset,owners⟩ := RuntimeSelectionPartition.order_values before.bindings action.inputRoles selected
    ⟨work,middle,ordered⟩
  have ordinals : (before.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using action.beforeFrame.ownersDistinct
  have inputTokens := (RuntimeStructuralWires.original_wires action).2.2
  rw [← ports,List.map_map,Function.comp_def] at inputTokens
  have selectedDistinct : selected.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.port.token) same)) inputTokens
  have allDistinct : before.bindings.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.owner.ordinal)
      (fun _ _ different same => different (congrArg (fun binding : Binding => binding.owner.ordinal) same)) ordinals
  let chosen : Binding → Bool := fun binding => action.inputRoles.contains binding.owner
  have selectedPerm : selected.Perm (before.bindings.filter chosen) := by
    apply (List.perm_ext_iff_of_nodup selectedDistinct (List.Pairwise.filter chosen allDistinct)).mpr
    intro binding
    constructor
    · intro member
      refine List.mem_filter.mpr ⟨subset member,?_⟩
      apply List.contains_iff_mem.mpr
      rw [← owners]
      exact List.mem_map_of_mem member
    · intro member
      obtain ⟨present,chosen⟩ := List.mem_filter.mp member
      have ownerMember : binding.owner ∈ selected.map Binding.owner :=
        owners.symm ▸ List.contains_iff_mem.mp chosen
      obtain ⟨found,inside,same⟩ := List.mem_map.mp ownerMember
      have exactBinding := RuntimeOwnerTransitionAction.map_unique (fun entry : Binding => entry.owner.ordinal)
        before.bindings ordinals found (subset inside) binding present (congrArg (·.ordinal) same)
      exact exactBinding ▸ inside
  refine ⟨selected,owners,ports,?_⟩
  exact List.perm_append_comm.trans ((selectedPerm.append_right _).trans (List.filter_append_perm chosen _))

private theorem layouts_exist (bindings : Map)
    (available : ∀ binding ∈ bindings, ∃ code, layout binding.owner.basis = some code) :
    ∃ layouts, ownerLayouts bindings = some layouts := by
  induction bindings with
  | nil => exact ⟨[],rfl⟩
  | cons binding rest ih =>
    obtain ⟨head,headRead⟩ := available binding List.mem_cons_self
    obtain ⟨tail,tailRead⟩ := ih (fun owner member => available owner (List.mem_cons_of_mem _ member))
    refine ⟨head::tail,?_⟩
    unfold ownerLayouts at tailRead ⊢
    simp only [List.mapM_cons,headRead,tailRead,bind,Option.bind,pure]

private theorem unit_shape {kind op inputs outputs tokens}
    (ordered : RuntimeStructuralAction.PortOrder kind op inputs outputs tokens) (unit : kind = .unit) :
    inputs = [] ∧ ∃ role, outputs = [role] := by
  cases ordered <;> simp_all

private theorem finish_shape {kind op inputs outputs tokens}
    (ordered : RuntimeStructuralAction.PortOrder kind op inputs outputs tokens) (finish : kind = .finish) :
    outputs = [] := by
  cases ordered <;> simp_all

private theorem output_layouts {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (available : ∀ binding ∈ before.bindings, Nonempty (SemanticOwnerLayout binding)) :
    ∃ layouts, ownerLayouts (produced action) = some layouts := by
  have supported (kind : action.kind = .join ∨ action.kind = .split) :
      ∃ layouts, ownerLayouts (produced action) = some layouts := by
    have resultLayouts := Qleisli.RuntimeStructuralSemanticLayouts.join_split_after_layouts action kind available
    apply layouts_exist
    intro binding member
    have resultBindings : action.after.bindings = spectators action ++ produced action := action.afterBindings
    have present : binding ∈ action.after.bindings := resultBindings.symm ▸ List.mem_append_right _ member
    obtain ⟨shape⟩ := resultLayouts binding present
    exact ⟨shape.layout,shape.reference⟩
  cases kind : action.kind with
  | join => exact supported (.inl kind)
  | split => exact supported (.inr kind)
  | unit =>
    obtain ⟨inputs,role,outputs⟩ := unit_shape action.portOrder kind
    have outputWidth := beq_iff_eq.mp (Bool.and_eq_true_iff.mp action.outputWidths).1
    have count : action.outputs.length = 1 := by simpa only [outputs,List.length_singleton] using outputWidth
    obtain ⟨port,portRead⟩ := List.length_eq_one_iff.mp count
    have shape := action.coordinates
    rw [inputs,outputs,portRead] at shape
    have unitBasis : role.basis = [.unit] := shape.symm
    refine ⟨[Semantics.FiniteCarrier.singleton],?_⟩
    unfold produced
    rw [outputs,portRead]
    change ownerLayouts [⟨role,port⟩] = _
    simp only [ownerLayouts,List.mapM_cons,List.mapM_nil,unitBasis]
    rfl
  | finish =>
    have outputs := finish_shape action.portOrder kind
    refine ⟨[],?_⟩
    unfold produced
    rw [outputs]
    rfl

/-- The same before and after physical coordinates act on arbitrary reference
columns. The new logical index is the source operand regrouping, keeping all
spectators in their original order. The independent output layout includes
results beyond the per-owner native reader limits. -/
theorem original_reference_action {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (input : Frame action.beforeFrame) :
    ∃ selected : Map, selected.map Binding.owner = action.inputRoles ∧
      selected.map Binding.port = action.inputs ∧ (spectators action ++ selected).Perm before.bindings ∧
      ∃ output : Sparse, sparseLayout (forestBasis action.after.bindings) = some output ∧
        ∀ {Reference : Type} (joint : Nat → Reference → ℂ) physical reference,
          referenceAction input joint physical reference =
          ((List.range output.dimension).map fun logical =>
            scalar (embed action.interval.after.quantum.frame action.after.bindings output physical logical) *
              joint (Qleisli.MixedRadix.recode (spectators action ++ selected) before.bindings
                (sourceDimension before.bindings) logical) reference).sum := by
  obtain ⟨selected,owners,ports,partition⟩ := original_partition action
  have originalPermutation : (spectators action ++ selected).Perm action.beforeFrame.bindings :=
    action.beforeBindings.symm ▸ partition
  obtain ⟨all,kept⟩ := reindex_exists input.owners (spectators action ++ selected) originalPermutation.subset
  obtain ⟨unchanged,operands,rfl⟩ := RuntimeNamedBlockEncoding.append_exists _ _ all
  let initial : OwnerCodes before.bindings := action.beforeBindings ▸ input.owners
  have available (binding : Binding) (member : binding ∈ before.bindings) :
      Nonempty (SemanticOwnerLayout binding) := by
    obtain ⟨code,_read⟩ := lookup_exists initial binding member
    exact ⟨⟨code.layout,code.reference.1,code.reference.2.1,code.reference.2.2⟩⟩
  have resultBindings : action.after.bindings = spectators action ++ produced action := action.afterBindings
  obtain ⟨newOwners,newRead⟩ := output_layouts action available
  have selectedCarriers : RuntimeStructuralAction.owners action.inputs action.inputRoles = carrierOwners selected := by
    rw [← ports,← owners]
    simp only [RuntimeStructuralAction.owners,carrierOwners,List.zip_map',List.map_map,Function.comp_def]
  have codeSame : forestBasis selected = forestBasis (produced action) := by
    unfold forestBasis produced
    rw [zipped_carriers]
    exact selectedCarriers ▸ action.coordinates
  have newProduct := forest_from_layouts newRead
  have originalProduct := forest_original operands
  rw [codeSame] at originalProduct
  have sameProduct : newOwners.foldr tensor Semantics.FiniteCarrier.singleton = layoutProduct operands :=
    Option.some.inj (newProduct.symm.trans originalProduct)
  have outputLayout := forest_append (ownerLayouts_original unchanged) newRead
  have reorderedLayout := forest_append (ownerLayouts_original unchanged) (ownerLayouts_original operands)
  rw [sameProduct,← resultBindings] at outputLayout
  have combined := forest_original (append unchanged operands)
  have exactLayout : layout (forestBasis action.after.bindings) =
      some (layoutProduct (append unchanged operands)) :=
    outputLayout.trans (reorderedLayout.symm.trans combined)
  obtain ⟨output,original,agrees⟩ := sparseLayout_complete _ _ exactLayout
  have ⟨frames,wires,_⟩ := RuntimeStructuralWires.original_wires action
  have widths := beq_iff_eq.mp (Bool.and_eq_true_iff.mp action.outputWidths).1
  have producedPorts : (produced action).map Binding.port = action.outputs := by
    unfold produced
    simp only [List.map_map,Function.comp_def]
    exact List.map_snd_zip (Nat.le_of_eq widths)
  have axes : forestAxes action.interval.after.quantum.frame action.after.bindings =
      forestAxes action.interval.before.quantum.frame (spectators action ++ selected) := by
    unfold forestAxes
    rw [frames,resultBindings]
    simp only [List.flatMap_append]
    have suffix : (produced action).flatMap (fun b => b.port.wires) = selected.flatMap (fun b => b.port.wires) := by
      calc
        _ = action.outputs.flatMap (·.wires) := by rw [← producedPorts,List.flatMap_map]
        _ = action.inputs.flatMap (·.wires) := wires
        _ = _ := by rw [← ports,List.flatMap_map]
    rw [suffix]
  have dimensions : output.dimension = (sparseProduct (append unchanged operands)).dimension :=
    agrees.dimension.trans (product_agrees (append unchanged operands)).dimension.symm
  refine ⟨selected,owners,ports,partition,output,original,?_⟩
  intro Reference joint physical reference
  rw [RuntimeNamedOutputOrder.regroup_dense_action input (spectators action ++ selected)
    ⟨append unchanged operands,kept⟩ originalPermutation joint physical reference,dimensions]
  apply Qleisli.Exact.sum_map_congr
  intro logical member
  change coefficients action.interval.before.quantum.frame (append unchanged operands) physical logical * _ = _
  rw [funext (dimensionAt_source input.owners),action.beforeBindings]
  apply congrArg (fun coefficient =>
    coefficient * joint (Qleisli.MixedRadix.recode (spectators action ++ selected) before.bindings
      (sourceDimension before.bindings) logical) reference)
  unfold embed
  rw [axes]
  have entry := congrArg (fun coordinate : Option Nat =>
    if coordinate == some (Semantics.Finite.gather physical
      (forestAxes action.interval.before.quantum.frame (spectators action ++ selected))) then
      Semantics.Exact.Scalar.one else Semantics.Exact.Scalar.zero) (agrees.labels logical)
  exact (product_coefficient _ (append unchanged operands) physical logical (List.mem_range.mp member)).symm.trans
    (congrArg scalar entry).symm

#print axioms original_partition
#print axioms original_reference_action
end Qleisli.RuntimeStructuralSourceAction
