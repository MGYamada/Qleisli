import Qleisli.RuntimeStructuralWires
import Qleisli.RuntimeStructuralSemanticLayouts
import Qleisli.RuntimeSemanticForest
import Qleisli.RuntimeLiteralReturnOrder

/-! The original structural operations preserve the complete physical operator.
The exact result uses the original checked source owner order and the
independent reference forest layout.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeStructuralSourceAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open Semantics.FiniteCarrier (layout tensor singleton)
open RuntimeOwnerMap (Map Binding Owner)
open RuntimeForestCode (carrierOwners forestBasis forestAxes embed)
open Qleisli.RuntimeForestOrderedProduct (forest_append agrees_entry)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.RuntimeStructuralLayoutEvidence (SemanticOwnerLayout)
open Qleisli.RuntimeSemanticForest (Available Frame owner_reads forest_read product frame_exists product_agrees)
open Qleisli.Semantics.Exact (scalar)

private def kept (incoming : Map) (roles : List Owner) : Map :=
  incoming.filter (fun binding => !roles.contains binding.owner)

/-- The original source operand lookup determines the output logical index. -/
def sourceRegroup {Reference : Type} (roles : List Owner) (incoming : Map)
    (joint : Nat → Reference → ℂ) : Option (Nat → Reference → ℂ) := do
  let selected ← roles.mapM (RuntimeOwnerMap.byOwner incoming)
  return fun logical reference =>
    joint (Qleisli.MixedRadix.recode (kept incoming roles ++ selected) incoming
      (sourceDimension incoming) logical) reference

def spectators {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before) : Map :=
  kept before.bindings action.inputRoles

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
    ∃ selected : Map, action.inputRoles.mapM (RuntimeOwnerMap.byOwner before.bindings) = some selected ∧
      selected.map Binding.owner = action.inputRoles ∧ selected.map Binding.port = action.inputs ∧
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
  refine ⟨selected,RuntimeLiteralHistory.order_source ⟨work,middle,ordered⟩,owners,ports,?_⟩
  exact List.perm_append_comm.trans ((selectedPerm.append_right _).trans (List.filter_append_perm chosen _))

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
    (available : Available before.bindings) : Available action.after.bindings := by
  have created (result : Available (produced action)) : Available action.after.bindings := by
    intro binding member
    rw [action.afterBindings] at member
    rcases List.mem_append.mp member with retained | new
    · exact available binding (List.mem_filter.mp retained).1
    · exact result binding new
  cases kind : action.kind with
  | join => exact Qleisli.RuntimeStructuralSemanticLayouts.join_split_after_layouts action (.inl kind) available
  | split => exact Qleisli.RuntimeStructuralSemanticLayouts.join_split_after_layouts action (.inr kind) available
  | unit =>
    obtain ⟨inputs,role,outputs⟩ := unit_shape action.portOrder kind
    have outputWidth := beq_iff_eq.mp (Bool.and_eq_true_iff.mp action.outputWidths).1
    have count : action.outputs.length = 1 := by simpa only [outputs,List.length_singleton] using outputWidth
    obtain ⟨port,portRead⟩ := List.length_eq_one_iff.mp count
    have shape := action.coordinates
    rw [inputs,outputs,portRead] at shape
    have unitBasis : role.basis = [.unit] := shape.symm
    have portLayout : layout role.basis = some singleton := by rw [unitBasis]; rfl
    have member : (port,role) ∈ action.outputs.zip action.outputRoles := by
      rw [outputs,portRead]
      exact List.mem_cons_self
    have widths := RuntimeStructuralAction.widths_reference _ _ action.outputWidths port role member singleton portLayout
    apply created
    intro binding inside
    unfold produced at inside
    rw [outputs,portRead] at inside
    have original : binding = (⟨role,port⟩ : Binding) := by simpa using inside
    subst binding
    exact ⟨⟨singleton,portLayout,widths.1,widths.2⟩⟩
  | finish =>
    have outputs := finish_shape action.portOrder kind
    apply created
    intro binding member
    unfold produced at member
    rw [outputs] at member
    cases member

private theorem append_product {first second : Map} (left : Available first) (right : Available second) :
    product (first ++ second) = tensor (product first) (product second) := by
  have complete : Available (first ++ second) := fun binding member =>
    (List.mem_append.mp member).elim (left binding) (right binding)
  exact Option.some.inj ((forest_read complete).symm.trans
    (forest_append (owner_reads first left) (owner_reads second right)))

/-- The actual structural receipt transports a reference frame across every
supported source operation. The result supplies its own independent layouts
and can serve as the input of a later structural operation. -/
theorem original_reference_action {dependencies program sources caller block start count event before}
    (action : @RuntimeStructuralAction.Checked dependencies program sources caller block start count event before)
    (input : Frame before.bindings) :
    ∃ output : Frame action.after.bindings,
      ∀ {Reference : Type} (joint : Nat → Reference → ℂ),
        ∃ expected, sourceRegroup (event.arguments.flatMap SourceTypes.SourceRuntimeValues.valueOwners)
            before.bindings joint = some expected ∧
          ∀ row reference, RuntimeSemanticForest.action input action.interval.before.quantum.frame joint row reference =
            RuntimeSemanticForest.action output action.interval.after.quantum.frame expected row reference := by
  obtain ⟨selected,sourceRead,owners,ports,partition⟩ := original_partition action
  let grouped := spectators action ++ selected
  have groupedAvailable : Available grouped := fun binding member => input.available binding (partition.subset member)
  obtain ⟨reordered⟩ := frame_exists groupedAvailable
  have resultAvailable := output_layouts action input.available
  obtain ⟨output⟩ := frame_exists resultAvailable
  have resultBindings : action.after.bindings = spectators action ++ produced action := action.afterBindings
  have spectatorsAvailable : Available (spectators action) := fun binding member =>
    groupedAvailable binding (List.mem_append_left _ member)
  have selectedAvailable : Available selected := fun binding member =>
    groupedAvailable binding (List.mem_append_right _ member)
  have producedAvailable : Available (produced action) := fun binding member =>
    resultAvailable binding (resultBindings.symm ▸ List.mem_append_right _ member)
  have selectedCarriers : RuntimeStructuralAction.owners action.inputs action.inputRoles = carrierOwners selected := by
    rw [← ports,← owners]
    simp only [RuntimeStructuralAction.owners,carrierOwners,List.zip_map',List.map_map,Function.comp_def]
  have codeSame : forestBasis selected = forestBasis (produced action) := by
    unfold forestBasis produced
    rw [zipped_carriers]
    exact selectedCarriers ▸ action.coordinates
  have sameProduct : product selected = product (produced action) := by
    have left := forest_read selectedAvailable
    rw [codeSame] at left
    exact Option.some.inj (left.symm.trans (forest_read producedAvailable))
  have exactProduct : product grouped = product action.after.bindings := by
    change product (spectators action ++ selected) = _
    rw [resultBindings,append_product spectatorsAvailable selectedAvailable,
      append_product spectatorsAvailable producedAvailable,sameProduct]
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
  have dimensions : reordered.code.dimension = output.code.dimension :=
    (product_agrees reordered).dimension.trans
      ((congrArg (fun l => l.labels.length) exactProduct).trans (product_agrees output).dimension.symm)
  have unique : before.bindings.Nodup := by
    rw [← action.beforeBindings]
    exact List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different same => different (congrArg (fun b : Binding => b.port.token) same))
      action.beforeFrame.tokensDistinct
  refine ⟨output,?_⟩
  intro Reference joint
  let expected := fun logical reference =>
    joint (Qleisli.MixedRadix.recode grouped before.bindings (sourceDimension before.bindings) logical) reference
  refine ⟨expected,?_,?_⟩
  · rw [← action.originalInputs]
    simp only [sourceRegroup,sourceRead,bind,Option.bind,pure,expected,grouped,spectators]
  · intro row reference
    have regrouped := RuntimeSemanticForest.regroup_action input reordered partition.symm unique
      action.interval.before.quantum.frame joint row reference
    refine regrouped.trans ?_
    unfold RuntimeSemanticForest.action
    rw [dimensions]
    apply Qleisli.Exact.sum_map_congr
    intro logical _member
    apply congrArg (fun coefficient => coefficient * expected logical reference)
    unfold embed
    rw [axes,agrees_entry (product_agrees reordered),agrees_entry (product_agrees output),exactProduct]

#print axioms original_partition
#print axioms original_reference_action
end Qleisli.RuntimeStructuralSourceAction
