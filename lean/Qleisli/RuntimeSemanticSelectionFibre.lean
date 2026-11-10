import Qleisli.RuntimeSemanticSelectionGeometry
import Qleisli.RuntimeSparseOperationAction
import Qleisli.RuntimeFiniteSectorAction

/-! The original target's logical fibre in a complete semantic source frame.
Gathering the target into the low logical digit preserves the actual owner
coordinates and all spectator/reference amplitudes.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSemanticSelectionFibre
open QleisliKernel QleisliKernel.Qirf
open Semantics.Finite (scatter gather)
open Semantics.FiniteCarrier (encoding tensor)
open Semantics.Exact (Matrix)
open QleisliKernel.FiniteRestriction (pack SectorEvaluationBinding)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (forestAxes)
open Qleisli.RuntimeSemanticForest (Frame Available ownerLayout owner_layout product frame_exists regroup_action)
open Qleisli.RuntimeSparseBlockEncoding (coefficient coefficient_scatter)
open Qleisli.RuntimeNamedHeadCoefficients (fibre applyHead head_code_action_total head_operator_encoding_total)
open Qleisli.RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (recode)
open Qleisli.Semantics.Exact (action)
open Qleisli.Semantics.RawAction (events)

private theorem product_singleton (target : Binding) : product [target] = ownerLayout target := by
  cases shape : ownerLayout target with
  | mk bits labels => simp [product,shape,tensor,Semantics.FiniteCarrier.singleton]

noncomputable def targetFibre {Reference : Type} (owners : Map) (target : Binding)
    (physicalFrame : List Nat) (base : Nat) (joint : Nat → Reference → ℂ) :
    Nat → Reference → ℂ :=
  let spectators := owners.erase target
  fibre (ownerLayout target).labels.length (product spectators).labels.length
    (coefficient spectators physicalFrame base)
    (fun logical ref => joint (recode (target::spectators) owners (sourceDimension owners) logical) ref)

/-- Overwriting the target axes acts only on the actual target code. The
correlated spectator fibre depends on the same base and original owner order. -/
theorem target_slice {owners : Map} (frame : Frame owners)
    (uniqueOwners : owners.Nodup) (target : Binding) (member : target ∈ owners)
    (physicalFrame : List Nat) (uniqueAxes : (forestAxes physicalFrame owners).Nodup)
    {Reference : Type} (joint : Nat → Reference → ℂ) (base row : Nat) (reference : Reference)
    (bound : row < 2^(ownerLayout target).bits) :
    Qleisli.RuntimeSemanticForest.action frame physicalFrame joint
        (scatter base (target.port.wires.map physicalFrame.idxOf) row) reference =
      action (encoding (ownerLayout target)) (targetFibre owners target physicalFrame base joint)
        row reference := by
  let spectators := owners.erase target
  let axes := target.port.wires.map physicalFrame.idxOf
  let otherAxes := forestAxes physicalFrame spectators
  let physical := scatter base axes row
  let orderedJoint := fun logical ref =>
    joint (recode (target::spectators) owners (sourceDimension owners) logical) ref
  have order : owners.Perm (target::spectators) := List.perm_cons_erase member
  obtain ⟨ordered⟩ : Nonempty (Frame ([target] ++ spectators)) :=
    frame_exists (fun b present => frame.available b (order.symm.subset present))
  have axesUnique : (axes ++ otherAxes).Nodup := by
    have reordered := ((order.flatMap_right (fun b : Binding => b.port.wires)).map physicalFrame.idxOf).nodup uniqueAxes
    simpa only [forestAxes,List.flatMap_cons,List.map_append,axes,otherAxes] using reordered
  have disjoint : otherAxes.Disjoint axes :=
    List.disjoint_left.mpr (fun axis other selected =>
      (List.nodup_append.mp axesUnique).2.2 axis selected axis other rfl)
  have width : axes.length = (ownerLayout target).bits :=
    (List.length_map _).trans (owner_layout (frame.available target member)).2
  have selected : gather physical (forestAxes physicalFrame [target]) = row := by
    change gather (scatter base axes row) (forestAxes physicalFrame [target]) = row
    simpa only [forestAxes,List.flatMap_cons,List.flatMap_nil,List.append_nil,axes] using
      Qleisli.RuntimeFiniteTargetScatter.gather_scatter base row axes
        (List.nodup_append.mp axesUnique).1 (width.symm ▸ bound)
  change Qleisli.RuntimeSemanticForest.action frame physicalFrame joint physical reference = _
  rw [regroup_action frame ordered order uniqueOwners]
  change Qleisli.RuntimeSemanticForest.action ordered physicalFrame orderedJoint physical reference = _
  rw [Qleisli.RuntimeSparseOperationAction.block_native_encoding ordered,head_code_action_total,
    selected,product_singleton]
  have stable : coefficient spectators physicalFrame physical = coefficient spectators physicalFrame base := by
    funext logical
    exact coefficient_scatter spectators physicalFrame axes disjoint base row logical
  rw [stable]
  rfl

/-- Reassemble the target fibre after a logical operation in the same
original full owner order. The input and output logical digits use the true
carrier cardinality, and the other owners' amplitudes remain correlated. -/
theorem target_update {owners : Map} (frame : Frame owners)
    (uniqueOwners : owners.Nodup) (target : Binding) (member : target ∈ owners)
    (physicalFrame : List Nat) (matrix : Matrix)
    (columns : matrix.cols = (ownerLayout target).labels.length)
    (rows : matrix.rows = (ownerLayout target).labels.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    Qleisli.RuntimeSemanticForest.action frame physicalFrame
        (RuntimeLiteralHistory.applySourceOwner owners owners target target matrix joint) physical reference =
      action (encoding (ownerLayout target))
        (fun digit ref => action matrix (targetFibre owners target physicalFrame physical joint) digit ref)
        (gather physical (target.port.wires.map physicalFrame.idxOf)) reference := by
  let spectators := owners.erase target
  let order := target::spectators
  let orderedJoint := fun logical ref => joint (recode order owners (sourceDimension owners) logical) ref
  have permutation : owners.Perm order := List.perm_cons_erase member
  obtain ⟨ordered⟩ : Nonempty (Frame ([target] ++ spectators)) :=
    frame_exists (fun b present => frame.available b (permutation.symm.subset present))
  have dimensions : sourceDimension ([target] ++ spectators) = sourceDimension owners := by
    funext binding
    change sourceDimension order binding = sourceDimension owners binding
    by_cases present : binding ∈ owners
    · simp only [sourceDimension,if_pos present,if_pos (permutation.mem_iff.mp present)]
    · simp only [sourceDimension,if_neg present,if_neg (fun found => present (permutation.mem_iff.mpr found))]
  have reorder := regroup_action ordered frame permutation.symm (permutation.nodup uniqueOwners)
    physicalFrame (applyHead matrix orderedJoint) physical reference
  rw [dimensions] at reorder
  rw [← show Qleisli.RuntimeSemanticForest.action ordered physicalFrame (applyHead matrix orderedJoint)
    physical reference = Qleisli.RuntimeSemanticForest.action frame physicalFrame
      (RuntimeLiteralHistory.applySourceOwner owners owners target target matrix joint) physical reference from reorder]
  rw [Qleisli.RuntimeSparseOperationAction.block_native_encoding ordered,product_singleton,
    head_operator_encoding_total _ _ _ _ _ _ _ rows.symm]
  have index : forestAxes physicalFrame [target] = target.port.wires.map physicalFrame.idxOf := by
    simp only [forestAxes,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [index]
  unfold targetFibre
  simp only [columns]
  rfl

theorem returned_axes
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) :
    let physicalFrame := frame.interval.after.quantum.frame
    let firstAxes := source.returned.first.port.wires.map physicalFrame.idxOf
    let secondAxes := source.returned.second.port.wires.map physicalFrame.idxOf
    forestAxes physicalFrame source.returned.toList = firstAxes ++ secondAxes ∧
      (firstAxes ++ secondAxes).Nodup := by
  intro physicalFrame firstAxes secondAxes
  let all := source.transport.after.bindings
  let returned := source.returned.toList
  have outputAxes := RuntimeTargetScatter.output_axes_unique frame source
  have partition := RuntimeSelectionPartition.source_output_partition frame source
  have pairAxes : forestAxes physicalFrame returned = firstAxes ++ secondAxes := by
    simp only [returned,forestAxes,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,
      firstAxes,secondAxes]
  have pairUnique : (firstAxes ++ secondAxes).Nodup := by
    have permuted := ((partition.flatMap_right (fun b : Binding => b.port.wires)).map physicalFrame.idxOf).symm.nodup outputAxes
    have appended : (forestAxes physicalFrame returned ++
        forestAxes physicalFrame (RuntimeSelectionPartition.complement all returned)).Nodup := by
      simpa only [all,returned,forestAxes,List.flatMap_append,List.map_append] using permuted
    exact pairAxes ▸ (List.nodup_append.mp appended).1
  exact ⟨pairAxes,pairUnique⟩

theorem native_owner_layout {binding : Binding}
    (available : Nonempty (RuntimeStructuralLayoutEvidence.SemanticOwnerLayout binding))
    {basis : Semantics.FiniteCarrier.Basis} (same : binding.owner.basis = basis)
    {bits : Nat} {labels : List Nat}
    (read : RuntimeInterval.Computed (FiniteCarrier.read basis) ⟨bits,labels⟩) :
    ownerLayout binding = ⟨bits,labels⟩ := by
  have original := (owner_layout available).1
  rw [same] at original
  obtain ⟨work,left,ran⟩ := read
  exact Option.some.inj (original.symm.trans (FiniteCarrier.read_reference _ _ work left ran))

theorem unique_bindings {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    checked.bindings.Nodup :=
  List.Pairwise.of_map (fun b : Binding => b.port.token)
    (fun _ _ different same => different (congrArg (fun b : Binding => b.port.token) same))
    checked.tokensDistinct

/-- The original ordered caller events at an actual checked label apply its
logical target action through the real rectangular target encoding. -/
theorem logical_sector_action
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    {labels : List Nat}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (before : Frame codes.owners.before.bindings) :
    ∃ trace : RuntimeSelectionTraceEvidence.TraceEvidence frame codes.owners selectorBits targetBits retained restricted,
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference)
      {label row : Nat} {required logical : Matrix},
      NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,required) logical →
      row < outputCode.rows →
      gather physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) =
        pack selectorBits label row →
      let base := scatter physical
        (codes.owners.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) label
      events dependencies trace.traceResult.events
        (fun input => Qleisli.RuntimeSemanticForest.action before frame.interval.before.quantum.frame joint input reference)
        physical =
      action outputCode (fun digit ref => action required
        (targetFibre codes.owners.transport.after.bindings codes.owners.returned.second
          frame.interval.after.quantum.frame base joint) digit ref) row reference := by
  obtain ⟨trace,after,sectorAction⟩ :=
    RuntimeSemanticSelectionGeometry.semantic_sector_action frame codes.owners restricted before
  let all := codes.owners.transport.after.bindings
  let returned := codes.owners.returned.toList
  let physicalFrame := frame.interval.after.quantum.frame
  let first := codes.owners.returned.first
  let second := codes.owners.returned.second
  let firstAxes := first.port.wires.map physicalFrame.idxOf
  let secondAxes := second.port.wires.map physicalFrame.idxOf
  have outputAxes := RuntimeTargetScatter.output_axes_unique frame codes.owners
  obtain ⟨pairAxes,pairUnique⟩ := returned_axes frame codes.owners
  have selected := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have firstMember : first ∈ all := selected.1 (by simp [first])
  have secondMember : second ∈ all := selected.1 (by simp [second])
  have owners : first.owner = selector ∧ second.owner = target := by
    simpa only [first,second,List.map_cons,List.map_nil,List.cons.injEq,and_true] using selected.2
  have selectorLayout := native_owner_layout (after.available first firstMember) (congrArg (·.basis) owners.1)
    layouts.selectorRead
  have firstBits := congrArg Semantics.FiniteCarrier.Layout.bits selectorLayout
  have firstWidth : firstAxes.length = selectorBits :=
    (List.length_map _).trans ((owner_layout (after.available first firstMember)).2.trans firstBits)
  obtain ⟨targetLayout,targetReference,_targetBits,inputNative,_outputNative,_inputGram,_outputGram⟩ :=
    RuntimeFiniteTargetCode.target_codes frame codes layouts
  have secondLayout := (owner_layout (after.available second secondMember)).1
  rw [owners.2] at secondLayout
  have inputEncoding : inputCode = encoding (ownerLayout second) :=
    inputNative.trans (congrArg encoding (Option.some.inj (targetReference.symm.trans secondLayout)))
  have uniqueOwners : all.Nodup := unique_bindings codes.owners.transport.after
  refine ⟨trace,?_⟩
  intro Reference joint physical reference label row required logical binding rowBound coordinate base
  obtain ⟨sector,found,checked,sameLogical⟩ := Qleisli.NominalSector.logical_binding_map binding
  have physicalBound : row < sector.rows := checked.physicalShape.2.symm ▸ rowBound
  obtain ⟨work,left,read⟩ := restricted
  have read := Raw.Sector.read_bound dependencies [.bits selectorBits] [.bits targetBits]
    (RuntimePureInterval.fragment frame.selected frame.operations outputs) retained work left read
  have inside := (List.getElem?_eq_some_iff.mp found).1
  rw [QleisliKernel.Exact.listRel_length _ _ _ read.2.2.2.2.2.2.2,List.length_range] at inside
  have labelBound : label < 2^firstAxes.length := by
    simpa only [firstWidth,Semantics.Finite.width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Nat.add_zero] using inside
  have sliced (input : Nat) (bound : input < sector.cols) :
      Qleisli.RuntimeSemanticForest.action after physicalFrame joint
        (scatter physical (forestAxes physicalFrame returned) (pack selectorBits label input)) reference =
      action inputCode (targetFibre all second physicalFrame base joint) input reference := by
    have inputBound : input < 2^(ownerLayout second).bits := by
      rw [checked.physicalShape.1,inputEncoding] at bound
      exact bound
    rw [pairAxes]
    have split := RuntimeFiniteSectorAction.scatter_pair physical label input firstAxes secondAxes pairUnique labelBound
    rw [firstWidth] at split
    rw [split]
    exact (target_slice after uniqueOwners second secondMember physicalFrame outputAxes joint base input reference
      inputBound).trans (congrArg (fun matrix => action matrix (targetFibre all second physicalFrame base joint)
        input reference) inputEncoding.symm)
  have actual := sectorAction joint physical reference found physicalBound coordinate
  calc
    _ = action sector
        (fun input ref => Qleisli.RuntimeSemanticForest.action after physicalFrame joint
          (scatter physical (forestAxes physicalFrame returned) (pack selectorBits label input)) ref) row reference :=
      actual
    _ = action sector (fun input ref => action inputCode
        (targetFibre all second physicalFrame base joint) input ref) row reference := by
      unfold action
      apply Qleisli.Exact.sum_map_congr
      intro input member
      exact congrArg (fun value => Qleisli.Semantics.Exact.entry sector row input * value)
        (sliced input (List.mem_range.mp member))
    _ = _ := by
      simpa only [sameLogical,binding.1] using
        Qleisli.CodeSpace.map_reference_action checked (targetFibre all second physicalFrame base joint)
          row reference physicalBound

/-- A coordinate outside an original owner's support makes the complete
encoding vanish, even when its joint input is correlated with every other owner. -/
theorem owner_padding_zero {owners : Map} (frame : Frame owners)
    (uniqueOwners : owners.Nodup) (owner : Binding) (member : owner ∈ owners)
    (physicalFrame : List Nat) {Reference : Type} (joint : Nat → Reference → ℂ)
    (physical : Nat) (reference : Reference)
    (padding : gather physical (owner.port.wires.map physicalFrame.idxOf) ∉ (ownerLayout owner).labels) :
    Qleisli.RuntimeSemanticForest.action frame physicalFrame joint physical reference = 0 := by
  unfold Qleisli.RuntimeSemanticForest.action
  calc
    _ = ((List.range frame.code.dimension).map fun _ => (0 : ℂ)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro digit present
      have empty : Qleisli.Semantics.Exact.scalar
          (RuntimeForestCode.embed physicalFrame owners frame.code physical digit) = 0 := by
        by_contra nonzero
        have support := RuntimeSemanticForest.owner_support frame uniqueOwners owner member physicalFrame physical
          digit (List.mem_range.mp present) nonzero
        exact padding (List.mem_of_getElem? support.2)
      rw [empty,zero_mul]
    _ = 0 := by simp

/-- The real sector on selector padding acts on the zero encoded fibre.
There is no source arm for that coordinate and no substitution of its sector. -/
theorem padding_sector_action
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    (restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs [selector,target])
    {labels : List Nat}
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (before : Frame source.before.bindings) :
    ∃ trace : RuntimeSelectionTraceEvidence.TraceEvidence frame source selectorBits targetBits retained restricted,
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference),
      gather physical (source.returned.first.port.wires.map frame.interval.after.quantum.frame.idxOf) ∉ labels →
      events dependencies trace.traceResult.events
        (fun input => Qleisli.RuntimeSemanticForest.action before frame.interval.before.quantum.frame joint input reference)
        physical = 0 := by
  obtain ⟨trace,after,sectorAction⟩ :=
    RuntimeSemanticSelectionGeometry.semantic_sector_action frame source restricted before
  let all := source.transport.after.bindings
  let physicalFrame := frame.interval.after.quantum.frame
  let first := source.returned.first
  let second := source.returned.second
  let firstAxes := first.port.wires.map physicalFrame.idxOf
  let secondAxes := second.port.wires.map physicalFrame.idxOf
  let pair := forestAxes physicalFrame source.returned.toList
  obtain ⟨axes,unique⟩ := returned_axes frame source
  have ordered := RuntimeSelectionPartition.order_values _ _ _ source.returned.ordered
  have firstMember : first ∈ all := ordered.1 (by simp [first])
  have secondMember : second ∈ all := ordered.1 (by simp [second])
  have owners : first.owner = selector ∧ second.owner = target := by
    simpa only [first,second,List.map_cons,List.map_nil,List.cons.injEq,and_true] using ordered.2
  have selectorLayout := native_owner_layout (after.available first firstMember) (congrArg (·.basis) owners.1)
    layouts.selectorRead
  obtain ⟨targetLabels,targetRead⟩ := layouts.targetRead
  have targetLayout := native_owner_layout (after.available second secondMember) (congrArg (·.basis) owners.2)
    targetRead
  have firstWidth : firstAxes.length = selectorBits := (List.length_map _).trans
    ((owner_layout (after.available first firstMember)).2.trans
      (congrArg Semantics.FiniteCarrier.Layout.bits selectorLayout))
  have secondWidth : secondAxes.length = targetBits := (List.length_map _).trans
    ((owner_layout (after.available second secondMember)).2.trans
      (congrArg Semantics.FiniteCarrier.Layout.bits targetLayout))
  have uniqueOwners := unique_bindings source.transport.after
  refine ⟨trace,?_⟩
  intro Reference joint physical reference padding
  let label := gather physical firstAxes
  let row := gather physical secondAxes
  have labelBound : label < 2^firstAxes.length := RuntimeForestProduct.gather_bound physical firstAxes
  have rowBound : row < 2^targetBits := secondWidth ▸ RuntimeForestProduct.gather_bound physical secondAxes
  have coordinate : gather physical pair = pack selectorBits label row := by
    change gather physical (forestAxes physicalFrame source.returned.toList) = _
    rw [axes,RuntimeForestProduct.gather_append,firstWidth]
    rfl
  obtain ⟨work,left,ran⟩ := restricted
  have read := Raw.Sector.read_bound dependencies [.bits selectorBits] [.bits targetBits]
    (RuntimePureInterval.fragment frame.selected frame.operations outputs) retained work left ran
  have sectors : QleisliKernel.Exact.ListRel
      (SectorEvaluationBinding dependencies selectorBits [.bits targetBits] retained.steps)
      (List.range (2^selectorBits)) retained.sectors := by
    simpa only [Semantics.Finite.width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using
      read.2.2.2.2.2.2.2
  have inside : label < retained.sectors.length := by
    rw [QleisliKernel.Exact.listRel_length _ _ _ sectors,List.length_range]
    exact firstWidth ▸ labelBound
  let sector := retained.sectors[label]'inside
  have found : retained.sectors[label]? = some sector := List.getElem?_eq_getElem inside
  obtain ⟨_,localSteps,beforeWork,afterWork,_,_,reconstructed,_,_⟩ := Qleisli.NominalSector.indexed_sector sectors found
  obtain ⟨_,_,_,matrix⟩ := QleisliKernel.Finite.circuitMatrix_columns dependencies
    ⟨[.bits targetBits],localSteps⟩ sector beforeWork afterWork reconstructed
  have rows : sector.rows = 2^targetBits := by
    simpa only [Semantics.Finite.width,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using
      congrArg Matrix.rows matrix
  have disjoint : firstAxes.Disjoint secondAxes :=
    List.disjoint_left.mpr (fun axis low high => (List.nodup_append.mp unique).2.2 axis low axis high rfl)
  have zeroSlice (input : Nat) :
      Qleisli.RuntimeSemanticForest.action after physicalFrame joint
        (scatter physical pair (pack selectorBits label input)) reference = 0 := by
    have split : scatter physical pair (pack selectorBits label input) =
        scatter (scatter physical firstAxes label) secondAxes input := by
      change scatter physical (forestAxes physicalFrame source.returned.toList) _ = _
      rw [axes]
      simpa only [firstWidth] using
        RuntimeFiniteSectorAction.scatter_pair physical label input firstAxes secondAxes unique labelBound
    apply owner_padding_zero after uniqueOwners first firstMember physicalFrame joint _ reference
    change gather (scatter physical pair (pack selectorBits label input)) firstAxes ∉ (ownerLayout first).labels
    rw [split,RuntimeTargetScatter.gather_disjoint _ input secondAxes firstAxes disjoint,
      RuntimeFiniteTargetScatter.gather_scatter physical label firstAxes (List.nodup_append.mp unique).1 labelBound,
      selectorLayout]
    exact padding
  have actual := sectorAction joint physical reference found (rows.symm ▸ rowBound) coordinate
  refine actual.trans ?_
  unfold action
  calc
    _ = ((List.range sector.cols).map fun _ => (0 : ℂ)).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro input _
      change Qleisli.Semantics.Exact.entry sector row input *
        Qleisli.RuntimeSemanticForest.action after physicalFrame joint
          (scatter physical pair (pack selectorBits label input)) reference = 0
      rw [zeroSlice,mul_zero]
    _ = 0 := by simp

#print axioms padding_sector_action
#print axioms owner_padding_zero
#print axioms target_slice
#print axioms target_update
#print axioms logical_sector_action
end Qleisli.RuntimeSemanticSelectionFibre
