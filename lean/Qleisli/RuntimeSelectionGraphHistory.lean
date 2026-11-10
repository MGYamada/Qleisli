import Qleisli.RuntimeSelectionGraphSource
import Qleisli.RuntimeSemanticSelectionSource

/-! Substitute independently evaluated original arm coefficients in the
coherent source history, keeping the actual source ordinal and owner digits.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSelectionGraphHistory
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes
open Semantics.Exact (Matrix)
open RuntimeOwnerMap (Binding Map)
open RuntimeSelectionSteps (Edge)
open RuntimeSelectionLogicalRead (FromArms)
open RuntimeSelectionGraphSource (ArmEvaluated ArmEvaluatedWith)
open RuntimeSemanticForest (Frame ownerLayout owner_layout)
open RuntimeForestRegroup (sourceDimension)
open Qleisli.MixedRadix (decode encode volume)
open RuntimeGraphCoefficients (Coefficient)
open Qleisli.Semantics.Exact (action entry)

def Coefficients (matrix : Matrix) (source : Coefficient) : Prop :=
  ∀ row col, row < matrix.rows → col < matrix.cols → source row col = entry matrix row col

theorem ArmEvaluatedWith.coefficients {artifact : Artifact} {catalogue root scope owner name offset selector target}
    {table : QuantumArms.Table artifact.sources owner name offset selector target}
    {index : Fin table.arms.length} {matrix : Matrix} {source : Coefficient}
    (arm : ArmEvaluatedWith catalogue root scope table index matrix source) : Coefficients matrix source := by
  obtain ⟨⟨_,_,_⟩,evidence,_,same,_,agrees⟩ := arm
  rw [same]
  exact agrees.coefficient

def OrderedCoefficients {artifact : Artifact} (catalogue : GenericCatalogue.Checked artifact.sources)
    (root : Validity.Root) (scope : List Edge) {owner name offset selector target}
    (table : QuantumArms.Table artifact.sources owner name offset selector target)
    (ordinals : List Nat) (matrices : List Matrix) (sources : List Coefficient) : Prop :=
  List.Forall₂ Coefficients matrices sources ∧
  List.Forall₂ (fun ordinal pair => ∃ index, table.arms[index].label.ordinal = ordinal ∧
    ArmEvaluatedWith catalogue root scope table index pair.1 pair.2) ordinals (matrices.zip sources)

theorem ordered_coefficients {artifact : Artifact} {catalogue root scope owner name offset selector target}
    {table : QuantumArms.Table artifact.sources owner name offset selector target}
    {ordinals : List Nat} {matrices : List Matrix}
    (original : QleisliKernel.Exact.ListRel (fun ordinal matrix =>
      ∃ index, table.arms[index].label.ordinal = ordinal ∧ ArmEvaluated catalogue root scope table index matrix)
      ordinals matrices) :
    ∃ sources, OrderedCoefficients catalogue root scope table ordinals matrices sources := by
  induction ordinals generalizing matrices with
  | nil =>
    cases matrices with
    | nil => exact ⟨[],.nil,.nil⟩
    | cons _ _ => cases original
  | cons ordinal rest ih =>
    cases matrices with
    | nil => cases original
    | cons matrix tail =>
      obtain ⟨index,same,source,evaluated⟩ := original.1
      obtain ⟨sources,related,ordered⟩ := ih original.2
      exact ⟨source::sources,.cons (ArmEvaluatedWith.coefficients evaluated) related,
        .cons ⟨index,same,evaluated⟩ ordered⟩

theorem table_coefficients {artifact : Artifact} {catalogue root scope owner name offset selector target}
    {table : QuantumArms.Table artifact.sources owner name offset selector target}
    {ordinals : List Nat} {matrices : List Matrix}
    (original : QleisliKernel.Exact.ListRel (fun ordinal matrix =>
      ∃ index, table.arms[index].label.ordinal = ordinal ∧ ArmEvaluated catalogue root scope table index matrix)
      ordinals matrices) :
    ∃ sources, List.Forall₂ Coefficients matrices sources := by
  obtain ⟨sources,related,_⟩ := ordered_coefficients original
  exact ⟨sources,related⟩

noncomputable def sourceAction {Reference : Type} (order : Map) (selector target : Binding)
    (arms : List Coefficient) (joint : Nat → Reference → ℂ) (logical : Nat) (ref : Reference) : ℂ :=
  let cards := sourceDimension order
  let digit := decode order cards logical
  if logical < volume order cards then
    match arms[digit selector]? with
    | none => 0
    | some arm =>
      ((List.range (cards target)).map fun col => arm (digit target) col *
        joint (encode order cards fun owner => if owner = target then col else digit owner) ref).sum
  else 0

private theorem paired_at {matrices : List Matrix} {sources : List Coefficient}
    (related : List.Forall₂ Coefficients matrices sources) (index : Nat) :
    match matrices[index]?,sources[index]? with
    | some matrix,some source => Coefficients matrix source
    | none,none => True
    | _,_ => False := by
  induction related generalizing index with
  | nil => trivial
  | cons head _ ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih index

/-- Source evaluation on the logical owner order can use the original
coefficient operators in place of the checked matrices. -/
theorem source_action_eq {Reference : Type} {order : Map} (frame : Frame order)
    (selector target : Binding) (member : target ∈ order)
    {matrices : List Matrix} {sources : List Coefficient}
    (related : List.Forall₂ Coefficients matrices sources)
    (shape : ∀ matrix ∈ matrices, matrix.rows = sourceDimension order target ∧
      matrix.cols = sourceDimension order target)
    (joint : Nat → Reference → ℂ) :
    sourceAction order selector target sources joint =
      RuntimeSourceOrdinalAction.sourceAction order selector target matrices joint := by
  funext logical ref
  let cards := sourceDimension order
  let digit := decode order cards logical
  unfold sourceAction RuntimeSourceOrdinalAction.sourceAction
  by_cases inside : logical < volume order (sourceDimension order)
  · simp only [if_pos inside]
    change (match sources[digit selector]? with
      | none => 0
      | some arm => ((List.range (cards target)).map fun col => arm (digit target) col *
          joint (encode order cards fun owner => if owner = target then col else digit owner) ref).sum) =
      (match matrices[digit selector]? with
      | none => 0
      | some arm => action arm
          (fun col => joint (encode order cards fun owner => if owner = target then col else digit owner))
          (digit target) ref)
    have each := paired_at related (digit selector)
    cases written : matrices[digit selector]? <;> cases actual : sources[digit selector]? <;>
      simp only [written,actual] at each ⊢
    rename_i matrix source
    have dims := shape matrix (List.mem_of_getElem? written)
    change matrix.rows = cards target ∧ matrix.cols = cards target at dims
    have positive (binding : Binding) (present : binding ∈ order) : 0 < cards binding := by
      have available := (owner_layout (frame.available binding present)).1
      simpa only [cards,sourceDimension,if_pos present,Semantics.FiniteCarrier.dimension,available,
        Option.map_some,Option.getD_some] using (RuntimeForestProduct.layout_bounds _ _ available).1
    have rowBound : digit target < matrix.rows := by
      rw [dims.1]
      exact MixedRadix.decode_bound order cards logical positive inside target member
    unfold action
    rw [← dims.2]
    apply Qleisli.Exact.sum_map_congr
    intro col present
    rw [each _ _ rowBound (List.mem_range.mp present)]
  · simp only [if_neg inside]

#print axioms table_coefficients
#print axioms source_action_eq
end Qleisli.RuntimeSelectionGraphHistory
