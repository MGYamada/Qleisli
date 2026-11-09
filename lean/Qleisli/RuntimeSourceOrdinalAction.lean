import Qleisli.RuntimeMultiwayGram
import Qleisli.RuntimeNamedSelectionWholeOutput

/-! Evaluate the written selection table in source owner coordinates.
The retained code serves only to prove that this source action describes
the exact finite domain of the original physical occurrence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSourceOrdinalAction
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.Exact (Matrix)
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode (Frame)
open RuntimeOwnerCodeReindex (dimensionAt)
open Qleisli.RuntimeForestRegroup (sourceDimension dimensionAt_source frame_volume)
open Qleisli.RuntimeMultiwayGram (OrdinalTable selectorIndex ordinalAction)
open Qleisli.RuntimeNamedSelectionWholeOutput (onFinite)
open Qleisli.MixedRadix (decode encode volume)

noncomputable def sourceAction {Reference : Type} (order : Map) (selector target : Binding)
    (arms : List Matrix) (joint : Nat → Reference → ℂ) (logical : Nat) (ref : Reference) : ℂ :=
  let cards := sourceDimension order
  let digit := decode order cards logical
  if logical < volume order cards then
    match arms[digit selector]? with
    | none => 0
    | some arm =>
      Qleisli.Semantics.Exact.action arm
        (fun col => joint (encode order cards fun owner => if owner = target then col else digit owner))
        (digit target) ref
  else 0

/-- The source coordinate calculation and the action on the same retained
finite owner code agree pointwise, including the exact domain boundary. -/
theorem onFinite_ordinalAction {roles state checked labels arms inputCode outputCode sectors}
    (frame : @Frame roles state checked) (selector target : Binding)
    (member : selector ∈ checked.bindings)
    (table : OrdinalTable inputCode outputCode sectors labels arms)
    (card : dimensionAt frame.owners selector = labels.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) :
    onFinite (ordinalAction frame selector target member table card joint) =
      sourceAction checked.bindings selector target arms joint := by
  funext logical ref
  have cards : dimensionAt frame.owners = sourceDimension checked.bindings :=
    funext (dimensionAt_source frame.owners)
  have domain : volume checked.bindings (sourceDimension checked.bindings) = frame.code.dimension := by
    rw [← cards,frame_volume]
  dsimp only [onFinite,sourceAction]
  rw [domain]
  by_cases inside : logical < frame.code.dimension
  · rw [dif_pos inside,if_pos inside]
    let ordinal := selectorIndex frame selector member card ⟨logical,inside⟩
    have index : decode checked.bindings (sourceDimension checked.bindings) logical selector = ordinal.val := by
      rw [← cards]
      rfl
    have found : arms[ordinal.val]? = some (table.arm ordinal) :=
      List.getElem?_eq_getElem (by rw [table.count]; exact ordinal.isLt)
    rw [index,found]
    unfold ordinalAction RuntimeTargetDigit.update
    simp only [cards]
    rfl
  · rw [dif_neg inside,if_neg inside]

#print axioms onFinite_ordinalAction
end Qleisli.RuntimeSourceOrdinalAction
