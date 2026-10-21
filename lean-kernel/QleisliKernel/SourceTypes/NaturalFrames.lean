import QleisliKernel.SourceTypes.NaturalCatalog
import QleisliKernel.SourceTypes.NaturalNormalize
import QleisliKernel.SourceTypes.NaturalSubstitute

/-! Original formal identities in canonical affine order. Original ordinals
retain positional calls; sorting matches BinderKey's name-first iteration without
confusing binders from separate original declarations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.NaturalFrames
open Semantics.SourceNatural Semantics.SourceAffine NaturalAffine NaturalPredicates

structure Binder where
  owner : NaturalCatalog.Key
  ordinal : Nat
  name : String
  deriving BEq, DecidableEq, Repr

structure Frame where
  binders : List Binder

def original (helper : NaturalCatalog.Original) : Frame :=
  let binders := helper.helper.parameters.zipIdx.map fun (name,ordinal) =>
    (⟨helper.key,ordinal,name⟩ : Binder)
  ⟨binders.mergeSort (fun a b => a.name ≤ b.name)⟩

def lookup (frame : Frame) (path : Path) : Option Nat := do
  let [name] := path | none
  let (_,position) ← frame.binders.zipIdx.find? (fun (binder,_) => binder.name == name)
  return position

def names (frame : Frame) (values : Valuation) (path : Path) : Option Nat :=
  (lookup frame path).map (fun position => (values position).toNat)

def Natural (frame : Frame) (values : Valuation) : Prop :=
  ∀ position,position < frame.binders.length → 0 ≤ values position

/-- A positional caller list is interpreted at original formal ordinals, even
though the affine coefficient frame has canonical name-first order. -/
def argumentValues (frame : Frame) (arguments : List Nat) : Valuation := fun position =>
  match frame.binders[position]? with
  | none => 0
  | some binder => (arguments[binder.ordinal]?.getD 0 : Nat)

theorem argumentValues_natural (frame : Frame) (arguments : List Nat) :
    Natural frame (argumentValues frame arguments) := by
  intro position _bound
  unfold argumentValues
  split <;> omega

def replacements (frame : Frame) (arguments : List Form) : List Form :=
  frame.binders.map (fun binder => arguments[binder.ordinal]?.getD ⟨0,[]⟩)

private theorem related_get (forms : List Form) (numbers : List Nat) (values : Valuation)
    (related : Related (fun (form : Form) (n : Nat) => form.evaluate values = (n : Int)) forms numbers)
    (position : Nat) :
    (forms[position]?.getD ⟨0,[]⟩).evaluate values = (numbers[position]?.getD 0 : Nat) := by
  induction related generalizing position with
  | nil => rfl
  | cons head _ ih =>
    cases position with
    | zero => exact head
    | succ position => exact ih position

theorem replacements_meaning (frame : Frame) (arguments : List Form) (numbers : List Nat)
    (values : Valuation)
    (related : Related (fun (form : Form) (n : Nat) => form.evaluate values = (n : Int)) arguments numbers) :
    NaturalSubstitute.replacementValues (replacements frame arguments) values =
      argumentValues frame numbers := by
  funext position
  simp only [NaturalSubstitute.replacementValues,replacements,List.getElem?_map]
  cases found : frame.binders[position]? with
  | none => simp [argumentValues,found]
  | some binder =>
    simp only [found,Option.map_some,Option.getD_some,argumentValues]
    exact related_get _ _ _ related binder.ordinal

def initial (frame : Frame) : WorkM (Context (Natural frame)) := do
  Finite.guard (frame.binders.length ≤ 32) .limit
  Finite.exactWork (Exact.charge (frame.binders.length*(frame.binders.length+3)+1))
  let rows := (List.range frame.binders.length).map (fun position =>
    (coordinate frame.binders.length position).scale (-1))
  let _ ← rows.mapM valid
  return ⟨[rows],by
    intro values
    rw [satisfies_singleton]
    constructor
    · intro held position bound
      have member : (coordinate frame.binders.length position).scale (-1) ∈ rows :=
        List.mem_map.mpr ⟨position,List.mem_range.mpr bound,rfl⟩
      have negative := held _ member
      rw [Form.evaluate_scale,coordinate_evaluate] at negative
      omega
    · intro held row member
      obtain ⟨position,bound,same⟩ := List.mem_map.mp member
      subst row
      rw [Form.evaluate_scale,coordinate_evaluate]
      have nonnegative := held position (List.mem_range.mp bound)
      omega⟩

def readName {meaning : Valuation → Prop} (frame : Frame) (calls : Calls)
    (natural : ∀ values,meaning values → Natural frame values) (fuel : Nat) (path : Path) :
    WorkM (NaturalNormalize.Result (names frame) calls meaning (fuel+1) (.name path)) := do
  Finite.exactWork (Exact.charge ((path.map String.utf8ByteSize).sum+
    (frame.binders.map (fun b => b.name.utf8ByteSize+1)).sum+1))
  match found : lookup frame path with
  | none => throw .request
  | some position =>
    if bound : position < frame.binders.length then
      let result ← witness (parameter frame.binders.length position)
      return ⟨result.val,by
        intro values held
        refine ⟨(values position).toNat,?_,?_⟩
        · change names frame values path = some (values position).toNat
          simp only [names,found,Option.map_some]
        · obtain ⟨work,left,ok⟩ := result.property
          rw [parameter_meaning _ _ _ _ _ ok]
          exact (Int.toNat_of_nonneg (natural values held position bound)).symm⟩
    else throw .request

end QleisliKernel.SourceTypes.NaturalFrames
