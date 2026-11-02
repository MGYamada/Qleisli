import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.SourceComputedSyntax

/-! Actual scoped owner/environment preparation for compute/use/uncompute.
Returning typed owners supplies no clean-release or computed-relation equation.
Those exact native obligations remain mandatory for either source form.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeComputed
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues
open Semantics.SourceOwners

def offset {tokens} (written : SourceComputedSyntax.Checked tokens) : Nat :=
  written.parts.header.calleeOffset

def names {tokens} (written : SourceComputedSyntax.Checked tokens) : List String :=
  written.parts.data.toList.map (·.text) ++ [written.parts.auxiliary.text]

structure Initial where
  auxiliary : Owner
  environment : Environment
  nextOrdinal : Nat
  heldData : List Owner
  deriving DecidableEq, Repr

def prepare {tokens} (written : SourceComputedSyntax.Checked tokens) (input : Owner)
    (remaining : Environment) (nextOrdinal : Nat) (staticNames : List String) : Except String Initial := do
  if !(names written).all (fun name => !staticNames.contains name) then
    throw "computed scope binder shadows an original static formal"
  let auxiliary : Owner := ⟨nextOrdinal,[.bit]⟩
  let (visible,heldData) ← match written.parts.logical,written.parts.data with
    | none,none => pure (remaining.filter (fun cell => (valueOwners cell.value).isEmpty),[input])
    | some _,some data => do
      let visible ← bind [data.text] [.owner input] [] (.computedData (offset written))
      pure (visible,[])
    | _,_ => throw "computed scope source binder shape"
  let initial ← bind [written.parts.auxiliary.text] [.owner auxiliary] visible (.computedAuxiliary (offset written))
  return ⟨auxiliary,initial,nextOrdinal+1,heldData⟩

structure Returned (input : Owner) where
  data : Owner
  auxiliary : Owner
  dataType : data.basis = input.basis
  auxiliaryType : auxiliary.basis = [.bit]

def returned {tokens} (written : SourceComputedSyntax.Checked tokens) (input : Owner) (value : Value) :
    Except String (Returned input) := do
  match written.parts.logical,value with
  | none,[.owner auxiliary] =>
    if typed : auxiliary.basis = [.bit] then return ⟨input,auxiliary,rfl,typed⟩
    else throw "protected computed body must return one exact Bit owner"
  | some _,[.tuple 2,.owner data,.owner auxiliary] =>
    if typed : data.basis = input.basis ∧ auxiliary.basis = [.bit] then
      if data.ordinal == auxiliary.ordinal then throw "certified computed result owners alias"
      return ⟨data,auxiliary,typed.1,typed.2⟩
    else throw "certified computed body must return its complete ordered data/Bit types"
  | _,_ => throw "computed body original result owner shape"

end QleisliKernel.SourceTypes.SourceRuntimeComputed
