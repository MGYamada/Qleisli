import QleisliKernel.SourceTypes.MemberFields

/-! Uncompiled bounded probes. These are expected results, not validation evidence.
No native acceptance or source-expression privacy verdict is exercised.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace MemberFieldExamples
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.SourceTypes.MemberFields
open QleisliKernel.Semantics.FiniteCarrier

local instance exceptDecidableEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error first, .error second =>
      if equal : first = second then .isTrue (by cases equal; rfl)
      else .isFalse (by intro result; cases result; exact equal rfl)
  | .ok first, .ok second =>
      if equal : first = second then .isTrue (by cases equal; rfl)
      else .isFalse (by intro result; cases result; exact equal rfl)
  | .error _, .ok _ => .isFalse (by intro result; cases result)
  | .ok _, .error _ => .isFalse (by intro result; cases result)

def plain : String := "pub enum Tri { A, B, C }\npub struct Empty {}\npub struct Packet { pub zero: Unit, pub bit: Bit, pub pad: Bits<0> }\n"
def sources : Sources := #[("owner",plain)]
def summary := ((readOriginalFields sources "owner" "Packet").run 2000000).1.map fun result =>
  result.fields.map fun field => (field.member.name.text,field.member.isPublic,field.basis)

theorem exact_fields : summary = .ok [
    ("zero",true,[.unit]),("bit",true,[.bit]),("pad",true,[.bits 0])] := by decide +kernel

-- Missing or equal-width substituted nodes are not the returned logical tree.
example : summary ≠ .ok [("bit",true,[.bit]),("pad",true,[.bits 0])] := by
  rw [exact_fields]
  decide
example : summary ≠ .ok [
    ("zero",true,[.bits 0]),("bit",true,[.bit]),("pad",true,[.bits 0])] := by
  rw [exact_fields]
  decide
example : summary ≠ .ok [
    ("bit",true,[.bit]),("zero",true,[.unit]),("pad",true,[.bits 0])] := by
  rw [exact_fields]
  decide
example : (((readOriginalFields sources "owner" "Empty").run 2000000).1.map
    (fun result => result.fields)) = .ok [] := by decide +kernel
example : ((readOriginalFields sources "owner" "Tri").run 2000000).1.isOk = false := by decide +kernel
example : ((readOriginalFields sources "owner" "Packet").run 0).1.isOk = false := by decide +kernel
example : ((readOriginalFields #[("owner",plain),("owner",plain)] "owner" "Packet").run
    2000000).1.isOk = false := by decide +kernel

def aliased : Sources := #[("sizes","pub static fn zero() -> Nat { 0 }\n"),("bridge","pub use sizes::zero;\n"),
  ("owner","use bridge::zero;\npub struct Packet { pub bit: Bit, hidden: Bits<zero()> }\n"),("facade","pub use owner::Packet;\n")]
def aliasSummary := ((readOriginalFields aliased "owner" "Packet").run 2000000).1.map fun result =>
  (result.original.origin.moduleName,result.fields.map fun field =>
    (field.member.name.text,field.member.isPublic,field.basis))

-- The private zero-width field retains both its marker and its exact node.
example : aliasSummary = .ok ("owner",[
    ("bit",true,[.bit]),("hidden",false,[.bits 0])]) := by decide +kernel

-- Import resolution preserves canonical ownership; it does not authenticate app.
example : (((resolveReference aliased "app" ["facade","::","Packet"]).run 2000000).1.map
    (fun resolved => resolved.moduleName)) = .ok "owner" := by decide +kernel

-- Pure policy counterexample: a reexporting module is not a private-field owner.
def hidden : Members.Member := ⟨⟨"hidden",⟨0,6⟩⟩,false,some [],⟨0,6⟩⟩
def owner : Origin := ⟨"owner","Packet","use bridge::zero;\npub struct Packet { pub bit: Bit, hidden: Bits<zero()> }\n"⟩
example : VisibleFrom "owner" owner hidden := Or.inr rfl
example : ¬ VisibleFrom "facade" owner hidden := by
  simp [VisibleFrom,hidden,owner]
example : ¬ VisibleFrom "app" owner hidden := by
  simp [VisibleFrom,hidden,owner]
end MemberFieldExamples
