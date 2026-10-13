import Protocol.ExecutionView.Graph

/-! Original caller alias descriptions from the same fresh native receipts.
Indices propose bindings; no host snapshot/cache assertion is accepted here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.ExecutionView.Caller
open QleisliKernel.Semantics QleisliKernel.Finite

def maxAliases : Nat := 1000000

private def record (tag : String) (fields : List Value) : Value :=
  .array (.text tag :: fields)

/-- Repeated indices describe distinct actual caller aliases against the same
fresh receipt. A missing original slot cannot mint replacement evidence. -/
def alias (root : Qirf.Validity.Root) (index : Nat) : WorkM Value := do
  let receipt ← lift (readOption ((root.receipts[index]?).join))
  let description ← FiniteView.functionEvidence receipt
  return record "evidence-alias" [.natural index,description]

theorem alias_bound (root : Qirf.Validity.Root) (index : Nat)
    (value : Value) (work left : Nat)
    (ok : (alias root index).run work = (.ok value,left)) :
    ∃ receipt description,
      root.receipts[index]? = some (some receipt) ∧
      (FiniteView.functionEvidence receipt).run work = (.ok description,left) ∧
      value = record "evidence-alias" [.natural index,description] := by
  unfold alias at ok
  obtain ⟨receipt,a,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨description,b,hd,h⟩ := bind_success _ _ _ _ _ h
  have selected := lift_success _ _ _ _ hr
  have returned := pure_success _ _ _ _ h
  have slot : root.receipts[index]? = some (some receipt) := by
    cases hs : root.receipts[index]? with
    | none => simp [hs,readOption] at selected
    | some candidate =>
      cases candidate with
      | none => simp [hs,readOption] at selected
      | some actual =>
        simp [hs,readOption] at selected
        exact congrArg (fun r => some (some r)) selected.1
  rcases returned with ⟨rfl,rfl⟩
  have sameWork := selected.2
  subst a
  exact ⟨receipt,description,slot,hd,rfl⟩

private def byteSize (value : Value) : WorkM Nat := do
  let bytes ← lift ((encode value).mapError (fun _ => .limit))
  return bytes.size

/-- Account for each repeated alias before accumulating its value. The initial
empty-list encoding includes all enclosing tags/lengths; each additional value
adds its encoding without the four-byte QDV1 header. Caller limits only lower
the fixed transport ceiling. Cons/reverse avoids quadratic list accumulation. -/
def origin (artifact : Qirf.Artifact) (root : Qirf.Validity.Root)
    (indices : List Nat) (limit : Nat := maxBytes) : WorkM Value := do
  guard (indices.length ≤ maxAliases) .limit
  exactWork (Exact.charge (indices.length+1))
  let actual ← lift ((FiniteView.program root.program).mapError (fun _ => .invalid))
  let interface := match artifact.rootInterface with
    | none => Value.null
    | some (input,output) => record "root-interface" [FiniteView.basis input,FiniteView.basis output]
  let describe := fun aliases => record "caller-origin" [interface,actual,.array aliases]
  let initial ← byteSize (describe [])
  let capacity := min limit maxBytes
  guard (initial ≤ capacity) .limit
  let (_,aliases) ← indices.foldlM (fun (used,aliases) index => do
    let value ← alias root index
    let size ← byteSize value
    guard (used + (size-4) ≤ capacity) .limit
    return (used+(size-4),value :: aliases)) (initial,[])
  return describe aliases.reverse

end QleisliKernel.Protocol.ExecutionView.Caller
