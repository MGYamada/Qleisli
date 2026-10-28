import QleisliKernel.Semantics.OrdinaryInputs
import QleisliKernel.FiniteCarrier

/-! Complete ordinary input-code enumeration. Original signature,
storage, actual root and every output history are separate required callers.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.OrdinaryDomain
open Semantics.FiniteCarrier Semantics.OrdinaryInputs Finite

private structure ReadLayout (basis : Basis) where
  code : Layout
  reference : layout basis = some code

private def readLayout (basis : Basis) : WorkM (ReadLayout basis) := fun before =>
  match ran : (FiniteCarrier.read basis).run before with
  | (.error error,after) => (.error error,after)
  | (.ok code,after) => (.ok ⟨code,FiniteCarrier.read_reference _ _ _ _ ran⟩,after)

private structure ForestRead (bases : List Basis) where
  code : Layout
  reference : forest bases = some code

private def forests : Nat → ((bases : List Basis) → WorkM (ForestRead bases)) :=
  Nat.rec (fun _ => throw .limit) (fun _ next bases => do
    match bases with
    | [] => return ⟨singleton,rfl⟩
    | first :: rest =>
      let head ← readLayout first
      let tail ← next rest
      guard (head.code.bits+tail.code.bits ≤ 6 &&
        head.code.labels.length*tail.code.labels.length ≤ 64) .limit
      exactWork (Exact.charge (head.code.labels.length*tail.code.labels.length+1))
      return ⟨tensor head.code tail.code,by
        change (do return tensor (← layout first) (← forest rest)) = _
        rw [head.reference,tail.reference]
        rfl⟩)

structure Checked (bases : List Basis) where
  code : Layout
  reference : forest bases = some code
  bounded : ∀ label ∈ code.labels, label < 2^code.bits

/-- Enumerate the independently interpreted code, never a producer's chosen
subset. Keep the complete source argument forest separate from its coordinates. -/
def read (bases : List Basis) : WorkM (Checked bases) := do
  guard (bases.length ≤ 64 && (bases.map List.length).sum ≤ 128) .limit
  let result ← forests 65 bases
  guard (result.code.bits ≤ 6 && !result.code.labels.isEmpty && result.code.labels.length ≤ 64) .limit
  exactWork (Exact.charge (result.code.labels.length+1))
  if bounded : result.code.labels.all (fun label => decide (label < 2^result.code.bits)) = true then
    return ⟨result.code,result.reference,by
      intro label member
      exact of_decide_eq_true ((List.all_eq_true.mp bounded) label member)⟩
  else throw .request

def assignments {bases : List Basis} (checked : Checked bases) : List (List Bool) :=
  checked.code.labels.map (bits checked.code.bits)

/-- Every returned row encodes the original ordered reference code exactly. -/
theorem assignment_codes {bases : List Basis} (checked : Checked bases) :
    (assignments checked).map Semantics.OrdinaryValue.littleEndian = checked.code.labels := by
  unfold assignments
  rw [List.map_map]
  have same : checked.code.labels.map
      (fun label => Semantics.OrdinaryValue.littleEndian (bits checked.code.bits label)) =
      checked.code.labels.map id := by
    apply List.map_congr_left
    intro label member
    exact bits_value _ _ (checked.bounded label member)
  simpa only [Function.comp_apply,List.map_id] using same

/-- No canonical input label can be omitted from actual supplied rows. This
does not prove original AST evaluation, runtime IO or a quantum-code theorem. -/
theorem complete {bases : List Basis} (checked : Checked bases) (label : Nat)
    (member : label ∈ checked.code.labels) :
    ∃ supplied ∈ assignments checked, Semantics.OrdinaryValue.littleEndian supplied = label := by
  refine ⟨bits checked.code.bits label,?_,bits_value _ _ (checked.bounded label member)⟩
  exact List.mem_map.mpr ⟨label,member,rfl⟩

theorem row_count {bases : List Basis} (checked : Checked bases) :
    (assignments checked).length = checked.code.labels.length := by
  exact List.length_map ..

end QleisliKernel.OrdinaryDomain
