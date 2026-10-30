import QleisliKernel.Semantics.RuntimeStorage
import QleisliKernel.FiniteCarrier

/-! Bounded storage/type matching for actual runtime-root proposals. Code-space,
ordinary-domain/history, body/effect and execution-view checks remain required
callers; a successful structural match alone issues no accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.RuntimeStorage
open Semantics.RuntimeStorage Finite

private def typeCells (basis : Semantics.FiniteCarrier.Basis) : Nat :=
  basis.foldl (fun count atom => count+1+match atom with
    | .enumeration origin names | .record origin names =>
      origin.moduleName.utf8ByteSize+origin.declarationName.utf8ByteSize+
        origin.source.utf8ByteSize+(names.map String.utf8ByteSize).sum
    | _ => 0) 0

private def nodeCells : Atom → Nat
  | .ordinary basis _ => 1+typeCells basis
  | .quantum owner => 1+typeCells owner.basis+owner.port.wires.length
  | .tuple _ => 1

/-- Bound metadata comparisons before expanding the stored type prefix. The
ordinary value payload is traversed separately by the existing value reader. -/
def footprint (expected : Semantics.RuntimeType.Tree) (stored : Value) : Nat :=
  expected.foldl (fun count atom => count+1+match atom with
    | .finite basisAtom => typeCells [basisAtom]
    | .quantum => 0) (stored.foldl (fun count atom => count+nodeCells atom) 0)

structure Checked (expected : Semantics.RuntimeType.Tree) (stored : Value) : Type where
  matched : Matches expected stored
  basisReads : ∀ basis ∈ bases stored, ∃ result before after,
    (FiniteCarrier.read basis).run before = (.ok result,after)
  quantumWidths : ∀ owner ∈ quantum stored,
    ∃ layout, Semantics.FiniteCarrier.layout owner.basis = some layout ∧
      owner.port.bits = layout.bits ∧ owner.port.wires.length = layout.bits

private def readBasis (basis : Semantics.FiniteCarrier.Basis) : WorkM
    (PLift (∃ result before after, (FiniteCarrier.read basis).run before = (.ok result,after))) := fun before =>
  match ran : (FiniteCarrier.read basis).run before with
  | (.error error,after) => (.error error,after)
  | (.ok result,after) => (.ok ⟨⟨result,before,after,ran⟩⟩,after)

private structure ReadLayout (basis : Semantics.FiniteCarrier.Basis) where
  layout : Semantics.FiniteCarrier.Layout
  reference : Semantics.FiniteCarrier.layout basis = some layout

private def readLayout (basis : Semantics.FiniteCarrier.Basis) : WorkM (ReadLayout basis) := fun before =>
  match ran : (FiniteCarrier.read basis).run before with
  | (.error error,after) => (.error error,after)
  | (.ok layout,after) =>
    (.ok ⟨layout,FiniteCarrier.read_reference _ _ _ _ ran⟩,after)

private def allBases : Nat → (items : List Semantics.FiniteCarrier.Basis) →
    WorkM (PLift (∀ basis ∈ items, ∃ result before after,
      (FiniteCarrier.read basis).run before = (.ok result,after))) :=
  Nat.rec (fun _ => throw .limit) (fun _ recurse items => do
    match items with
    | [] => return ⟨by simp⟩
    | first :: rest =>
      let head ← readBasis first
      let tail ← recurse rest
      return ⟨by
        intro basis member
        rcases List.mem_cons.mp member with same | later
        · subst basis; exact head.down
        · exact tail.down basis later⟩)

private def widths : Nat → (items : List Semantics.CarrierInterface.Owner) →
    WorkM (PLift (∀ owner ∈ items, ∃ layout,
      Semantics.FiniteCarrier.layout owner.basis = some layout ∧
        owner.port.bits = layout.bits ∧ owner.port.wires.length = layout.bits)) :=
  Nat.rec (fun _ => throw .limit) (fun _ recurse items => do
    match items with
    | [] => return ⟨by simp⟩
    | first :: rest =>
      let layout ← readLayout first.basis
      if ports : first.port.bits = layout.layout.bits ∧ first.port.wires.length = layout.layout.bits then
        let tail ← recurse rest
        return ⟨by
          intro owner member
          rcases List.mem_cons.mp member with same | later
          · subst owner
            exact ⟨layout.layout,layout.reference,ports⟩
          · exact tail.down owner later⟩
      else throw .request)

def read (expected : Semantics.RuntimeType.Tree) (stored : Value) :
    WorkM (Checked expected stored) := do
  guard (stored.length ≤ 3*128 && expected.length ≤ 3*128) .limit
  let cells := footprint expected stored
  exactWork (Exact.charge (16*(cells+expected.length+1)))
  if same : stored.foldr (fun atom rest => shapeStep rest atom) (some 0) = some 1 ∧
      typeOf stored = expected then
    let reads ← allBases 129 (bases stored)
    let ports ← widths 129 (quantum stored)
    return ⟨same,reads.down,ports.down⟩
  else throw .request

end QleisliKernel.RuntimeStorage
