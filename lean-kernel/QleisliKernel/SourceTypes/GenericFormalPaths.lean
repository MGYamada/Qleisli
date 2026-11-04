import QleisliKernel.SourceTypes.GenericOperation

/-! Enumerate lexical Op occurrences in the original generic graph. Each
child edge contributes its own position, including a shared node reached
twice, a zero-power child and unused operation arguments of a provider.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericFormalPaths
open QleisliKernel Finite
open QleisliKernel.Semantics.SymbolicBasis (Parameter)

abbrev Occurrence := List Nat × Nat × Parameter

private def visit (description : GenericOperation.Description) :
    Nat → Nat → List Nat → List Occurrence → WorkM (List Occurrence) :=
  Nat.rec (fun _ _ _ => throw .limit) (fun _ next index reversePath found => do
    exactWork (Exact.charge (8*(description.nodes.length+1)))
    let some node := description.nodes[index]? | throw .request
    match node with
    | .formal key =>
      exactWork (Exact.charge (8*(reversePath.length+1)))
      return (reversePath.reverse,index,key) :: found
    | _ =>
      let children := node.children
      exactWork (Exact.charge (8*(children.length+1)))
      children.zipIdx.foldlM (init := found) fun accumulated (child,position) => do
        guard (child < index) .request
        next child (position :: reversePath) accumulated)

/-- Paths use Op-child positions. Mixed-header ordinals in written source
are resolved by the native occurrence reader before the two lists are compared. -/
def read (description : GenericOperation.Description) : WorkM (List Occurrence) := do
  let count := description.nodes.length
  exactWork (Exact.charge (8*(count+1)))
  let found ← visit description (count+1) description.root [] []
  exactWork (Exact.charge (8*(found.length+1)))
  return found.reverse

end QleisliKernel.SourceTypes.GenericFormalPaths
