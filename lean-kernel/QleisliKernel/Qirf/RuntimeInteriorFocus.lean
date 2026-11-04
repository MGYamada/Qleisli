import QleisliKernel.SourceTypes.GenericStepEmbedding

/-! Follow original Op-child positions in a whole, already executed
substitution. The output location stays indexed by the whole returned
subject, including all preceding sibling blocks and their supplier rows.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeInteriorFocus
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.GenericOperationSubstitute (Step Embedded nodeSize rowSize)

inductive Route (description : GenericOperation.Description) : Nat → List Nat → Nat → Prop where
  | here (index : Nat) : Route description index [] index
  | child {index position next rest last} (node : GenericOperation.Node)
      (original : description.nodes[index]? = some node) (ordinal : node.children[position]? = some next)
      (tail : Route description next rest last) : Route description index (position :: rest) last

structure Projection {sources app original} (transfer : @GenericOperationSubstitute.Checked sources app original) where
  inputIndex : Nat
  row : Step app original
  atIndex : transfer.result.steps[inputIndex]? = some row
  nodeOffset : Nat
  rowOffset : Nat
  embedded : Embedded transfer.result.subject row.result.subject nodeOffset rowOffset

private def walk {sources app original} (transfer : @GenericOperationSubstitute.Checked sources app original) :
    Nat → (current : Projection transfer) → (positions : List Nat) →
    WorkM {out : Projection transfer // Route original.description current.inputIndex positions out.inputIndex} :=
  Nat.rec
    (fun current positions => match positions with
      | [] => pure ⟨current,.here _⟩
      | _ :: _ => throw .limit)
    (fun _ visit current positions => match positions with
      | [] => pure ⟨current,.here _⟩
      | position :: rest => do
        let parent := current.row
        let children := parent.node.children
        let count := children.length
        exactWork (Exact.charge (16*(count+transfer.result.steps.length+
          (min position count+1)*(parent.previous.length+1)+1)))
        match selected : children[position]? with
        | none => throw .request
        | some index =>
          match atChild : transfer.result.steps[index]? with
          | none => throw .request
          | some row =>
            let nodes := parent.offsetBefore nodeSize position
            let origins := parent.offsetBefore rowSize position
            exactWork (Exact.charge (8*(nodes+origins+1)))
            have localBlock := transfer.childEmbedding current.atIndex selected atChild
            let next : Projection transfer :=
              ⟨index,row,atChild,nodes+current.nodeOffset,origins+current.rowOffset,current.embedded.trans localBlock⟩
            let out ← visit next rest
            have originalNode : original.description.nodes[current.inputIndex]? = some parent.node := by
              rw [← transfer.result.index_at current.atIndex]
              exact parent.actual
            return ⟨out.val,.child parent.node originalNode selected out.property⟩)

structure Checked {sources app original} (transfer : @GenericOperationSubstitute.Checked sources app original)
    (positions : List Nat) extends Projection transfer where
  route : Route original.description original.description.root positions inputIndex

def Checked.outputIndex {sources app original transfer positions} (focus : @Checked sources app original transfer positions) : Nat :=
  focus.row.result.subject.description.root + focus.nodeOffset

/-- The root row comes from the actual whole transport result. No substitution
is rerun on the local piece selected by the input path. -/
def read {sources app original} (transfer : @GenericOperationSubstitute.Checked sources app original)
    (positions : List Nat) : WorkM (Checked transfer positions) := do
  exactWork (Exact.charge (16*(positions.length+transfer.result.steps.length+1)))
  match atRoot : transfer.result.steps[original.description.root]? with
  | none => throw .request
  | some row =>
    have same : row.result.subject = transfer.result.subject := by
      have returned := transfer.result.returned
      rw [atRoot,Option.map_some] at returned
      exact Option.some.inj returned
    let start : Projection transfer :=
      ⟨original.description.root,row,atRoot,0,0,by rw [← same]; exact Embedded.root _⟩
    let out ← walk transfer (positions.length+1) start positions
    return ⟨out.val,out.property⟩

end QleisliKernel.Qirf.RuntimeInteriorFocus
