import Qleisli.RuntimeFiniteTargetGram
import QleisliKernel.Qirf.RuntimeBodyOperations

/-! Consume the literal witness of the exact original native selection node.
The same finite source/code/layout/table fields produce physical intertwining
and logical Gram without a fixed lowering shape. The common body reader retains these witnesses at the original nested sites.
Named-call owner composition is a further obligation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionWitnessAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open RuntimeForestCode
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.RuntimeMultiwayGram

/-- The local source action at a particular node, with its original encodings
and physical trace. Other node kinds carry their own semantic obligations. -/
def SelectionLaw {R S : Type} {dependencies program block}
    (node : RuntimePureBody.Node dependencies program block)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) : Prop :=
  match node with
  | .selection frame selectorBits targetBits retained restricted inputCode outputCode labels expected logical _ codes layouts =>
    ∃ literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
        codes.owners.before codes.owners.transport.after,
      RuntimeInterval.Computed (RuntimeLocalEvents.readSource frame selectorBits targetBits retained
        restricted codes.owners) literal ∧
      logical = expected ∧ ∃ table : OrdinalTable inputCode outputCode retained.sectors labels expected,
        (∀ physical, Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
          (fun input => referenceAction literal.inputCode joint input r) physical =
            Qleisli.RuntimeMultiwayAction.finiteReferenceAction literal.outputCode
              (sourceAction frame codes layouts literal table joint) physical r) ∧
        ((List.finRange literal.outputCode.code.dimension).map fun index =>
          star (sourceAction frame codes layouts literal table joint index r) *
            sourceAction frame codes layouts literal table other index s).sum =
        ((List.finRange literal.outputCode.code.dimension).map fun index => star (joint index.val r) * other index.val s).sum
  | _ => False

/-- A real node supplies its literal receipt. Every field of the source and
native target equation stays indexed by that exact node. Its actual owner and
trace receipts supply the full code transport without an IR-shape premise. -/
theorem checked_selection {R S : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode : Matrix} {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {labels : List Nat} {expected logical : List Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels)
    (equations : RuntimeInterval.Computed (NominalSector.checkLogicals
      inputCode outputCode retained.sectors labels expected) logical)
    (witness : RuntimeSelectionWitness.Checked (.selection frame selectorBits targetBits retained restricted
      inputCode outputCode labels expected logical equations codes layouts))
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    SelectionLaw (.selection frame selectorBits targetBits retained restricted inputCode outputCode labels
      expected logical equations codes layouts) joint other r s := by
  cases witness with
  | selection literal original =>
    exact ⟨literal,original,Qleisli.RuntimeFiniteTargetGram.checked_selection
      frame codes layouts equations literal joint other r s⟩

private theorem witnessed {R S : Type} {dependencies program block}
    {node : RuntimePureBody.Node dependencies program block} (witness : RuntimeSelectionWitness.Checked node)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    SelectionLaw node joint other r s := by
  cases witness with
  | selection literal original =>
    exact checked_selection _ _ _ _ (.selection literal original) joint other r s

/-- The selected rank in the actual common result retains its original path.
Its coefficient identity and Gram law concern that exact native node, including
a selection nested inside a named call or an ordinary conditional branch. -/
theorem located_selection {R S : Type} {artifact owner name arguments request prepared order runtime}
    (body : @RuntimeBodyOperations.Checked artifact owner name arguments request prepared order runtime)
    {rank : Nat} (hit : RuntimeSelectionSteps.Located body.selections.witness rank)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
    RuntimeInterval.Computed (RuntimeSelectionSteps.readResult body.checked.result) body.selections ∧
      RuntimeSelectionSteps.At body.selections.witness rank hit.path hit.found ∧
      SelectionLaw hit.found.node joint other r s :=
  ⟨body.selectionsRead,hit.original,witnessed hit.found.literal joint other r s⟩

#print axioms located_selection
#print axioms checked_selection

end Qleisli.RuntimeSelectionWitnessAction
