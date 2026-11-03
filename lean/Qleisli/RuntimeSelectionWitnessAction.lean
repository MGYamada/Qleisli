import Qleisli.RuntimeFiniteTargetGram
import QleisliKernel.Qirf.RuntimeSelectionWitness

/-! Consume the literal witness of the exact original native selection node.
The same finite source/code/layout/table fields produce physical intertwining
and logical Gram. The explicit authentic SelectionForm premise is retained;
this module does not derive that original lowering shape, compose named-call
owner namespaces, grant acceptance or assume bounded arithmetic availability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeSelectionWitnessAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.Exact
open RuntimeForestCode
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct Qleisli.RuntimeMultiwayGram

/-- A real node supplies its literal receipt. Every field of the source and
native target equation stays indexed by that exact node; only the independently
stated actual IR-shape obligation remains a premise. -/
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
    (form : Qleisli.RuntimeOwnerTransitionAction.SelectionForm frame codes.owners)
    (joint : Nat → R → ℂ) (other : Nat → S → ℂ) (r : R) (s : S) :
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
        ((List.finRange literal.outputCode.code.dimension).map fun index => star (joint index.val r) * other index.val s).sum := by
  cases witness with
  | selection literal original =>
    exact ⟨literal,original,Qleisli.RuntimeFiniteTargetGram.checked_selection
      frame codes layouts equations literal form joint other r s⟩

#print axioms checked_selection

end Qleisli.RuntimeSelectionWitnessAction
