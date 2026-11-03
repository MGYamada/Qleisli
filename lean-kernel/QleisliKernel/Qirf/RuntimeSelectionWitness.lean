import QleisliKernel.Qirf.RuntimeLocalEvents
import QleisliKernel.Qirf.RuntimePureBody

/-! Literal interpretation of the same original selection node.
The indexed constructor retains every native source/code/layout/table field
and the actual readSource invocation. No caller matrix, capability flag,
independent root or replacement interval can supply this witness. It exposes
metadata for the proof consumer and grants no accepted handle. Deriving a
particular original lowering shape remains a separate obligation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Qirf.RuntimeSelectionWitness
open QleisliKernel QleisliKernel.Finite

/-- A literal read belongs to this exact selection node, including its same
original target-code reads, native sector read and original-ordinal table. -/
inductive Checked {dependencies program} {block : RuntimeInterval.Block dependencies program} :
    RuntimePureBody.Node dependencies program block → Type where
  | selection
      {start count inputs outputs selector target}
      {frame : RuntimePureInterval.Checked block 2 start count inputs outputs [selector,target]}
      {selectorBits targetBits : Nat} {retained : Raw.Sector.Retained}
      {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits targetBits]
        (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
      {inputCode outputCode : Semantics.Exact.Matrix} {labels : List Nat}
      {expected logical : List Semantics.Exact.Matrix}
      {equations : RuntimeInterval.Computed (NominalSector.checkLogicals
        inputCode outputCode retained.sectors labels expected) logical}
      {codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode}
      {layouts : RuntimePureBody.SelectionLayouts selector.basis target.basis selectorBits targetBits labels}
      (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
        codes.owners.before codes.owners.transport.after)
      (original : RuntimeInterval.Computed (RuntimeLocalEvents.readSource frame selectorBits targetBits retained
        restricted codes.owners) literal) :
      Checked (.selection frame selectorBits targetBits retained restricted inputCode outputCode labels
        expected logical equations codes layouts)

/-- Read only the exact retained selection node. Other node constructors
cannot manufacture selection evidence; their own continuations remain separate. -/
def read {dependencies program block} (node : RuntimePureBody.Node dependencies program block) :
    WorkM (Checked node) :=
  match node with
  | .selection frame selectorBits targetBits retained restricted _inputCode _outputCode _labels
      _expected _logical _equations codes _layouts => do
    let literal ← SourceTypes.NaturalAffine.witness
      (RuntimeLocalEvents.readSource frame selectorBits targetBits retained restricted codes.owners)
    return .selection literal.val (by with_reducible exact literal.property)
  | _ => throw .request

end QleisliKernel.Qirf.RuntimeSelectionWitness
