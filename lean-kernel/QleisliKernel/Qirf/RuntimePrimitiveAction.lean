import QleisliKernel.Qirf.RuntimePureInterval
import QleisliKernel.Qirf.Carrier
import QleisliKernel.CodeSpace
import QleisliKernel.Semantics.PrimitiveOperator

/-! Actual local primitive equations inside original mixed-runtime blocks.
Any literal pure interval must satisfy the independent exact logical operator
and full code-space equation. Instruction counts and particular Raw spellings
do not replace that equation. Source resolution, generic premises, complete
body traversal and the enclosing fresh graph remain mandatory callers.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimePrimitiveAction
open QleisliKernel QleisliKernel.Finite Semantics.Exact
abbrev Kind := Semantics.PrimitiveOperator.Kind

structure Checked {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count input output : Nat) (role : Semantics.SourceOwners.Owner) (kind : Kind) where
  interval : RuntimePureInterval.Checked block 1 start count [input] [output] [role]
  inputCode : Matrix
  outputCode : Matrix
  inputRead : RuntimeInterval.Computed
    (Carrier.ownerCode (interval.selected.map fun port => ⟨port,role.basis⟩)) inputCode
  outputRead : RuntimeInterval.Computed
    (Carrier.ownerCode (interval.returned.map fun port => ⟨port,role.basis⟩)) outputCode
  physical : Matrix
  physicalRead : RuntimeInterval.Computed (Raw.ProtectedEvaluation.reconstruct dependencies
    (RuntimePureInterval.fragment interval.selected interval.operations [output])) physical
  expected : Matrix
  reference : Semantics.PrimitiveOperator.meaning kind role.basis = some expected
  action : CodeSpace.Map inputCode outputCode physical
  equation : action.logical = expected

/-- Local reconstruction uses the final dependencies carried by the authentic
block. It never builds a dense matrix for the surrounding caller forest. -/
def check {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count input output : Nat) (role : Semantics.SourceOwners.Owner) (kind : Kind) :
    WorkM (Checked block start count input output role kind) := do
  let interval ← RuntimePureInterval.check block 1 start count [input] [output] [role]
  let layout ← FiniteCarrier.read role.basis
  exactWork (Exact.charge (4*(layout.labels.length+1)^2))
  match reference : Semantics.PrimitiveOperator.meaning kind role.basis with
  | none => throw .request
  | some expected =>
    let inputCode ← SourceTypes.NaturalAffine.witness
      (Carrier.ownerCode (interval.selected.map fun port => ⟨port,role.basis⟩))
    let outputCode ← SourceTypes.NaturalAffine.witness
      (Carrier.ownerCode (interval.returned.map fun port => ⟨port,role.basis⟩))
    let physical ← SourceTypes.NaturalAffine.witness (Raw.ProtectedEvaluation.reconstruct dependencies
      (RuntimePureInterval.fragment interval.selected interval.operations [output]))
    let action ← CodeSpace.readMap inputCode.val outputCode.val physical.val
    exactWork (Exact.charge (action.logical.entries.length+expected.entries.length+1))
    if equation : action.logical = expected then
      return ⟨interval,inputCode.val,outputCode.val,
        by with_reducible exact inputCode.property,by with_reducible exact outputCode.property,
        physical.val,by with_reducible exact physical.property,expected,reference,action,equation⟩
    else throw .equation

theorem Checked.fullCodeEquation {dependencies program block start count input output role kind}
    (checked : @Checked dependencies program block start count input output role kind) :
    CodeSpace.CompositionEquation checked.inputCode checked.outputCode checked.physical checked.expected := by
  rw [← checked.equation]
  exact checked.action.equation

end QleisliKernel.Qirf.RuntimePrimitiveAction
