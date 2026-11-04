import Qleisli.CodeSpaceAction
import Qleisli.RawProtectedEvaluation
import QleisliKernel.Qirf.RuntimePrimitiveSource

/-! The exact original primitive and its operand determine the action of the
checked local fragment on every encoded input, including external references.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeSourcePrimitiveAction
open QleisliKernel QleisliKernel.Qirf QleisliKernel.SourceTypes

private def primitive : CallName.Primitive → Option RuntimePrimitiveAction.Kind
  | .h => some .h
  | .globalPhaseEighth => some .globalPhaseEighth
  | _ => none

def operand {sources caller} : SourceRuntimeContext.Event sources caller →
    Option (RuntimePrimitiveAction.Kind × Semantics.SourceOwners.Owner)
  | .primitive event => match event.arguments with
    | [[.owner owner]] => (primitive event.kind).map fun kind => (kind,owner)
    | _ => none
  | .phase event => some (.phase event.application.coefficient.exponent,event.operand)
  | _ => none

private theorem kind_of_selection {source kind} (bound : RuntimePrimitiveSource.PrimitiveKind source kind) :
    primitive source = some kind := by cases bound <;> rfl

theorem original_operand {sources caller event next role kind}
    (use : @RuntimePrimitiveSource.Selected sources caller event next role kind) :
    operand event = some (kind,role) := by
  cases use with
  | phase => rfl
  | primitive event _ role kind _ args chosen =>
    simp only [operand,args,kind_of_selection chosen,Option.map_some]

/-- The source reference and the native operator are linked through the
actual checker call. Its physical matrix is the reconstruction of the
original fragment on this dependency root. -/
theorem reference_action {dependencies program block start count input output role kind}
    (action : @RuntimePrimitiveAction.Checked dependencies program block start count input output role kind)
    (binding : RuntimePrimitiveSource.Checked action) :
    Qleisli.Semantics.Raw.ProgramMeaning dependencies
        (RuntimePureInterval.fragment action.interval.selected action.interval.operations [output]) action.physical ∧
    ((operand binding.event).bind fun (op,owner) => Semantics.PrimitiveOperator.meaning op owner.basis) =
        some action.expected ∧
    ∀ {Reference : Type} (joint : Nat → Reference → ℂ) (row : Nat) (reference : Reference),
      row < action.physical.rows →
      Qleisli.Semantics.Exact.action action.physical
          (fun input ref => Qleisli.Semantics.Exact.action action.inputCode joint input ref) row reference =
        Qleisli.Semantics.Exact.action action.outputCode
          (fun output ref => Qleisli.Semantics.Exact.action action.expected joint output ref) row reference := by
  obtain ⟨work,left,read⟩ := action.physicalRead
  refine ⟨Qleisli.Raw.ProtectedEvaluation.reconstruct_denotes dependencies _ action.physical work left read,?_,?_⟩
  · rw [original_operand binding.selected]
    exact action.reference
  · intro Reference joint row reference bound
    have actual := Qleisli.CodeSpace.map_reference_action action.action joint row reference bound
    rw [action.equation] at actual
    exact actual

#print axioms reference_action
end Qleisli.RuntimeSourcePrimitiveAction
