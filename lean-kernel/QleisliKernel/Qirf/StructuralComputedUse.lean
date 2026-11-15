import QleisliKernel.Qirf.StructuralXorInterval
import QleisliKernel.Qirf.RuntimeComputedUse

/-! Original use matching for a structurally verified compute predicate.
Both literal compute circuits are checked against the same original predicate.
The use is checked on the two auxiliary values by the existing exact rule.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.StructuralComputedUse
open QleisliKernel Finite SourceTypes SourceRuntimeContext
open Semantics.Finite

structure Checked {sources caller} {event : ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event)
    (compute inverse : List Step) (uses : List Semantics.Raw.Use) where
  protectedScope : event.written.parts.logical = none
  forward : StructuralXor.Checked original.width original.compiled.clauses compute
  reverse : StructuralXor.Checked original.width original.compiled.clauses inverse
  body : SourceRuntimeTrace.ComputedBody event
  originalBody : RuntimeInterval.Computed (SourceRuntimeTrace.readComputedSource event) body
  action : RuntimeComputedUse.Action
  originalAction : RuntimeInterval.Computed (RuntimeComputedUse.sourceBody body) action
  emitted : RuntimeComputedUse.RawAction uses
  literalAction : RuntimeInterval.Computed (RuntimeComputedUse.rawAction uses) emitted
  equation : emitted.matrix = action.matrix

theorem Checked.sameCircuit {sources caller compute inverse uses} {event : ComputedEvent sources caller}
    {original : StructuralXorPredicate.Original event} (checked : Checked original compute inverse uses) :
    compute = inverse :=
  checked.forward.literal.trans checked.reverse.literal.symm

/-- Reuse the exact checks of the original auxiliary body and emitted diagonal.
The eventual enclosing Raw operation still supplies literal ownership,
scratch allocation and release, and its position in the whole program. -/
def read {sources caller} {event : ComputedEvent sources caller}
    (original : StructuralXorPredicate.Original event)
    (compute inverse : List Step) (uses : List Semantics.Raw.Use)
    (prepared : Option (RuntimeComputedUse.OriginalSource event) := none) :
    WorkM (Checked original compute inverse uses) := do
  if supported : event.written.parts.logical = none then
    let forward ← StructuralXorPredicate.check original compute
    let reverse ← StructuralXorPredicate.check original inverse
    let source ← match prepared with
      | some source => pure source
      | none => do
        let body ← NaturalAffine.witness (SourceRuntimeTrace.readComputedSource event)
        let action ← NaturalAffine.witness (RuntimeComputedUse.sourceBody body.val)
        pure (⟨original.body,original.original,body.val,by with_reducible exact body.property,
          action.val,by with_reducible exact action.property⟩ : RuntimeComputedUse.OriginalSource event)
    let emitted ← NaturalAffine.witness (RuntimeComputedUse.rawAction uses)
    exactWork (Exact.charge (emitted.val.matrix.entries.length + source.action.matrix.entries.length + 1))
    if equation : emitted.val.matrix = source.action.matrix then
      return ⟨supported,forward,reverse,source.body,source.bodyRead,source.action,source.actionRead,
        emitted.val,by with_reducible exact emitted.property,equation⟩
    else throw .equation
  else throw .request

/-- The two comparisons that actually run before the original use-body
check consume twice the literal predicate-circuit charge. This prefix shares
the caller's work state with the subsequent source and auxiliary checks. -/
theorem read_circuit_work {sources caller compute inverse uses work left}
    {event : ComputedEvent sources caller} {original : StructuralXorPredicate.Original event}
    {checked : Checked original compute inverse uses}
    {prepared : Option (RuntimeComputedUse.OriginalSource event)}
    (ok : (read original compute inverse uses prepared).run work = (.ok checked,left)) :
    ∃ forward reverse middle afterCircuits,
      (StructuralXorPredicate.check original compute).run work = (.ok forward,middle) ∧
      (StructuralXorPredicate.check original inverse).run middle = (.ok reverse,afterCircuits) ∧
      work = afterCircuits + 16 * ((original.compiled.clauses.map fun controls =>
        2 * controls.length + 7).sum + 1) := by
  simp only [read, checked.protectedScope, dite_true] at ok
  obtain ⟨forward,middle,first,ok⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨reverse,afterCircuits,second,_⟩ := Finite.bind_success _ _ _ _ _ ok
  have paidForward := StructuralXor.check_circuit_work first
  have paidReverse := StructuralXor.check_circuit_work second
  exact ⟨forward,reverse,middle,afterCircuits,first,second,by omega⟩

#print axioms read_circuit_work
#print axioms read

end QleisliKernel.Qirf.StructuralComputedUse
