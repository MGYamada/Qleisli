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
    (compute inverse : List Step) (uses : List Semantics.Raw.Use) :
    WorkM (Checked original compute inverse uses) := do
  if supported : event.written.parts.logical = none then
    let forward ← StructuralXorPredicate.check original compute
    let reverse ← StructuralXorPredicate.check original inverse
    let body ← NaturalAffine.witness (SourceRuntimeTrace.readComputedSource event)
    let action ← NaturalAffine.witness (RuntimeComputedUse.sourceBody body.val)
    let emitted ← NaturalAffine.witness (RuntimeComputedUse.rawAction uses)
    exactWork (Exact.charge (emitted.val.matrix.entries.length + action.val.matrix.entries.length + 1))
    if equation : emitted.val.matrix = action.val.matrix then
      return ⟨supported,forward,reverse,body.val,by with_reducible exact body.property,
        action.val,by with_reducible exact action.property,emitted.val,
        by with_reducible exact emitted.property,equation⟩
    else throw .equation
  else throw .request

#print axioms read

end QleisliKernel.Qirf.StructuralComputedUse
