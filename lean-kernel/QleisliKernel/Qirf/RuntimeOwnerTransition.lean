import QleisliKernel.Qirf.RuntimeOwnerMap

/-! Source-owner transport through an original pure Raw interval. Each surviving
token retains its source owner, including owners with no physical wires.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOwnerTransition
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeOwnerMap (Map Binding)

def resolve (state : Raw.Observation.State) (entry : Nat × Semantics.RawOwnerFlow.Tree) : WorkM Binding := do
  match entry.2 with
  | .pair .. => throw .request
  | .owner role bits =>
    let some port := state.quantum.live.find? (·.token == entry.1) | throw .request
    guard (port.bits == bits) .request
    return ⟨role,port⟩

structure Checked {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : Map) where
  after : RuntimeOwnerMap.Checked (before.map (·.owner)) interval.after
  flow : ∃ operations initial final moved,
    Sector.pureOps ((block.operations.drop start).take count) = some operations ∧
    Semantics.RawOwnerFlow.seed (before.map (·.owner)) (before.map (·.port)) = some initial ∧
    operations.foldlM Semantics.RawOwnerFlow.step initial = some final ∧
    RuntimeInterval.Computed (final.mapM (resolve interval.after)) moved ∧
    RuntimeInterval.Computed (RuntimeOwnerMap.order (before.map (·.owner)) moved) after.bindings

/-- Keep the witnesses from the same computation used by the source-body loop.
The extra data about intermediate frames is erased. -/
def read {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : Map) :
    WorkM (Checked interval before) := do
  exactWork (Exact.charge (32*(before.length+1)*(block.operations.length+1)))
  let ops ← lift (readOption (Sector.pureOps ((block.operations.drop start).take count)).attach)
  let initial ← lift (readOption (Semantics.RawOwnerFlow.seed
    (before.map (·.owner)) (before.map (·.port))).attach)
  let final ← lift (readOption (ops.val.foldlM Semantics.RawOwnerFlow.step initial.val).attach)
  let moved ← NaturalAffine.witness (final.val.mapM (resolve interval.after))
  let ordered ← NaturalAffine.witness (RuntimeOwnerMap.order (before.map (·.owner)) moved.val)
  let after ← RuntimeOwnerMap.checkBindings (before.map (·.owner)) interval.after ordered.val
  return ⟨after.val,⟨ops.val,initial.val,final.val,moved.val,ops.property,initial.property,
    final.property,by with_reducible exact moved.property,by
      rw [after.property]
      with_reducible exact ordered.property⟩⟩

/-- A two-owner source lookup retains the actual bindings and their order. -/
structure Pair (roles : List RuntimeOwnerMap.Owner) (bindings : Map) where
  first : Binding
  second : Binding
  ordered : RuntimeInterval.Computed (RuntimeOwnerMap.order roles bindings) [first,second]

def readPair (roles : List RuntimeOwnerMap.Owner) (bindings : Map) : WorkM (Pair roles bindings) := do
  let ordered ← NaturalAffine.witness (RuntimeOwnerMap.order roles bindings)
  match found : ordered.val with
  | [first,second] => return ⟨first,second,by rw [← found]; with_reducible exact ordered.property⟩
  | _ => throw .request

/-- Both ordered pairs come from the complete source frame at their own end
of this interval, along the same independently computed Raw owner flow. -/
structure Selection {dependencies program block start count}
    (interval : @RuntimeInterval.Checked dependencies program block start count)
    (inputs outputs : List Nat) (roles : List RuntimeOwnerMap.Owner) where
  callerRoles : List RuntimeOwnerMap.Owner
  before : RuntimeOwnerMap.Checked callerRoles interval.before
  transport : Checked interval before.bindings
  selected : Pair roles before.bindings
  returned : Pair roles transport.after.bindings
  inputTokens : inputs = [selected.first.port.token,selected.second.port.token]
  outputTokens : outputs = [returned.first.port.token,returned.second.port.token]

end QleisliKernel.Qirf.RuntimeOwnerTransition
