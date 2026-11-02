import QleisliKernel.Qirf.RuntimePureInterval

/-! Literal named-call scopes with a complete native output interface.
The native live order is only an internal scope order. The common original-body
traversal must derive the source return order and transport its full owner
history before the caller continuation can use this scope. No width-based role
inference or execution authority is supplied by this component.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeCallInterval
open QleisliKernel QleisliKernel.Finite

structure Checked {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (inputs : List Nat) where
  interval : RuntimeInterval.Checked block start count
  operations : List Semantics.Raw.Op
  literal : (block.operations.drop start).take count = operations.map Semantics.Observation.Op.pure
  selected : List Semantics.Raw.Port
  atEntry : PureInterval.ports interval.before inputs = some selected
  localEntry : Raw.Observation.State
  entryRead : RuntimeInterval.Computed (PureInterval.initial
    (Semantics.Ownership.pureProgram (RuntimePureInterval.fragment selected operations []))) localEntry
  localAfter : Raw.Observation.State
  nativeRead : RuntimeInterval.Computed
    (Raw.Observation.checkOps dependencies 65 localEntry (operations.map Semantics.Observation.Op.pure)) localAfter
  returned : List Semantics.Raw.Port
  complete : returned = localAfter.quantum.live
  atExit : PureInterval.ports interval.after (returned.map (·.token)) = some returned
  spectators : PureInterval.spectators interval.before inputs =
    PureInterval.spectators interval.after (returned.map (·.token))
  prepared : RuntimeInterval.Prepared dependencies
    (Semantics.Ownership.pureProgram
      (RuntimePureInterval.fragment selected operations (returned.map (·.token))))

def Checked.program {dependencies program block start count inputs}
    (checked : @Checked dependencies program block start count inputs) : Semantics.Observation.Program :=
  Semantics.Ownership.pureProgram
    (RuntimePureInterval.fragment checked.selected checked.operations (checked.returned.map (·.token)))

/-- The complete independently computed local output set is checked against
the actual enclosing interval before source recursion assigns any result role.
Separate zero-width ports and every caller spectator remain present. -/
def read {dependencies program} (block : RuntimeInterval.Block dependencies program)
    (start count : Nat) (inputs : List Nat) : WorkM (Checked block start count inputs) := do
  exactWork (Exact.charge (64*(inputs.length+block.operations.length+1)))
  let interval ← RuntimeInterval.check block start count
  match parsed : Sector.pureOps ((block.operations.drop start).take count) with
  | none => throw .request
  | some operations =>
    match atEntry : PureInterval.ports interval.before inputs with
    | none => throw .request
    | some selected =>
      let localEntry ← SourceTypes.NaturalAffine.witness (PureInterval.initial
        (Semantics.Ownership.pureProgram (RuntimePureInterval.fragment selected operations [])))
      let localAfter ← SourceTypes.NaturalAffine.witness
        (Raw.Observation.checkOps dependencies 65 localEntry.val (operations.map Semantics.Observation.Op.pure))
      let returned := localAfter.val.quantum.live
      exactWork (Exact.charge (64*(interval.before.quantum.live.length+interval.after.quantum.live.length+
        selected.length+returned.length+1)^2))
      if atExit : PureInterval.ports interval.after (returned.map (·.token)) = some returned then
        if spectators : PureInterval.spectators interval.before inputs =
            PureInterval.spectators interval.after (returned.map (·.token)) then
          let prepared ← RuntimeInterval.prepare dependencies
            (Semantics.Ownership.pureProgram
              (RuntimePureInterval.fragment selected operations (returned.map (·.token))))
          return ⟨interval,operations,Sector.pureOps_bound _ _ parsed,selected,atEntry,localEntry.val,
            by with_reducible exact localEntry.property,localAfter.val,
            by with_reducible exact localAfter.property,returned,rfl,atExit,spectators,prepared⟩
        else throw .request
      else throw .request

end QleisliKernel.Qirf.RuntimeCallInterval
