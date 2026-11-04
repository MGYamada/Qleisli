import QleisliKernel.Qirf.RuntimeOrdinaryBody

/-! Actual mixed named-call scopes inside one retained runtime block.
Every visible caller SSA input is retained with its original symbolic binding.
Canonical callee quantum roles are introduced only by the enclosing original
body continuation. The complete native output sets and all quantum spectators
are checked before that continuation derives source result order and history.
No root, source body, matrix or accepted execution is supplied here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeCallScope
open QleisliKernel QleisliKernel.Finite

def program (inputs : List Semantics.Raw.Port) (classicalInputs : List Nat)
    (operations : List Semantics.Observation.Op) (outputs classicalOutputs : List Nat)
    (effect : Semantics.Raw.Effect) : Semantics.Observation.Program :=
  ⟨inputs,classicalInputs,operations,outputs,classicalOutputs,effect⟩

structure Checked {dependencies original} (block : RuntimeInterval.Block dependencies original)
    (start count : Nat) (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State)
    (effect : Semantics.Raw.Effect) where
  interval : RuntimeInterval.Checked block start count
  selected : List Semantics.Raw.Port
  atEntry : PureInterval.ports interval.before inputs = some selected
  visible : RuntimeOrdinaryBody.Visible interval.before ordinary
  localEntry : Raw.Observation.State
  entryRead : RuntimeInterval.Computed (PureInterval.initial
    (program selected (visible.table.map Prod.fst) ((block.operations.drop start).take count) [] [] effect)) localEntry
  localAfter : Raw.Observation.State
  nativeRead : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies 65 localEntry
    ((block.operations.drop start).take count)) localAfter
  returned : List Semantics.Raw.Port
  complete : returned = localAfter.quantum.live
  atExit : PureInterval.ports interval.after (returned.map (·.token)) = some returned
  spectators : PureInterval.spectators interval.before inputs =
    PureInterval.spectators interval.after (returned.map (·.token))
  classicalOutputs : List Nat
  localClassical : classicalOutputs = RuntimeOrdinaryBody.visibleIds localAfter
  actualClassical : classicalOutputs = RuntimeOrdinaryBody.visibleIds interval.after
  prepared : RuntimeInterval.Prepared dependencies
    (program selected (visible.table.map Prod.fst) ((block.operations.drop start).take count)
      (returned.map (·.token)) classicalOutputs effect)

def Checked.program {dependencies original block start count inputs ordinary effect}
    (checked : @Checked dependencies original block start count inputs ordinary effect) : Semantics.Observation.Program :=
  RuntimeCallScope.program checked.selected (checked.visible.table.map Prod.fst) ((block.operations.drop start).take count)
    (checked.returned.map (·.token)) checked.classicalOutputs effect

private def reserve {dependencies original} (block : RuntimeInterval.Block dependencies original) (inputs : List Nat) : WorkM Unit :=
  exactWork (Exact.charge (64*(inputs.length+block.operations.length+1)))

/-- This is the complete literal subject for a named callee, with every actual
visible SSA input and no caller quantum spectator in its canonical namespace.
The same parent block independently checks global identity and lexical history.
The source return tree and all canonical owner aliases must still be bound. -/
private def readAt {dependencies original block start count}
    (interval : @RuntimeInterval.Checked dependencies original block start count) (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State)
    (effect : Semantics.Raw.Effect) :
    WorkM {scope : Checked block start count inputs ordinary effect // scope.interval = interval} := do
  match atEntry : PureInterval.ports interval.before inputs with
  | none => throw .request
  | some selected =>
    let visible ← RuntimeOrdinaryBody.readVisible interval.before ordinary
    let operations := (block.operations.drop start).take count
    let localEntry ← SourceTypes.NaturalAffine.witness (PureInterval.initial
      (program selected (visible.table.map Prod.fst) operations [] [] effect))
    let localAfter ← SourceTypes.NaturalAffine.witness
      (Raw.Observation.checkOps dependencies 65 localEntry.val operations)
    let returned := localAfter.val.quantum.live
    let classicalOutputs := RuntimeOrdinaryBody.visibleIds localAfter.val
    exactWork (Exact.charge (64*(interval.before.quantum.live.length+interval.after.quantum.live.length+
      selected.length+returned.length+interval.before.classical.length+interval.after.classical.length+
      localAfter.val.classical.length+1)^2))
    if atExit : PureInterval.ports interval.after (returned.map (·.token)) = some returned then
      if spectators : PureInterval.spectators interval.before inputs =
          PureInterval.spectators interval.after (returned.map (·.token)) then
        if actualClassical : classicalOutputs = RuntimeOrdinaryBody.visibleIds interval.after then
          let prepared ← RuntimeInterval.prepare dependencies
            (program selected (visible.table.map Prod.fst) operations (returned.map (·.token)) classicalOutputs effect)
          return ⟨⟨interval,selected,atEntry,visible,localEntry.val,
            by with_reducible exact localEntry.property,localAfter.val,
            by with_reducible exact localAfter.property,returned,rfl,atExit,spectators,classicalOutputs,
            rfl,actualClassical,prepared⟩,rfl⟩
        else throw .request
      else throw .request
    else throw .request

/-- The caller already checked this exact parent interval. All local entry,
exit, body and spectator checks run against the retained interval. -/
def readWithInterval {dependencies original block start count}
    (interval : @RuntimeInterval.Checked dependencies original block start count) (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State)
    (effect : Semantics.Raw.Effect) :
    WorkM {scope : Checked block start count inputs ordinary effect // scope.interval = interval} := do
  reserve block inputs
  readAt interval inputs ordinary effect

def read {dependencies original} (block : RuntimeInterval.Block dependencies original)
    (start count : Nat) (inputs : List Nat) (ordinary : RuntimeOrdinaryBody.State)
    (effect : Semantics.Raw.Effect) : WorkM (Checked block start count inputs ordinary effect) := do
  reserve block inputs
  let interval ← RuntimeInterval.check block start count
  return (← readAt interval inputs ordinary effect).val

end QleisliKernel.Qirf.RuntimeCallScope
