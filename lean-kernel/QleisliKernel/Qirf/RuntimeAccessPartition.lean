import QleisliKernel.Qirf.RuntimeAccessSource

/-! Match the actual ordinary Raw splits and joins around a written access call.
The partition follows the original coordinates and restores the returned tokens
in reverse order, including distinct owners for empty ranges.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeAccessPartition
open QleisliKernel Finite SourceTypes.AccessSyntax
open RuntimeAccessSource (Parameter)
open QleisliKernel.Semantics.Raw (Port)

private structure Parent where
  parameter : Parameter
  remainder : Option Nat
  removed : List (Nat × Nat) := []

private structure Access where
  binder : String
  position : Option Nat
  returned : Nat

private def findParent (parents : List Parent) (binder : String) : Option Parent :=
  parents.find? (fun parent => parent.parameter.original.binder.text == binder)

private def replaceParent (parents : List Parent) (binder : String) (next : Parent) : List Parent :=
  parents.map (fun parent => if parent.parameter.original.binder.text == binder then next else parent)

private def extract (parent : Parent) (place : Place) (selected : Port)
    (operations : List RuntimeInterval.Op) : Option (Parent × Option Nat × List RuntimeInterval.Op) := do
  let input ← parent.remainder
  match place.range with
  | none =>
    if !parent.removed.isEmpty || selected.token != input then none else
      some ({parent with remainder := none},none,operations)
  | some (start,stop) =>
    if stop > start && parent.removed.any (fun (i,j) => i < j && start < j && i < stop) then none else do
      let earlier := (parent.removed.map (fun (i,j) => min (start-i) (j-i))).sum
      let position := start-earlier
      let .pure (.split original leading tail leftBits) :: .pure (.split next picked suffix width) ::
        .pure (.join left right remainder) :: rest := operations | none
      if original != input || leftBits != position || next != tail || picked != selected.token ||
          width != stop-start || left != leading || right != suffix then none else
        some ({parent with remainder := some remainder,removed := (start,stop) :: parent.removed},
          some position,rest)

private def restore (parent : Parent) (access : Access)
    (operations : List RuntimeInterval.Op) : Option (Parent × List RuntimeInterval.Op) := do
  match access.position with
  | none =>
    if parent.remainder.isSome then none else some ({parent with remainder := some access.returned},operations)
  | some position =>
    let input ← parent.remainder
    let .pure (.split original leading suffix leftBits) :: .pure (.join left picked head) ::
      .pure (.join joined right output) :: rest := operations | none
    if original != input || leftBits != position || left != leading || picked != access.returned ||
        joined != head || right != suffix then none else
      some ({parent with remainder := some output},rest)

def routingCount (places : List Place) : Nat := 3 * (places.filter (fun place => !place.whole)).length

/-- Replay only the literal routing around the call. Every token is read from
the actual Raw operations or the checked local entry and return. The surrounding
Raw checker independently validates freshness, widths and live owner flow. -/
def replay (entry : List Parameter) (places : List Place) (selected returned : List Port)
    (before after : List RuntimeInterval.Op) : Option (List Port) := do
  if places.length != selected.length || places.length != returned.length then none else do
    let parents : List Parent := entry.map fun parameter => ⟨parameter,some parameter.port.token,[]⟩
    let (parents,accesses,remaining) ← ((places.zip selected).zip returned).foldlM
      (fun (parents,accesses,operations) ((place,input),output) => do
        let binder := place.owner.binder.text
        let parent ← findParent parents binder
        let (next,position,rest) ← extract parent place input operations
        return (replaceParent parents binder next,⟨binder,position,output.token⟩ :: accesses,rest))
      (parents,[],before)
    if !remaining.isEmpty then none else do
      let (restored,remaining) ← accesses.foldlM (fun (parents,operations) access => do
        let parent ← findParent parents access.binder
        let (next,rest) ← restore parent access operations
        return (replaceParent parents access.binder next,rest)) (parents,after)
      if !remaining.isEmpty then none else
        restored.mapM fun parent => do
          let token ← parent.remainder
          return {parent.parameter.port with token}

structure Restored {tokens dependencies program block callee lookup names calls start count inputs outputs}
    (call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs)
    (entry : List Parameter) (begin : Nat) where
  preamble : RuntimeInterval.Checked block begin (start-begin)
  bounded : begin ≤ start
  entryLive : PureInterval.ports preamble.before (entry.map (·.port.token)) = some (entry.map (·.port))
  entryComplete : preamble.before.quantum.live.length = entry.length
  routing : RuntimeInterval.Checked block (start+count) (routingCount call.places)
  restored : List Port
  replayed : replay entry call.places call.frame.selected call.frame.returned
    ((block.operations.drop begin).take (start-begin))
    ((block.operations.drop (start+count)).take (routingCount call.places)) = some restored
  live : PureInterval.ports routing.after (restored.map (·.token)) = some restored
  complete : routing.after.quantum.live.length = restored.length

private def readRouting {tokens dependencies program block callee lookup names calls start count inputs outputs}
    (call : @RuntimeAccessInterval.Checked tokens dependencies program callee lookup names calls
      block start count inputs outputs)
    (entry : List Parameter) (begin : Nat) : WorkM (Restored call entry begin) := do
  if bounded : begin ≤ start then
    let preamble ← RuntimeInterval.check block begin (start-begin)
    let routing ← RuntimeInterval.check block (start+count) (routingCount call.places)
    exactWork (Exact.charge (32*(call.places.length+entry.length+1)*(call.places.length+entry.length+1)))
    let ports := entry.map (·.port)
    if entryLive : PureInterval.ports preamble.before (ports.map (·.token)) = some ports then
      if entryComplete : preamble.before.quantum.live.length = entry.length then
        match replayed : replay entry call.places call.frame.selected call.frame.returned
            ((block.operations.drop begin).take (start-begin))
            ((block.operations.drop (start+count)).take (routingCount call.places)) with
        | none => throw .request
        | some restored =>
          if live : PureInterval.ports routing.after (restored.map (·.token)) = some restored then
            if complete : routing.after.quantum.live.length = restored.length then
              return ⟨preamble,bounded,by simpa [ports,List.map_map] using entryLive,
                entryComplete,routing,restored,replayed,live,complete⟩
            else throw .request
          else throw .request
      else throw .request
    else throw .request
  else throw .request

structure Checked {sources owner name dependencies program signature root}
    (source : @RuntimeAccessSource.Checked sources owner name dependencies program signature root)
    (start count : Nat) (inputs outputs : List Nat) where
  call : RuntimeAccessSource.First source start count inputs outputs
  owners : Restored call.interval source.entry 0

/-- The first two written statements are anchored at the root. Here the first
call must be preceded only by its own extraction and followed by its complete
restoration. The checked return keeps the original parent and spectator axes. -/
def read {sources owner name dependencies program signature root}
    (source : @RuntimeAccessSource.Checked sources owner name dependencies program signature root)
    (start count : Nat) (inputs outputs : List Nat) : WorkM (Checked source start count inputs outputs) := do
  let call ← RuntimeAccessSource.readFirst source start count inputs outputs
  return ⟨call,← readRouting call.interval source.entry 0⟩

def Checked.nextOffset {sources owner name dependencies program signature root source start count inputs outputs}
    (first : @Checked sources owner name dependencies program signature root source start count inputs outputs) : Nat :=
  start+count+routingCount first.call.interval.places

def Checked.nextEntry {sources owner name dependencies program signature root source start count inputs outputs}
    (first : @Checked sources owner name dependencies program signature root source start count inputs outputs) :
    List Parameter :=
  (source.entry.zip first.owners.restored).map fun (original,port) => {original with port}

structure Second {sources owner name dependencies program signature root source firstStart firstCount firstInputs firstOutputs}
    (first : @Checked sources owner name dependencies program signature root source firstStart firstCount firstInputs firstOutputs)
    (start count : Nat) (inputs outputs : List Nat) where
  call : RuntimeAccessInterval.Checked source.calls.after source.lookup source.naturals
    (fun _ _ => none) root.block start count inputs outputs
  owners : Restored call first.nextEntry first.nextOffset
  compatible : SourceTypes.AccessSyntax.compatible first.call.interval.places call.places = true

/-- The next call starts with the first call's restored tokens. The only Raw
operations allowed between the call bodies are their checked structural routes. -/
def readSecond {sources owner name dependencies program signature root source firstStart firstCount firstInputs firstOutputs}
    (first : @Checked sources owner name dependencies program signature root source firstStart firstCount firstInputs firstOutputs)
    (start count : Nat) (inputs outputs : List Nat) : WorkM (Second first start count inputs outputs) := do
  let call ← RuntimeAccessInterval.read source.calls.after source.lookup source.naturals
    (fun _ _ => none) root.block start count inputs outputs
  exactWork (Exact.charge (32*(first.call.interval.places.length+1)*(call.places.length+1)))
  if compatible : SourceTypes.AccessSyntax.compatible first.call.interval.places call.places = true then
    return ⟨call,← readRouting call first.nextEntry first.nextOffset,compatible⟩
  else throw .request

theorem Second.exclusive_disjoint {sources owner name dependencies program signature root source
    firstStart firstCount firstInputs firstOutputs first start count inputs outputs}
    (second : @Second sources owner name dependencies program signature root source
      firstStart firstCount firstInputs firstOutputs first start count inputs outputs)
    (a b : Nat) (left right : Place)
    (leftAt : first.call.interval.places[a]? = some left) (rightAt : second.call.places[b]? = some right)
    (exclusive : left.role = .excl ∨ right.role = .excl) (axis : Nat)
    (present : axis ∈ ((first.call.interval.frame.selected.map (·.wires))[a]?).getD []) :
    axis ∉ ((second.call.frame.selected.map (·.wires))[b]?).getD [] :=
  RuntimeAccessInterval.exclusive_actual_disjoint first.call.interval second.call second.compatible
    a b left right leftAt rightAt exclusive axis present

end QleisliKernel.Qirf.RuntimeAccessPartition
