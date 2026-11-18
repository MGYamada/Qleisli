import QleisliKernel.Qirf.RuntimeAccessSource
import QleisliKernel.Qirf.RuntimeOwnerMap
import QleisliKernel.Qirf.RuntimeBranchProjection
import QleisliKernel.Raw.ObservationOwnership

/-! Match the actual ordinary Raw splits and joins around a written access call.
The partition follows the original coordinates and restores the returned tokens
in reverse order, including distinct owners for empty ranges.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeAccessPartition
open QleisliKernel Finite SourceTypes.AccessSyntax
open RuntimeAccessSource (Parameter)
open QleisliKernel.Semantics.Raw (Port)

private structure Parent (Key : Type) where
  key : Key
  remainder : Option Nat
  removed : List (Nat × Nat) := []

private structure Picked (Key : Type) where
  parent : Key
  position : Option Nat
  token : Nat

private def findParent {Key : Type} [BEq Key] (parents : List (Parent Key)) (key : Key) : Option (Parent Key) :=
  parents.find? (fun parent => parent.key == key)

private def replaceParent {Key : Type} [BEq Key] (parents : List (Parent Key)) (next : Parent Key) :
    List (Parent Key) :=
  parents.map (fun parent => if parent.key == next.key then next else parent)

private def extract {Key : Type} (parent : Parent Key) (range : Option (Nat × Nat))
    (operations : List RuntimeInterval.Op) : Option (Parent Key × Picked Key × List RuntimeInterval.Op) := do
  let input ← parent.remainder
  match range with
  | none =>
    if !parent.removed.isEmpty then none else
      some ({parent with remainder := none},⟨parent.key,none,input⟩,operations)
  | some (start,stop) =>
    if stop > start && parent.removed.any (fun (i,j) => i < j && start < j && i < stop) then none else do
      let earlier := (parent.removed.map (fun (i,j) => min (start-i) (j-i))).sum
      let position := start-earlier
      let .pure (.split original leading tail leftBits) :: .pure (.split next picked suffix width) ::
        .pure (.join left right remainder) :: rest := operations | none
      if original != input || leftBits != position || next != tail ||
          width != stop-start || left != leading || right != suffix then none else
        some ({parent with remainder := some remainder,removed := (start,stop) :: parent.removed},
          ⟨parent.key,some position,picked⟩,rest)

private def restore {Key : Type} (parent : Parent Key) (picked : Picked Key) (returned : Nat)
    (operations : List RuntimeInterval.Op) : Option (Parent Key × List RuntimeInterval.Op) := do
  match picked.position with
  | none =>
    if parent.remainder.isSome then none else some ({parent with remainder := some returned},operations)
  | some position =>
    let input ← parent.remainder
    let .pure (.split original leading suffix leftBits) :: .pure (.join left token head) ::
      .pure (.join joined right output) :: rest := operations | none
    if original != input || leftBits != position || left != leading || token != returned ||
        joined != head || right != suffix then none else
      some ({parent with remainder := some output},rest)

private abbrev Extraction (Key : Type) := List (Parent Key) × List (Picked Key) × List RuntimeInterval.Op
private abbrev Restoration (Key : Type) := List (Parent Key) × List RuntimeInterval.Op

private def extractAll {Key : Type} [BEq Key] (entry : List (Key × Nat))
    (places : List (Key × Option (Nat × Nat))) (before : List RuntimeInterval.Op) :
    Option (List (Parent Key) × List (Picked Key)) := do
  let parents : List (Parent Key) := entry.map fun (key,token) => ⟨key,some token,[]⟩
  let (parents,picked,remaining) ← places.foldlM
    (fun (state : Extraction Key) (key,range) => do
      let (parents,picked,operations) := state
      let parent ← findParent parents key
      let (next,selection,rest) ← extract parent range operations
      return (replaceParent parents next,selection :: picked,rest)) (parents,[],before)
  if remaining.isEmpty then some (parents,picked) else none

private def restoreAll {Key : Type} [BEq Key] (parents : List (Parent Key))
    (picked : List (Picked Key)) (returned : List Nat) (after : List RuntimeInterval.Op) : Option (List Nat) := do
  if picked.length != returned.length then none else do
    let (restored,remaining) ← (picked.zip returned.reverse).foldlM
      (fun (state : Restoration Key) (selection,token) => do
        let (parents,operations) := state
        let parent ← findParent parents selection.parent
        let (next,rest) ← restore parent selection token operations
        return (replaceParent parents next,rest)) (parents,after)
    if remaining.isEmpty then restored.mapM (·.remainder) else none

def routingCount (places : List Place) : Nat := 3 * (places.filter (fun place => !place.whole)).length

/-- Replay the literal routing around the checked root call. Keep the original
port axes for the adjacent, unchanged-axis access proof. -/
def replay (entry : List Parameter) (places : List Place) (selected returned : List Port)
    (before after : List RuntimeInterval.Op) : Option (List Port) := do
  let (parents,picked) ← extractAll (entry.map fun parameter => (parameter.original.binder.text,parameter.port.token))
    (places.map fun place => (place.owner.binder.text,place.range)) before
  if picked.reverse.map (·.token) != selected.map (·.token) then none else do
    let restored ← restoreAll parents picked (returned.map (·.token)) after
    some ((entry.zip restored).map fun (parameter,token) => {parameter.port with token})

/-- Only structural splits and joins belong to the routing around a call. -/
def isRoute : RuntimeInterval.Op → Bool
  | .pure (.split ..) | .pure (.join ..) => true
  | _ => false

section
open Semantics

private theorem take_frame {state : RawTrace.Interface} {token : Nat}
    {port : Semantics.Raw.Port} {after : RawTrace.Interface}
    (read : RawTrace.take state token = some (port,after)) : after.frame = state.frame := by
  obtain ⟨_,_,returned⟩ := Option.bind_eq_some_iff.mp read
  cases Option.some.inj returned
  rfl

private theorem route_step {before after : Ownership.State} {op : RuntimeInterval.Op}
    (route : isRoute op = true) (step : Ownership.Step before op after) :
    after.frame = before.frame ∧ after.wires = before.wires := by
  cases op with
  | pure op =>
    cases step with
    | pure before op after body =>
      obtain ⟨events, ran⟩ := body.action
      cases op <;> simp [isRoute] at route
      case split token left right width =>
        refine ⟨?_,by simpa [Ownership.allocated] using body.wires⟩
        unfold RawTrace.step at ran
        obtain ⟨⟨port,middle⟩,take,returned⟩ := Option.bind_eq_some_iff.mp ran
        have shape := congrArg (fun result : RawTrace.Interface × List Semantics.Raw.Event => result.1.frame)
          (Option.some.inj returned)
        exact shape.symm.trans (take_frame take)
      case join left right token =>
        refine ⟨?_,by simpa [Ownership.allocated] using body.wires⟩
        unfold RawTrace.step at ran
        obtain ⟨⟨l,middle⟩,first,rest⟩ := Option.bind_eq_some_iff.mp ran
        obtain ⟨⟨r,last⟩,second,returned⟩ := Option.bind_eq_some_iff.mp rest
        have shape := congrArg (fun result : RawTrace.Interface × List Semantics.Raw.Event => result.1.frame)
          (Option.some.inj returned)
        exact shape.symm.trans ((take_frame second).trans (take_frame first))
  | _ => simp [isRoute] at route

/-- Split/join routing preserves the ordered live frame and issues no new
logical wire. This applies to any verified prefix, including zero-width
places, since the complete Raw ownership judgment tracks all live owners. -/
private theorem run_routes {before after : Ownership.State} {ops : List RuntimeInterval.Op}
    (run : Ownership.Run before ops after) (routes : ops.all isRoute = true) :
    after.frame = before.frame ∧ after.wires = before.wires := by
  induction ops generalizing before with
  | nil => cases run; exact ⟨rfl,rfl⟩
  | cons op ops ih =>
    cases run with
    | cons before op middle ops after valid head tail =>
      have decisions : isRoute op = true ∧ ops.all isRoute = true := by
        simpa only [List.all_cons,Bool.and_eq_true] using routes
      have first := route_step decisions.1 head
      have rest := ih tail decisions.2
      exact ⟨rest.1.trans first.1,rest.2.trans first.2⟩

private theorem initial_valid {before after : Ownership.State} {ops : List RuntimeInterval.Op}
    (run : Ownership.Run before ops after) : Ownership.Valid before := by
  cases run <;> assumption

/-- Literal extraction and restoration account for the same distinct live
wires throughout. New owner tokens do not justify dropping or double-counting
any logical storage in the checked Raw route. -/
theorem checked_route_storage {dependencies fuel before after ops}
    (read : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies fuel before ops) after)
    (routes : ops.all isRoute = true) :
    after.quantum.frame = before.quantum.frame ∧ after.quantum.seenWires = before.quantum.seenWires ∧
    (after.quantum.live.flatMap (·.wires)).length = (before.quantum.live.flatMap (·.wires)).length := by
  obtain ⟨work,left,ok⟩ := read
  have run := Raw.Observation.checkOps_ownership dependencies fuel before after ops work left ok
  have storage := run_routes run routes
  have final := run.final_valid
  have initial := initial_valid run
  exact ⟨storage.1,storage.2,final.count.trans ((congrArg List.length storage.1).trans initial.count.symm)⟩

end

private theorem extract_routes {Key : Type} {parent range operations next selection rest}
    (read : @extract Key parent range operations = some (next,selection,rest))
    (tail : rest.all isRoute = true) : operations.all isRoute = true := by
  unfold extract at read
  obtain ⟨input,_,read⟩ := Option.bind_eq_some_iff.mp read
  split at read
  · split at read
    · cases read
    · have same : operations = rest := congrArg (fun x : Parent Key × Picked Key × List RuntimeInterval.Op => x.2.2)
        (Option.some.inj read)
      rwa [same]
  · split at read
    · cases read
    · split at read
      · dsimp only at read
        split at read
        · cases read
        · have same := congrArg (fun x : Parent Key × Picked Key × List RuntimeInterval.Op => x.2.2)
            (Option.some.inj read)
          simp only [List.all_cons,isRoute,Bool.true_and] at ⊢
          simpa only [Prod.snd] using congrArg (fun ops => ops.all isRoute) same |>.trans tail
      · cases read

private theorem restore_routes {Key : Type} {parent selection returned operations next rest}
    (read : @restore Key parent selection returned operations = some (next,rest))
    (tail : rest.all isRoute = true) : operations.all isRoute = true := by
  unfold restore at read
  split at read
  · split at read
    · cases read
    · have same : operations = rest := congrArg (fun x : Parent Key × List RuntimeInterval.Op => x.2)
        (Option.some.inj read)
      rwa [same]
  · obtain ⟨input,_,read⟩ := Option.bind_eq_some_iff.mp read
    split at read
    · split at read
      · cases read
      · have same := congrArg (fun x : Parent Key × List RuntimeInterval.Op => x.2) (Option.some.inj read)
        simp only [List.all_cons,isRoute,Bool.true_and] at ⊢
        simpa only [Prod.snd] using congrArg (fun ops => ops.all isRoute) same |>.trans tail
    · cases read

private theorem fold_routes {α β : Type} (operations : β → List RuntimeInterval.Op)
    (step : β → α → Option β)
    (preserves : ∀ {before item after}, step before item = some after →
      (operations after).all isRoute = true → (operations before).all isRoute = true)
    (items : List α) {before after : β} (read : items.foldlM step before = some after)
    (tail : (operations after).all isRoute = true) : (operations before).all isRoute = true := by
  induction items generalizing before with
  | nil => rw [Option.some.inj read]; exact tail
  | cons first rest ih =>
    rw [List.foldlM_cons] at read
    obtain ⟨middle,stepped,remaining⟩ := Option.bind_eq_some_iff.mp read
    exact preserves stepped (ih remaining)

private theorem extractAll_routes {Key : Type} [BEq Key] {entry places before parents picked}
    (read : @extractAll Key _ entry places before = some (parents,picked)) : before.all isRoute = true := by
  unfold extractAll at read
  obtain ⟨⟨current,selected,remaining⟩,steps,read⟩ := Option.bind_eq_some_iff.mp read
  dsimp only at read
  split at read
  · rename_i done
    refine fold_routes (fun state : Extraction Key => state.2.2) _ ?_ _ steps ?_
    · intro ⟨_,_,operations⟩ ⟨_,_⟩ next stepRead stepTail
      obtain ⟨parent,_,stepRead⟩ := Option.bind_eq_some_iff.mp stepRead
      obtain ⟨⟨updated,selection,rest⟩,stepExtracted,stepRead⟩ := Option.bind_eq_some_iff.mp stepRead
      cases Option.some.inj stepRead
      exact extract_routes stepExtracted stepTail
    · have noRemaining : remaining = [] := List.isEmpty_iff.mp (by simpa using done)
      simp [noRemaining]
  · cases read

private theorem restoreAll_routes {Key : Type} [BEq Key] {parents picked returned after restored}
    (read : @restoreAll Key _ parents picked returned after = some restored) : after.all isRoute = true := by
  unfold restoreAll at read
  split at read
  · cases read
  · obtain ⟨⟨current,remaining⟩,steps,read⟩ := Option.bind_eq_some_iff.mp read
    dsimp only at read
    split at read
    · rename_i done
      refine fold_routes (fun state : Restoration Key => state.2) _ ?_ _ steps ?_
      · intro ⟨_,operations⟩ ⟨_,_⟩ next stepRead stepTail
        obtain ⟨parent,_,stepRead⟩ := Option.bind_eq_some_iff.mp stepRead
        obtain ⟨⟨updated,rest⟩,stepRestored,stepRead⟩ := Option.bind_eq_some_iff.mp stepRead
        cases Option.some.inj stepRead
        exact restore_routes stepRestored stepTail
      · have noRemaining : remaining = [] := List.isEmpty_iff.mp (by simpa using done)
        simp [noRemaining]
    · cases read

/-- A successful replay consumes both literal routing slices completely. -/
theorem replay_routes {entry places selected returned before after result}
    (read : replay entry places selected returned before after = some result) :
    before.all isRoute = true ∧ after.all isRoute = true := by
  unfold replay at read
  obtain ⟨⟨parents,picked⟩,extracted,read⟩ := Option.bind_eq_some_iff.mp read
  dsimp only at read
  split at read
  · cases read
  · obtain ⟨restored,reassembled,_⟩ := Option.bind_eq_some_iff.mp read
    exact ⟨extractAll_routes extracted,restoreAll_routes reassembled⟩

/-- A checked lexical place uses its original logical parent and concrete
coordinates. An empty selection and a whole zero-width owner are distinct. -/
structure ActivePlace where
  parent : RuntimeOwnerMap.Owner
  range : Option (Nat × Nat)

def activeCount (places : List ActivePlace) : Nat :=
  3 * (places.filter (fun place => place.range.isSome)).length

private def entryTokens (entry : RuntimeOwnerMap.Map) : List (RuntimeOwnerMap.Owner × Nat) :=
  entry.map fun binding => (binding.owner,binding.port.token)

private def placeRanges (places : List ActivePlace) : List (RuntimeOwnerMap.Owner × Option (Nat × Nat)) :=
  places.map fun place => (place.parent,place.range)

private def activeAxes (entry : RuntimeOwnerMap.Map) (places : List ActivePlace) : Option (List (List Nat)) :=
  places.mapM fun place => do
    let parent ← RuntimeOwnerMap.byOwner entry place.parent
    match place.range with
    | none => some parent.port.wires
    | some (start,stop) =>
      let [.bits width] := parent.owner.basis | none
      if start ≤ stop && stop ≤ width && width == parent.port.bits then
        some ((parent.port.wires.drop start).take (stop-start))
      else none

private def observationFields (state : RuntimeInterval.State) :=
  (state.quantum,state.classical,state.active,state.scope,state.nextScope,state.observe)

private theorem observationFields_inj {first second : RuntimeInterval.State}
    (same : observationFields first = observationFields second) : first = second := by
  cases first
  cases second
  simpa [observationFields] using same

private def stateFields (state : RuntimeInterval.State) : Nat :=
  state.quantum.live.length+state.quantum.seenTokens.length+state.quantum.seenWires.length+
    state.quantum.frame.length+state.classical.length+state.active.length+1

private def remainingPorts (state : RuntimeInterval.State) (parents : List (Parent RuntimeOwnerMap.Owner)) :
    Option (List (RuntimeOwnerMap.Owner × Option Port)) :=
  parents.mapM fun parent => do
    match parent.remainder with
    | none => some (parent.key,none)
    | some token =>
      let port ← state.quantum.live.find? (fun port => port.token == token)
      some (parent.key,some port)

structure ActiveEntry {dependencies program block start count}
    (inner : @RuntimeInterval.Checked dependencies program block start count)
    (entry : RuntimeOwnerMap.Map) (places : List ActivePlace) where
  bounded : activeCount places ≤ start
  preamble : RuntimeInterval.Checked block (start-activeCount places) (activeCount places)
  connected : preamble.after = inner.before
  frame : RuntimeOwnerMap.Checked (entry.map (·.owner)) preamble.before
  originalFrame : frame.bindings = entry
  parents : List (Parent RuntimeOwnerMap.Owner)
  picked : List (Picked RuntimeOwnerMap.Owner)
  extracted : extractAll (entryTokens entry) (placeRanges places)
    ((block.operations.drop (start-activeCount places)).take (activeCount places)) = some (parents,picked)
  selected : List Port
  selectedAt : PureInterval.ports inner.before (picked.reverse.map (·.token)) = some selected
  inputAxes : activeAxes entry places = some (selected.map (·.wires))
  remainders : List (RuntimeOwnerMap.Owner × Option Port)
  remaindersAt : remainingPorts inner.before parents = some remainders
  partition : (selected ++ remainders.filterMap Prod.snd).Perm inner.before.quantum.live

/-- Read the actual preamble and obtain the callee ports before running its
existing source check. Neither a proposed port nor a stale parent is accepted. -/
def readActiveEntry {dependencies program block start count}
    (inner : @RuntimeInterval.Checked dependencies program block start count)
    (entry : RuntimeOwnerMap.Map) (places : List ActivePlace) : WorkM (ActiveEntry inner entry places) := do
  guard (places.length ≤ 64 && entry.length ≤ 128) .limit
  let routeCount := activeCount places
  if bounded : routeCount ≤ start then
    let preamble ← RuntimeInterval.check block (start-routeCount) routeCount
    let roles := entry.map (·.owner)
    let roleFields := Raw.OwnerFlow.fields (roles ++ places.map (·.parent))
    exactWork (Exact.charge (32*((roleFields+1)*(entry.length+places.length+1)+
      (entry.length+places.length+1)*(inner.before.quantum.live.length+places.length+1)+
      stateFields preamble.after+stateFields inner.before)))
    if connected : observationFields preamble.after = observationFields inner.before then
      let frame ← RuntimeOwnerMap.checkBindings roles preamble.before entry
      match extracted : extractAll (entryTokens entry) (placeRanges places)
          ((block.operations.drop (start-routeCount)).take routeCount) with
      | none => throw .request
      | some (parents,picked) =>
        match selectedAt : PureInterval.ports inner.before (picked.reverse.map (·.token)),
            remaindersAt : remainingPorts inner.before parents with
        | some selected,some remainders =>
          if axes : activeAxes entry places = some (selected.map (·.wires)) then
            if partition : (selected ++ remainders.filterMap Prod.snd).Perm inner.before.quantum.live then
              return ⟨bounded,preamble,observationFields_inj connected,frame.val,frame.property,parents,picked,
                extracted,selected,selectedAt,axes,remainders,remaindersAt,partition⟩
            else throw .request
          else throw .request
        | _,_ => throw .request
    else throw .request
  else throw .request

theorem ActiveEntry.routes {dependencies program block start count inner entry places}
    (opening : @ActiveEntry dependencies program block start count inner entry places) :
    ((block.operations.drop (start-activeCount places)).take (activeCount places)).all isRoute = true :=
  extractAll_routes opening.extracted

/-- The checked extraction changes owner tokens while preserving every live
logical wire and its ordered frame. -/
theorem ActiveEntry.storage {dependencies program block start count inner entry places}
    (opening : @ActiveEntry dependencies program block start count inner entry places) :
    opening.preamble.after.quantum.frame = opening.preamble.before.quantum.frame ∧
    opening.preamble.after.quantum.seenWires = opening.preamble.before.quantum.seenWires ∧
    (opening.preamble.after.quantum.live.flatMap (·.wires)).length =
      (opening.preamble.before.quantum.live.flatMap (·.wires)).length :=
  checked_route_storage opening.preamble.intervalRead opening.routes

structure ActiveExit {dependencies program block start count inner entry places}
    (opening : @ActiveEntry dependencies program block start count inner entry places)
    (returned : List Port) where
  bounded : start+count+activeCount places ≤ block.operations.length
  returnedAt : PureInterval.ports inner.after (returned.map (·.token)) = some returned
  widths : returned.map (·.bits) = opening.selected.map (·.bits)
  spectators : PureInterval.spectators inner.before (opening.selected.map (·.token)) =
    PureInterval.spectators inner.after (returned.map (·.token))
  tokens : List Nat
  reassembled : restoreAll opening.parents opening.picked (returned.map (·.token))
    ((block.operations.drop (start+count)).take (activeCount places)) = some tokens
  after : RuntimeInterval.State
  original : RuntimeInterval.Computed
    (Raw.Observation.checkOps dependencies block.fuel inner.after
      ((block.operations.drop (start+count)).take (activeCount places))) after
  ports : List Port
  portsAt : PureInterval.ports after tokens = some ports
  parentWidths : ports.map (·.bits) = entry.map (·.port.bits)
  restored : RuntimeOwnerMap.Map
  bound : restored = (entry.zip ports).map (fun (parent,port) => ⟨parent.owner,port⟩)
  frame : RuntimeOwnerMap.Checked (entry.map (·.owner)) after
  originalFrame : frame.bindings = restored

/-- Replay the exact suffix from the actual callee exit. The returned tokens
are spliced into their original parent coordinates, preserving untouched
ports and the identity of every zero-width parent. -/
def readActiveExit {dependencies program block start count inner entry places}
    (opening : @ActiveEntry dependencies program block start count inner entry places)
    (returned : List Port) : WorkM (ActiveExit opening returned) := do
  let routeCount := activeCount places
  let operations := (block.operations.drop (start+count)).take routeCount
  exactWork (Exact.charge (32*((entry.length+places.length+returned.length+1)^2+
    (returned.length+1)*(inner.before.quantum.live.length+inner.after.quantum.live.length+1)+
    (places.length+1)*Raw.OwnerFlow.fields (entry.map (·.owner) ++ places.map (·.parent))+
    block.operations.length+1)))
  if bounded : start+count+routeCount ≤ block.operations.length then
    let returnedTokens := returned.map (·.token)
    if valid : PureInterval.ports inner.after returnedTokens = some returned ∧
        returned.map (·.bits) = opening.selected.map (·.bits) ∧
        PureInterval.spectators inner.before (opening.selected.map (·.token)) =
          PureInterval.spectators inner.after returnedTokens then
      guard (decide returnedTokens.Nodup) .request
      match reassembled : restoreAll opening.parents opening.picked returnedTokens operations with
      | none => throw .request
      | some tokens =>
        let after ← SourceTypes.NaturalAffine.witness
          (Raw.Observation.checkOps dependencies block.fuel inner.after operations)
        match portsAt : PureInterval.ports after.val tokens with
        | none => throw .request
        | some ports =>
          if widths : ports.map (·.bits) = entry.map (·.port.bits) then
            let restored : RuntimeOwnerMap.Map := (entry.zip ports).map fun (parent,port) => ⟨parent.owner,port⟩
            let frame ← RuntimeOwnerMap.checkBindings (entry.map (·.owner)) after.val restored
            return ⟨bounded,valid.1,valid.2.1,valid.2.2,tokens,reassembled,after.val,
              by with_reducible exact after.property,ports,portsAt,widths,restored,rfl,frame.val,frame.property⟩
          else throw .request
    else throw .request
  else throw .request

theorem ActiveExit.routes {dependencies program block start count inner entry places opening returned}
    (closing : @ActiveExit dependencies program block start count inner entry places opening returned) :
    ((block.operations.drop (start+count)).take (activeCount places)).all isRoute = true :=
  restoreAll_routes closing.reassembled

/-- The checked reassembly introduces no wire and releases no live storage,
including when it restores an owner with zero-width selected axes. -/
theorem ActiveExit.storage {dependencies program block start count inner entry places opening returned}
    (closing : @ActiveExit dependencies program block start count inner entry places opening returned) :
    closing.after.quantum.frame = inner.after.quantum.frame ∧
    closing.after.quantum.seenWires = inner.after.quantum.seenWires ∧
    (closing.after.quantum.live.flatMap (·.wires)).length =
      (inner.after.quantum.live.flatMap (·.wires)).length :=
  checked_route_storage closing.original closing.routes

private def renameParents {Key : Type} (parents : List (Parent Key))
    (renames : List (Nat × Nat)) : Option (List (Parent Key)) :=
  parents.mapM fun parent => do
    match parent.remainder with
    | none => return parent
    | some token =>
      let (_,output) ← renames.find? (fun rename => rename.1 == token)
      return {parent with remainder := some output}

/-- The same ordered suffix, with parked tokens coming from independently
checked original spectator phis. Full named-body semantics remain separate. -/
structure BranchExit {dependencies program block offset entry places roles}
    {branch : @RuntimeInterval.Branch dependencies program block offset}
    (opening : ActiveEntry branch.interval entry places)
    {inputFrame : RuntimeOwnerMap.Checked roles branch.interval.before}
    {ordinary : RuntimeOrdinaryBody.State}
    (projected : RuntimeBranchProjection.Checked branch inputFrame (opening.selected.map (·.token)) ordinary)
    (returned : List Port) where
  bounded : offset+1+activeCount places ≤ block.operations.length
  selectedExit : returned.Perm projected.prepared.whole.state.quantum.live
  returnedAt : PureInterval.ports branch.interval.after (returned.map (·.token)) = some returned
  widths : returned.map (·.bits) = opening.selected.map (·.bits)
  covered : (opening.parents.filterMap (·.remainder)).Perm (projected.renames.map Prod.fst)
  parents : List (Parent RuntimeOwnerMap.Owner)
  transported : renameParents opening.parents projected.renames = some parents
  tokens : List Nat
  reassembled : restoreAll parents opening.picked (returned.map (·.token))
    ((block.operations.drop (offset+1)).take (activeCount places)) = some tokens
  after : RuntimeInterval.State
  original : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies block.fuel branch.interval.after
    ((block.operations.drop (offset+1)).take (activeCount places))) after
  ports : List Port
  portsAt : PureInterval.ports after tokens = some ports
  restored : RuntimeOwnerMap.Checked (entry.map (·.owner)) after
  ordered : restored.bindings = (entry.zip ports).map (fun (parent,port) => ⟨parent.owner,port⟩)
  literal : RuntimeInterval.Checked block (offset-activeCount places) (activeCount places+1+activeCount places)
  literalBefore : literal.before = opening.preamble.before
  literalAfter : literal.after = after

def readBranchExit {dependencies program block offset entry places roles}
    {branch : @RuntimeInterval.Branch dependencies program block offset}
    (opening : ActiveEntry branch.interval entry places)
    {inputFrame : RuntimeOwnerMap.Checked roles branch.interval.before}
    {ordinary : RuntimeOrdinaryBody.State}
    (projected : RuntimeBranchProjection.Checked branch inputFrame (opening.selected.map (·.token)) ordinary)
    (returned : List Port) : WorkM (BranchExit opening projected returned) := do
  let size := activeCount places
  let operations := (block.operations.drop (offset+1)).take size
  let renames := projected.renames
  let tokens := returned.map (·.token)
  exactWork (Exact.charge (32*((entry.length+places.length+returned.length+renames.length+1)^2+
    (returned.length+1)*branch.interval.after.quantum.live.length+
    (places.length+1)*Raw.OwnerFlow.fields (entry.map (·.owner) ++ places.map (·.parent))+
    block.operations.length+1)))
  if valid : offset+1+size ≤ block.operations.length ∧
      returned.Perm projected.prepared.whole.state.quantum.live ∧
      PureInterval.ports branch.interval.after tokens = some returned ∧
      returned.map (·.bits) = opening.selected.map (·.bits) ∧
      (opening.parents.filterMap (·.remainder)).Perm (renames.map Prod.fst) then
    match transported : renameParents opening.parents renames with
    | none => throw .request
    | some parents =>
      match reassembled : restoreAll parents opening.picked tokens operations with
      | none => throw .request
      | some finalTokens =>
        let after ← SourceTypes.NaturalAffine.witness
          (Raw.Observation.checkOps dependencies block.fuel branch.interval.after operations)
        match portsAt : PureInterval.ports after.val finalTokens with
        | none => throw .request
        | some ports =>
          let restored := (entry.zip ports).map (fun (parent,port) => ⟨parent.owner,port⟩)
          let checked ← RuntimeOwnerMap.checkBindings (entry.map (·.owner)) after.val restored
          let literal ← RuntimeInterval.check block (offset-size) (size+1+size)
          exactWork (Exact.charge (32*(stateFields literal.before+stateFields literal.after+
            stateFields opening.preamble.before+stateFields after.val+1)))
          if endpoints : decide (observationFields literal.before = observationFields opening.preamble.before) &&
              decide (observationFields literal.after = observationFields after.val) then
            have same := Bool.and_eq_true_iff.mp endpoints
            return ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2,parents,transported,
              finalTokens,reassembled,after.val,by with_reducible exact after.property,ports,portsAt,
              checked.val,checked.property,literal,observationFields_inj (of_decide_eq_true same.1),
              observationFields_inj (of_decide_eq_true same.2)⟩
          else throw .request
  else throw .request

theorem BranchExit.routes {dependencies program block offset entry places roles}
    {branch : @RuntimeInterval.Branch dependencies program block offset}
    {opening : ActiveEntry branch.interval entry places}
    {inputFrame : RuntimeOwnerMap.Checked roles branch.interval.before}
    {ordinary : RuntimeOrdinaryBody.State}
    {projected : RuntimeBranchProjection.Checked branch inputFrame (opening.selected.map (·.token)) ordinary}
    {returned : List Port} (closing : BranchExit opening projected returned) :
    ((block.operations.drop (offset+1)).take (activeCount places)).all isRoute = true :=
  restoreAll_routes closing.reassembled

theorem BranchExit.storage {dependencies program block offset entry places roles}
    {branch : @RuntimeInterval.Branch dependencies program block offset}
    {opening : ActiveEntry branch.interval entry places}
    {inputFrame : RuntimeOwnerMap.Checked roles branch.interval.before}
    {ordinary : RuntimeOrdinaryBody.State}
    {projected : RuntimeBranchProjection.Checked branch inputFrame (opening.selected.map (·.token)) ordinary}
    {returned : List Port} (closing : BranchExit opening projected returned) :
    closing.after.quantum.frame = branch.interval.after.quantum.frame ∧
    closing.after.quantum.seenWires = branch.interval.after.quantum.seenWires ∧
    (closing.after.quantum.live.flatMap (·.wires)).length =
      (branch.interval.after.quantum.live.flatMap (·.wires)).length :=
  checked_route_storage closing.original closing.routes

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
