import QleisliKernel.Qirf.RuntimeNamedFrameAxes
import QleisliKernel.Raw.ObservationOwnership

/-! Named-call returns use the source result order, while the local Raw
program finishes in its live-port order. Both orders include Unit ports.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedReturnAxes
open QleisliKernel Finite SourceTypes
open QleisliKernel.Semantics.Raw (Port)
open RuntimeOwnerMap (Binding Map Owner)
open RuntimeForestCode (portAxes)

private def move (owners : List Owner) (binding : Binding) : Except String Binding := do
  let owner ← SourceRuntimeValues.mappedOwner owners binding.owner
  pure ⟨owner,binding.port⟩

private theorem move_order (owners : List Owner) (input output : Map) (ok : input.mapM (move owners) = .ok output) :
    input.map (·.port) = output.map (·.port) ∧
    input.mapM (fun b => SourceRuntimeValues.mappedOwner owners b.owner) = .ok (output.map (·.owner)) := by
  induction input generalizing output with
  | nil =>
    have same : [] = output := Except.ok.inj ok
    subst output
    exact ⟨rfl,rfl⟩
  | cons b rest ih =>
    cases owner : SourceRuntimeValues.mappedOwner owners b.owner with
    | error e => simp [List.mapM_cons,move,owner,bind,Except.bind] at ok
    | ok o =>
      cases tail : rest.mapM (move owners) with
      | error e => simp [List.mapM_cons,move,owner,tail,bind,Except.bind,pure,Except.pure] at ok
      | ok later =>
        have same : (⟨o,b.port⟩ : Binding) :: later = output := by
          simpa [List.mapM_cons,move,owner,tail,bind,Except.bind,pure,Except.pure] using ok
        subst output
        have restOrder := ih later tail
        exact ⟨congrArg (List.cons b.port) restOrder.1,by
          simp [List.mapM_cons,owner,restOrder.2,bind,Except.bind,pure,Except.pure]⟩

private theorem selected_lookup (live ports : List Port)
    (read : PureInterval.portsOf live (ports.map (·.token)) = some ports) :
    ∀ port ∈ ports, live.find? (fun p => p.token == port.token) = some port := by
  induction ports with
  | nil => simp
  | cons first rest ih =>
    cases head : live.find? (fun p => p.token == first.token) with
    | none => simp [PureInterval.portsOf,List.mapM_cons,head] at read
    | some p =>
      cases tail : PureInterval.portsOf live (rest.map (·.token)) with
      | none =>
        unfold PureInterval.portsOf at tail read
        simp [List.mapM_cons,head,tail] at read
      | some later =>
        have combined : p :: later = first :: rest := by
          unfold PureInterval.portsOf at tail read
          simpa [List.mapM_cons,head,tail] using read
        obtain ⟨rfl,rfl⟩ := List.cons.inj combined
        intro port member
        rcases List.mem_cons.mp member with rfl | further
        · exact head
        · exact ih tail _ further

private theorem same_members (live first second : List Port)
    (a : PureInterval.portsOf live (first.map (·.token)) = some first)
    (b : PureInterval.portsOf live (second.map (·.token)) = some second)
    (spectators : live.filter (fun p => !(first.map Port.token).contains p.token) =
      live.filter (fun p => !(second.map Port.token).contains p.token)) : first ⊆ second := by
  intro p mem
  have found := selected_lookup live first a p mem
  by_cases token : p.token ∈ second.map Port.token
  · obtain ⟨q,member,same⟩ := List.mem_map.mp token
    have qFound := selected_lookup live second b q member
    rw [same] at qFound
    rwa [← Option.some.inj (qFound.symm.trans found)]
  · have liveP := List.mem_of_find?_eq_some found
    have spectator : p ∈ live.filter (fun q => !(second.map Port.token).contains q.token) :=
      List.mem_filter.mpr ⟨liveP,by simpa using token⟩
    rw [← spectators] at spectator
    have missing : p.token ∉ first.map Port.token := by simpa using (List.mem_filter.mp spectator).2
    exact False.elim (missing (List.mem_map_of_mem mem))

private theorem perm_of_members (a b : List Port) (au : a.Nodup) (bu : b.Nodup) (ab : a ⊆ b) (ba : b ⊆ a) :
    a.Perm b := by
  apply List.perm_iff_count.mpr
  intro p
  by_cases h : p ∈ a
  · have left := List.count_pos_iff.mpr h
    have right := List.count_pos_iff.mpr (ab h)
    have l := List.nodup_iff_count.mp au p
    have r := List.nodup_iff_count.mp bu p
    omega
  · rw [List.count_eq_zero_of_not_mem h,List.count_eq_zero_of_not_mem (fun hb => h (ba hb))]

private theorem ports_unique {ports : List Port} (unique : (ports.map Port.token).Nodup) : ports.Nodup :=
  List.Pairwise.of_map Port.token (fun _ _ different same => different (congrArg Port.token same)) unique

variable {dependencies : List Semantics.Finite.Dependency} {program : Semantics.Observation.Program}
  {block : RuntimeInterval.Block dependencies program} {start count : Nat} {inputs : List Nat}
  {sources : Sources} {caller : String} {event : SourceRuntimeContext.NamedEvent sources caller}
  {before child : RuntimeNamedBoundary.SourceState} {retired : List Owner} {result : SourceRuntimeValues.Value}

/-- Retains whole ports in the child's actual binding order. The list of
transported source owners is exactly the written result value, including Unit. -/
theorem source_order {interval : RuntimeInterval.Checked block start count}
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired result) :
    boundary.returned = child.bindings.map (·.port) ∧
    child.bindings.mapM (fun b => SourceRuntimeValues.mappedOwner event.ownerMap b.owner) =
      .ok (SourceRuntimeValues.valueOwners event.value) := by
  have moved := move_order event.ownerMap child.bindings boundary.mapped boundary.mappedRead
  exact ⟨boundary.returnRead.trans moved.1.symm,moved.2.trans (congrArg Except.ok boundary.resultOwners)⟩

private theorem return_perm {interval : RuntimeInterval.Checked block start count}
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired result)
    (native : List Port) (selected : PureInterval.ports interval.after (native.map (·.token)) = some native)
    (unique : (native.map Port.token).Nodup)
    (spectators : PureInterval.spectators interval.before inputs =
      PureInterval.spectators interval.after (native.map (·.token))) : boundary.returned.Perm native := by
  have ordered := boundary.afterFrame.tokensDistinct
  rw [boundary.sameAfter,boundary.afterBindings,List.map_append] at ordered
  have mapped := (List.nodup_append.mp ordered).2.1
  have sourceUnique : (boundary.returned.map Port.token).Nodup := by
    rw [boundary.returnRead,List.map_map]
    exact mapped
  have same := boundary.spectators.symm.trans spectators
  exact perm_of_members _ _ (ports_unique sourceUnique) (ports_unique unique)
    (same_members _ _ _ boundary.atExit selected same) (same_members _ _ _ selected boundary.atExit same.symm)

theorem pure_ports (scope : RuntimeCallInterval.Checked block start count inputs)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired result) :
    boundary.returned.Perm scope.returned := by
  obtain ⟨w,left,ran⟩ := scope.nativeRead
  have valid := (Raw.Ownership.valid _ (Raw.Observation.checkOps_invariants _ _ _ _ _ w left ran).1).owners
  exact return_perm boundary scope.returned scope.atExit (by rw [scope.complete]; exact valid) scope.spectators

theorem mixed_ports {ordinary effect} (scope : RuntimeCallScope.Checked block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired result) :
    boundary.returned.Perm scope.returned := by
  obtain ⟨w,left,ran⟩ := scope.nativeRead
  have valid := (Raw.Ownership.valid _ (Raw.Observation.checkOps_invariants _ _ _ _ _ w left ran).1).owners
  exact return_perm boundary scope.returned scope.atExit (by rw [scope.complete]; exact valid) scope.spectators

private theorem lookup_indices (frame wires : List Nat) (f : Nat → Nat) (inside : wires ⊆ frame) :
    (wires.map frame.idxOf).mapM (fun i => (frame.map f)[i]?) = some (wires.map f) := by
  induction wires with
  | nil => rfl
  | cons first rest ih =>
    have bounds := List.cons_subset.mp inside
    have firstAt : (frame.map f)[frame.idxOf first]? = some (f first) := by
      rw [List.getElem?_map,RuntimeNamedFrameAxes.wireLookup frame bounds.1] <;> rfl
    simp only [List.map_cons,List.mapM_cons,firstAt,ih bounds.2] <;> rfl

private theorem self_indices (wires : List Nat) (distinct : wires.Nodup) :
    wires.map wires.idxOf = List.range wires.length := by
  induction wires with
  | nil => rfl
  | cons w rest ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
    rw [List.map_cons,List.idxOf_cons_self,List.length_cons,List.range_succ_eq_map,← ih tail,List.map_map]
    apply congrArg (List.cons 0)
    apply List.map_eq_map_iff.mpr
    intro v member
    have different : w ≠ v := fun same => fresh (same.symm ▸ member)
    simp [List.idxOf_cons,cond_eq_ite,different]

/-- The output coordinate permutation goes from source result order to
the order of the actual local program outputs. Together these maps recover
the enclosing axes for every returned wire without dropping a spectator. -/
structure Axes (localState parent : Raw.State) (source native : List Port) : Prop where
  ports : source.Perm native
  permutation : (portAxes (native.flatMap Port.wires) source).Perm (List.range (native.flatMap Port.wires).length)
  parentBound : ∀ i ∈ portAxes parent.frame source, i < parent.frame.length
  nativeToSource :
    (portAxes (native.flatMap Port.wires) source).mapM (fun i => (portAxes localState.frame native)[i]?) =
      some (portAxes localState.frame source)
  localToParent :
    (portAxes localState.frame source).mapM (fun i => (localState.frame.map parent.frame.idxOf)[i]?) =
      some (portAxes parent.frame source)

private theorem axesFrom {localState parent : Raw.State} {source native : List Port} (order : source.Perm native)
    (complete : native = localState.live) (valid : Raw.stateValid localState = true)
    (ambient : source.flatMap Port.wires ⊆ parent.frame) : Axes localState parent source native := by
  have wires := order.flatMap_right Port.wires
  have sub := wires.subset
  have unique : (native.flatMap Port.wires).Nodup := by
    rw [complete]
    exact (Raw.Ownership.valid _ valid).exclusive
  refine ⟨order,?_,?_,lookup_indices _ _ localState.frame.idxOf sub,?_⟩
  · exact (wires.map (native.flatMap Port.wires).idxOf).trans (List.Perm.of_eq (self_indices _ unique))
  · intro i member
    obtain ⟨wire,inside,rfl⟩ := List.mem_map.mp member
    exact List.idxOf_lt_length_of_mem (ambient inside)
  ·
    have inLocal : source.flatMap Port.wires ⊆ localState.frame := by
      intro w member
      apply (Raw.Ownership.valid _ valid).covered
      change w ∈ localState.live.flatMap Port.wires
      rw [← complete]
      exact sub member
    exact lookup_indices _ _ parent.frame.idxOf inLocal

private theorem ambientWires {interval : RuntimeInterval.Checked block start count}
    (boundary : RuntimeNamedBoundary.Checked interval inputs event before child retired result) :
    boundary.returned.flatMap Port.wires ⊆ interval.after.quantum.frame := by
  obtain ⟨work,left,ran⟩ := interval.intervalRead
  have valid := Raw.Ownership.valid _ (Raw.Observation.checkOps_invariants _ _ _ _ _ work left ran).1
  intro w member
  obtain ⟨p,found,onPort⟩ := List.mem_flatMap.mp member
  exact valid.covered w (List.mem_flatMap.mpr ⟨p,List.mem_of_find?_eq_some (selected_lookup _ _ boundary.atExit p found),onPort⟩)

theorem pure_axes (scope : RuntimeCallInterval.Checked block start count inputs)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired result) :
    Axes scope.localAfter.quantum scope.interval.after.quantum boundary.returned scope.returned := by
  obtain ⟨w,left,ran⟩ := scope.nativeRead
  exact axesFrom (pure_ports scope boundary) scope.complete (Raw.Observation.checkOps_invariants _ _ _ _ _ w left ran).1
    (ambientWires boundary)

theorem mixed_axes {ordinary effect} (scope : RuntimeCallScope.Checked block start count inputs ordinary effect)
    (boundary : RuntimeNamedBoundary.Checked scope.interval inputs event before child retired result) :
    Axes scope.localAfter.quantum scope.interval.after.quantum boundary.returned scope.returned := by
  obtain ⟨w,left,ran⟩ := scope.nativeRead
  exact axesFrom (mixed_ports scope boundary) scope.complete (Raw.Observation.checkOps_invariants _ _ _ _ _ w left ran).1
    (ambientWires boundary)

-- Only the final interface is compared. A classical branch's merged
-- interface is determined by its literal quantum phis, independently of
-- its histories, issued identities and amplitudes.
private theorem interfaceEq {a b : Semantics.RawTrace.Interface} (live : a.live = b.live)
    (frame : a.frame = b.frame) : a = b := by cases a; cases b; simp_all

private theorem erasedSame {a b input x y left right}
    (same : Semantics.Ownership.State.interface a = b.interface) (valid : Semantics.Ownership.Valid a)
    (l : Semantics.Ownership.Erase a input x left) (r : Semantics.Ownership.Erase b input y right) :
    left.interface = right.interface := by
  have live : a.live = b.live := congrArg Semantics.RawTrace.Interface.live same
  have frame : a.frame = b.frame := congrArg Semantics.RawTrace.Interface.frame same
  have first := RuntimeNamedFrameAxes.tokenLookup a.live x valid.owners l.present
  have second := RuntimeNamedFrameAxes.tokenLookup a.live y valid.owners (live.symm ▸ r.present)
  rw [l.owner] at first
  rw [r.owner] at second
  have port := Option.some.inj (first.symm.trans second)
  rw [l.result,r.result]
  simp only [Semantics.Ownership.State.interface,live,frame,port]

private theorem inputInterface {a b ports} (init : Semantics.Ownership.Inputs a ports b) :
    b.interface = ⟨a.live ++ ports,a.frame ++ ports.flatMap Port.wires⟩ := by
  induction init with
  | nil => simp [Semantics.Ownership.State.interface]
  | cons _ _ _ _ _ head _ ih =>
    rw [ih,head.result]
    simp [List.append_assoc]

private theorem stepSame {a b op left right} (same : Semantics.Ownership.State.interface a = b.interface)
    (valid : Semantics.Ownership.Valid a) (l : Semantics.Ownership.Step a op left)
    (r : Semantics.Ownership.Step b op right) : left.interface = right.interface := by
  cases l with
  | pure _ _ _ first =>
    cases r with
    | pure _ _ _ second =>
      obtain ⟨_,x⟩ := first.action
      obtain ⟨_,y⟩ := second.action
      rw [← same] at y
      exact congrArg Prod.fst (Option.some.inj (x.symm.trans y))
  | measure _ _ _ _ _ first _ =>
    cases r with | measure _ _ _ _ _ second _ => exact erasedSame same valid first second
  | discard _ _ _ _ first =>
    cases r with | discard _ _ _ _ second => exact erasedSame same valid first second
  | reset _ _ _ _ _ _ _ erased _ allocated =>
    cases r with
    | reset _ _ _ _ _ _ _ erased' _ allocated' =>
      have middle := erasedSame same valid erased erased'
      have live := congrArg Semantics.RawTrace.Interface.live middle
      have frame := congrArg Semantics.RawTrace.Interface.frame middle
      rw [allocated.result,allocated'.result]
      exact interfaceEq (congrArg (· ++ _) live) (congrArg (· ++ _) frame)
  | branch _ _ _ _ _ _ _ _ _ _ _ _ merge =>
    cases r with
    | branch _ _ _ _ _ _ _ _ _ _ _ _ merge' =>
      exact (inputInterface merge).trans (inputInterface merge').symm
  | constant => cases r; exact same
  | not => cases r; exact same
  | xor => cases r; exact same
  | and => cases r; exact same

private theorem runSame (ops : List Semantics.Observation.Op) {a b left right}
    (same : Semantics.Ownership.State.interface a = b.interface) (l : Semantics.Ownership.Run a ops left)
    (r : Semantics.Ownership.Run b ops right) : left.interface = right.interface := by
  induction ops generalizing a b left right with
  | nil => cases l; cases r; exact same
  | cons op ops ih =>
    cases l with
    | cons _ _ _ _ _ valid step tail =>
      cases r with
      | cons _ _ _ _ _ _ step' tail' => exact ih (stepSame same valid step step') tail tail'

private theorem actualRun (prepared : RuntimeInterval.Prepared dependencies program) :
    ∃ initial : Raw.Observation.State, initial.quantum.reference = Semantics.RawTrace.initial program.inputs ∧
      Semantics.Ownership.Run (Raw.Ownership.view initial.quantum) program.operations
        (Raw.Ownership.view prepared.whole.state.quantum) := by
  obtain ⟨_,_,checked⟩ := prepared.verified
  unfold Raw.Observation.verify at checked
  obtain ⟨_,start,_,h⟩ := Finite.bind_success _ _ _ _ _ checked
  obtain ⟨_,_,quantum,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨initial,afterInputs,ordinary,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨body,_,operations,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  have returned := (Finite.pure_success _ _ _ _ h).1
  have initialized : RuntimeInterval.Computed (PureInterval.initial program) initial := by
    refine ⟨start,afterInputs,?_⟩
    unfold PureInterval.initial
    rw [Finite.bind_run,quantum]
    exact ordinary
  refine ⟨initial,(RuntimeNamedFrameAxes.initialized initialized).1,?_⟩
  rw [returned]
  exact Raw.Observation.checkOps_ownership _ _ _ _ _ _ _ operations

private theorem preparedInterface (prepared : RuntimeInterval.Prepared dependencies program)
    {entry after : Raw.Observation.State} (opening : entry.quantum.reference = Semantics.RawTrace.initial program.inputs)
    (read : RuntimeInterval.Computed (Raw.Observation.checkOps dependencies 65 entry program.operations) after) :
    prepared.whole.prepared.state = after.quantum.reference := by
  obtain ⟨initial,layout,verified⟩ := actualRun prepared
  obtain ⟨work,left,ran⟩ := read
  have localRun := Raw.Observation.checkOps_ownership _ _ _ _ _ work left ran
  have same := runSame program.operations (a := Raw.Ownership.view initial.quantum)
    (b := Raw.Ownership.view entry.quantum) (layout.trans opening.symm) verified localRun
  exact (interfaceEq prepared.originalRoot.live prepared.originalRoot.frame).trans same

private theorem finishWires (live ports : List Port)
    (findAll : ∀ p ∈ ports, live.find? (fun q => q.token == p.token) = some p) :
    (ports.map Port.token).flatMap (fun token => ((live.find? (fun p => p.token == token)).map Port.wires).getD []) =
      ports.flatMap Port.wires := by
  induction ports with
  | nil => rfl
  | cons first rest ih =>
    have one := findAll first List.mem_cons_self
    have later := ih (fun p member => findAll p (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,List.flatMap_cons,one,Option.map_some,Option.getD_some,later]

structure Finish (prepared : RuntimeInterval.Prepared dependencies program) (localState : Raw.State) (native : List Port) : Prop where
  interface : prepared.whole.prepared.state = localState.reference
  literal : ∃ events, Semantics.Observation.readOps 65 (Semantics.RawTrace.initial program.inputs) program.operations =
      some (localState.reference,events) ∧ prepared.whole.prepared.events = events ++
        [.pure (.reorder localState.frame.length (portAxes localState.frame native))]

private theorem finish (prepared : RuntimeInterval.Prepared dependencies program) {localState : Raw.State} (native : List Port)
    (actual : prepared.whole.prepared.state = localState.reference)
    (complete : native = localState.live) (outputs : program.outputs = native.map Port.token)
    (unique : (localState.live.map Port.token).Nodup) : Finish prepared localState native := by
  have wires := finishWires localState.live native (fun p member =>
    RuntimeNamedFrameAxes.tokenLookup _ _ unique (complete ▸ member))
  have original := prepared.originalRoot.reader
  unfold Semantics.Observation.read at original
  cases body : Semantics.Observation.readOps 65 (Semantics.RawTrace.initial program.inputs) program.operations with
  | none => simp [body] at original
  | some pair =>
    obtain ⟨state,events⟩ := pair
    let outWires := program.outputs.flatMap (fun token =>
      ((state.live.find? (fun p => p.token == token)).map Port.wires).getD [])
    let output : Semantics.Observation.Prepared := ⟨state,events ++ [.pure (.reorder state.frame.length
      (Semantics.RawTrace.axes state outWires))],(Semantics.RawTrace.initial program.inputs).frame.length⟩
    have recorded : output = prepared.whole.prepared :=
      Option.some.inj (by simpa only [body] using original : some output = some prepared.whole.prepared)
    have stateEq : state = localState.reference :=
      (congrArg Semantics.Observation.Prepared.state recorded).trans actual
    have emitted := (congrArg Semantics.Observation.Prepared.events recorded).symm
    refine ⟨actual,events,?_,?_⟩
    · simpa only [stateEq] using body
    · simpa only [output,outWires,stateEq,Raw.State.reference,outputs,wires,Semantics.RawTrace.axes,
        RuntimeForestCode.portAxes] using emitted

/-- The reorder is the final event of the verified child program itself. -/
theorem pure_finish (scope : RuntimeCallInterval.Checked block start count inputs) :
    Finish scope.prepared scope.localAfter.quantum scope.returned := by
  obtain ⟨w,left,ran⟩ := scope.nativeRead
  have valid := (Raw.Ownership.valid _ (Raw.Observation.checkOps_invariants _ _ _ _ _ w left ran).1).owners
  exact finish scope.prepared scope.returned (preparedInterface scope.prepared
    (RuntimeNamedFrameAxes.initialized scope.entryRead).1 scope.nativeRead) scope.complete rfl valid

theorem mixed_finish {ordinary effect} (scope : RuntimeCallScope.Checked block start count inputs ordinary effect) :
    Finish scope.prepared scope.localAfter.quantum scope.returned := by
  obtain ⟨w,left,ran⟩ := scope.nativeRead
  have valid := (Raw.Ownership.valid _ (Raw.Observation.checkOps_invariants _ _ _ _ _ w left ran).1).owners
  exact finish scope.prepared scope.returned (preparedInterface scope.prepared
    (RuntimeNamedFrameAxes.initialized scope.entryRead).1 scope.nativeRead) scope.complete rfl valid

end QleisliKernel.Qirf.RuntimeNamedReturnAxes
