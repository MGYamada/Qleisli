import Qleisli.RuntimeCallPureStepLaw

/-! Compose paired literal pure intervals on their exact finite domains.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open Semantics.Finite (Dependency)
open Semantics.Raw (Event Port)
open Semantics.RawTrace (Interface)
open RuntimeCallTraceFrames (Partition WireOrder native_wires)
open Qleisli.Semantics.RawAction (events)

/-- Composition keeps the spectator coordinate fixed through both local
event lists. The bounded suffix reads only the finite parent rows on
which the first literal pair has already been shown to agree. -/
theorem PureAction.append {dependencies : List Dependency}
    {parent child pMid cMid pEnd cEnd : Interface} {spectators : List Port}
    {pFirst cFirst pRest cRest : List Event}
    (first : PureAction dependencies parent child pMid cMid spectators pFirst cFirst)
    (rest : PureAction dependencies pMid cMid pEnd cEnd spectators pRest cRest)
    (bounded : RawFiniteRows.BoundedEvents pMid.frame.length pRest pEnd.frame.length) :
    PureAction dependencies parent child pEnd cEnd spectators (pFirst++pRest) (cFirst++cRest) := by
  intro joint row within
  let midway := fun low high =>
    events dependencies cFirst (fun digit => joint digit high) low
  have replaced := bounded.congr dependencies
    (events dependencies pFirst
      (fun input => joint (project parent child.frame input) (project parent (WireOrder spectators) input)))
    (fun input => midway (project pMid cMid.frame input) (project pMid (WireOrder spectators) input))
    (first joint) row within
  have composed := replaced.trans (rest midway row within)
  simpa only [events,List.foldl_append,midway] using composed

#print axioms PureAction.append

/-- The checked outputs enumerate every local port once in the written
return order. Empty-wire ports still occur in this permutation. -/
theorem fragment_return_ports {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles) :
    frame.returned.Perm frame.pureBody.state.live ∧ Raw.stateValid frame.pureBody.state = true := by
  obtain ⟨work,left,verified⟩ := frame.pureRead
  have prepared := (Raw.Pure.verify_conditions _ _ _ work left verified).1
  obtain ⟨valid,coverage,_,_⟩ := Raw.prepare_safety _ _ _ prepared
  obtain ⟨_,_,_,_,outputsValid,_,_⟩ := Raw.prepare_conditions _ _ _ prepared
  simp only [Raw.outputValid,Bool.and_eq_true,RuntimePureInterval.fragment] at outputsValid
  have outputTokens := Raw.Ownership.unique_nodup outputs outputsValid.1.1.1.1
  obtain ⟨contained,returnedTokens⟩ := RuntimeNamedFrameAxes.selectedPorts _ _ _ frame.rawExit
  have liveTokens : (frame.pureBody.state.live.map (·.token)).Nodup :=
    (Raw.Ownership.valid _ valid).owners
  have unique (ports : List Port) (tokens : (ports.map Port.token).Nodup) : ports.Nodup :=
    List.Pairwise.of_map Port.token (fun _ _ different equal => different (congrArg Port.token equal)) tokens
  refine ⟨(List.perm_ext_iff_of_nodup (unique _ (returnedTokens.symm ▸ outputTokens))
    (unique _ liveTokens)).mpr ?_,valid⟩
  intro port
  refine ⟨fun member => contained member,?_⟩
  intro member
  have written : port.token ∈ frame.returned.map (·.token) := by
    rw [returnedTokens]
    exact coverage port member
  obtain ⟨found,returned,same⟩ := List.mem_map.mp written
  have equal := RuntimeOwnerTransitionAction.map_unique Port.token frame.pureBody.state.live liveTokens
    found (contained returned) port member same
  exact equal ▸ returned

private theorem checked_fold (dependencies : List Dependency)
    (recurse : Raw.Observation.State → List Semantics.Observation.Op → WorkM Raw.Observation.State)
    (operations : List Semantics.Raw.Op)
    {parent parentAfter : Raw.Observation.State} {child : Raw.State}
    {childAfter : Raw.Prepared} {spectators : List Port} {pPrefix cPrefix : List Event}
    {pBits cBits work left : Nat}
    (pRead : ((operations.map Semantics.Observation.Op.pure).foldlM
      (Raw.Observation.checkStep dependencies recurse) parent).run work = (.ok parentAfter,left))
    (cRead : operations.foldlM (Raw.advance (dependencies.map (·.signature))) ⟨child,cPrefix,cBits⟩ =
      .ok childAfter)
    (partition : Partition parent.quantum.reference child.reference spectators) :
    ∃ pEvents cEvents,
      childAfter.events = cPrefix++cEvents ∧
      operations.foldlM Semantics.RawTrace.advance ⟨parent.quantum.reference,pPrefix,pBits⟩ =
        some ⟨parentAfter.quantum.reference,pPrefix++pEvents,pBits⟩ ∧
      Partition parentAfter.quantum.reference childAfter.state.reference spectators ∧
      RawFiniteRows.BoundedEvents parent.quantum.frame.length pEvents parentAfter.quantum.frame.length ∧
      PureAction dependencies parent.quantum.reference child.reference
        parentAfter.quantum.reference childAfter.state.reference spectators pEvents cEvents := by
  induction operations generalizing parent child pPrefix cPrefix work with
  | nil =>
    have same := (pure_success _ _ _ _ pRead).1
    subst parentAfter
    have same : (⟨child,cPrefix,cBits⟩ : Raw.Prepared) = childAfter := Except.ok.inj cRead
    subst childAfter
    refine ⟨[],[],by simp,by simp,partition,.nil _,?_⟩
    intro joint row _
    rfl
  | cons operation operations ih =>
    simp only [List.map_cons,List.foldlM_cons] at pRead
    obtain ⟨parentMid,middle,first,rest⟩ := bind_success _ _ _ _ _ pRead
    obtain ⟨p,pStep,parentState,_,_⟩ :=
      RuntimeIntervalRawFold.checkStep_pure_raw dependencies recurse parent parentMid operation work middle first
    obtain ⟨head,pTrace,pBounds⟩ := RawFiniteRows.checked_step dependencies recurse parent parentMid operation work middle first
    subst parentMid
    have pOriginal := Raw.step_reference _ _ _ _ pStep
    have same : head = p.events := congrArg Prod.snd (Option.some.inj (pTrace.symm.trans pOriginal))
    subst head
    simp only [List.foldlM_cons] at cRead
    obtain ⟨childMid,advance,tail⟩ := except_bind_success _ _ _ cRead
    unfold Raw.advance at advance
    obtain ⟨c,cStep,next⟩ := except_bind_success _ _ _ advance
    have same := Except.ok.inj next
    subst childMid
    obtain ⟨partitionMid,headAction⟩ := pure_step_action operation partition pStep cStep
    obtain ⟨pTail,cTail,cEvents,pRest,partitionEnd,tailBounds,tailAction⟩ :=
      ih (pPrefix := pPrefix++p.events) rest tail partitionMid
    refine ⟨p.events++pTail,c.events++cTail,?_,?_,partitionEnd,pBounds.append tailBounds,
      headAction.append tailAction tailBounds⟩
    · simpa only [List.append_assoc] using cEvents
    · simpa only [List.foldlM_cons,Semantics.RawTrace.advance,pOriginal,bind,Option.bind,pure,List.append_assoc]
        using pRest

/-- Both folds come from the successful checked interval. The child trace
stops before the synthetic finish permutation of the local fragment. -/
theorem pure_interval_events {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    (spectators : List Port)
    (live : frame.interval.before.quantum.live.Perm (frame.selected++spectators)) :
    ∃ entry : Raw.State, ∃ parentEvents childEvents,
      entry.reference = ⟨frame.selected,WireOrder frame.selected⟩ ∧
      RuntimeLocalEvents.trace frame.interval.before.quantum.reference frame.operations =
        some ⟨frame.interval.after.quantum.reference,parentEvents,frame.interval.before.quantum.frame.length⟩ ∧
      RuntimeLocalEvents.trace entry.reference frame.operations =
        some ⟨frame.pureBody.state.reference,childEvents,entry.frame.length⟩ ∧
      WireOrder frame.returned ⊆ frame.pureBody.state.frame ∧
      Partition frame.interval.after.quantum.reference frame.pureBody.state.reference spectators ∧
      RawFiniteRows.BoundedEvents frame.interval.before.quantum.frame.length parentEvents
        frame.interval.after.quantum.frame.length ∧
      PureAction dependencies frame.interval.before.quantum.reference entry.reference
        frame.interval.after.quantum.reference frame.pureBody.state.reference spectators parentEvents childEvents := by
  obtain ⟨_,entry,entryRef,valid,childEvents,childFold,childTrace⟩ :=
    RuntimeIntervalRawFold.pure_interval_traces frame
  have nativeLive : frame.interval.before.quantum.live.Perm (entry.live++spectators) := by
    rw [show entry.live = frame.selected from congrArg Interface.live entryRef]
    exact live
  have partition := Partition.of_native _ _ _ frame.interval.history.1 valid nativeLive
  obtain ⟨returned,exitValid⟩ := fragment_return_ports frame
  have exitWires : WireOrder frame.returned ⊆ frame.pureBody.state.frame := by
    intro wire member
    obtain ⟨port,present,inside⟩ := List.mem_flatMap.mp member
    exact (Raw.Ownership.valid _ exitValid).covered wire
      (List.mem_flatMap.mpr ⟨port,returned.subset present,inside⟩)
  obtain ⟨work,left,read⟩ := frame.interval.intervalRead
  rw [frame.literal] at read
  cases fuel : block.fuel with
  | zero => rw [fuel] at read; cases read
  | succ depth =>
    rw [fuel] at read
    obtain ⟨checked,middle,folded,h⟩ := bind_success _ _ _ _ _ read
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    obtain ⟨parentEvents,emitted,equal,parentTrace,after,bounds,action⟩ :=
      checked_fold dependencies (Raw.Observation.checkOps dependencies depth) frame.operations
        (pPrefix := []) (pBits := frame.interval.before.quantum.frame.length) folded childFold partition
    simp only [List.nil_append] at equal parentTrace
    change childEvents = emitted at equal
    subst emitted
    rw [← same] at parentTrace after bounds action
    exact ⟨entry,parentEvents,childEvents,entryRef,parentTrace,childTrace,exitWires,after,bounds,action⟩

#print axioms pure_interval_events

/-- The full reference trace differs from the literal local event list
only by the written return permutation. -/
theorem fragment_finish {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {entry : Raw.State} {childEvents : List Event}
    (entryRef : entry.reference = ⟨frame.selected,WireOrder frame.selected⟩)
    (childTrace : RuntimeLocalEvents.trace entry.reference frame.operations =
      some ⟨frame.pureBody.state.reference,childEvents,entry.frame.length⟩) :
    let exit := frame.pureBody.state.reference
    let axes := Semantics.RawTrace.axes exit (WireOrder frame.returned)
    Semantics.RawTrace.run (RuntimePureInterval.fragment frame.selected frame.operations outputs) =
      some ⟨exit,childEvents++[.reorder exit.frame.length axes],entry.frame.length⟩ ∧
      axes.Perm (List.range exit.frame.length) := by
  intro exit axes
  obtain ⟨returned,valid⟩ := fragment_return_ports frame
  have originalWires := (returned.flatMap_right Port.wires).trans (native_wires _ valid)
  constructor
  · have returnedTokens := (RuntimeNamedFrameAxes.selectedPorts _ _ _ frame.rawExit).2
    let lookup := fun token : Nat =>
      ((exit.live.find? (fun port => port.token == token)).map Port.wires).getD []
    have writtenWires : outputs.flatMap lookup = WireOrder frame.returned := by
      calc
        _ = (frame.returned.map Port.token).flatMap lookup :=
          congrArg (fun tokens => tokens.flatMap lookup) returnedTokens.symm
        _ = _ := by
          rw [List.flatMap_map]
          apply List.flatMap_congr
          intro port member
          have live : port ∈ exit.live := returned.subset member
          have read := RuntimeNamedFrameAxes.tokenLookup exit.live port (Raw.Ownership.valid _ valid).owners live
          simp [lookup,read]
    have entryBits : entry.frame.length = (WireOrder frame.selected).length :=
      congrArg (List.length ∘ Interface.frame) entryRef
    have run := childTrace
    unfold RuntimeLocalEvents.trace at run
    rw [entryRef,entryBits] at run
    unfold Semantics.RawTrace.run RuntimePureInterval.fragment
    change (do
      let result ← frame.operations.foldlM Semantics.RawTrace.advance
        ⟨⟨frame.selected,WireOrder frame.selected⟩,[],(WireOrder frame.selected).length⟩
      pure (Semantics.RawTrace.finish (RuntimePureInterval.fragment frame.selected frame.operations outputs) result)) = _
    rw [run]
    change some (⟨exit,childEvents++[.reorder exit.frame.length (Semantics.RawTrace.axes exit (outputs.flatMap lookup))],
      (WireOrder frame.selected).length⟩ : Semantics.RawTrace.Prepared) = _
    rw [writtenWires,entryBits]
  · exact (originalWires.map exit.frame.idxOf).trans
      (List.Perm.of_eq (RuntimeNamedCallerAction.self_indices _ (Raw.Ownership.valid _ valid).frame))

#print axioms fragment_finish

/-- Evaluate the complete local fragment at the coordinate in its written
return order. Its final permutation selects the original literal row. -/
theorem fragment_prefix_action {dependencies program block arity start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block arity start count inputs outputs roles)
    {entry : Raw.State} {childEvents : List Event}
    (entryRef : entry.reference = ⟨frame.selected,WireOrder frame.selected⟩)
    (childTrace : RuntimeLocalEvents.trace entry.reference frame.operations =
      some ⟨frame.pureBody.state.reference,childEvents,entry.frame.length⟩)
    (operator : Nat → ℂ) (row : Nat) (bounded : row < 2^frame.pureBody.state.frame.length) :
    ∃ trace, Semantics.RawTrace.run (RuntimePureInterval.fragment frame.selected frame.operations outputs) = some trace ∧
      events dependencies trace.events operator
        (project frame.pureBody.state.reference (WireOrder frame.returned) row) =
        events dependencies childEvents operator row := by
  let exit := frame.pureBody.state.reference
  let axes := Semantics.RawTrace.axes exit (WireOrder frame.returned)
  obtain ⟨traceRead,permutation⟩ := fragment_finish frame entryRef childTrace
  change axes.Perm (List.range exit.frame.length) at permutation
  refine ⟨_,traceRead,?_⟩
  let packed := project exit (WireOrder frame.returned) row
  have width : axes.length = exit.frame.length := permutation.length_eq.trans List.length_range
  have packedBound : packed < 2^exit.frame.length := by
    simpa only [packed,project,← width] using RuntimeForestProduct.gather_bound row axes
  have reordered := Qleisli.RuntimeNamedThreePackedOutput.reorder_gather dependencies
    exit.frame.length axes permutation (events dependencies childEvents operator) packed packedBound
  obtain ⟨original,within,coordinate,action⟩ := reordered
  obtain ⟨projection,bijective,values⟩ :=
    Qleisli.RuntimeNamedThreePackedOutput.gather_bijective exit.frame.length axes permutation
  have same : projection ⟨original,within⟩ = projection ⟨row,bounded⟩ :=
    Fin.ext ((values ⟨original,within⟩).trans (coordinate.trans (values ⟨row,bounded⟩).symm))
  have equal : original = row := congrArg Fin.val (bijective.1 same)
  simpa only [events,List.foldl_append,List.foldl_cons,List.foldl_nil,equal] using action

#print axioms fragment_prefix_action
end Qleisli.RuntimeCallHistory
