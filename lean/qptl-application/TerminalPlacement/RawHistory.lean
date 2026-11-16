import Qleisli.RuntimeCallTraceProjection
import Qleisli.RuntimeOriginalObservation
import Qleisli.RuntimeLiteralHistory
import Qleisli.RuntimeObservingComposition
import Qleisli.RuntimeAdjacentRootAction
import QleisliKernel.Target.CanonicalOpenQasmPlacement
import QleisliKernel.Qirf.RuntimeNamedFrameAxes
import QleisliKernel.Raw.ObservationOwnership

/-! Weighted reference marginals for an original Raw erasure.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeTerminalRawMarginal
open QleisliKernel.Semantics.Finite (gather)
open Qleisli.Semantics.ObservingAction (erase)
open Qleisli.RuntimeCallTraceProjection (split_eq sum_split)
open Qleisli.RuntimeOriginalObservation (erasure_frame_geometry)

private theorem remaining_partition (frame wires : List Nat)
    (frameUnique : frame.Nodup) (wireUnique : wires.Nodup) (inside : wires ⊆ frame) :
    frame.Perm ((frame.filter fun wire => !wires.contains wire) ++ wires) := by
  have same : (frame.filter wires.contains).Perm wires := by
    apply (List.perm_ext_iff_of_nodup (frameUnique.filter _) wireUnique).mpr
    intro wire
    simp only [List.mem_filter,List.contains_iff_mem]
    exact ⟨And.right,fun member => ⟨inside member,member⟩⟩
  have partition := (List.filter_append_perm wires.contains frame).symm
  exact (partition.trans List.perm_append_comm).trans (same.append_left _)

/-- Each original finite row is selected by the unique corresponding
erasure outcome and retained row. The original coefficient is unrestricted. -/
theorem erase_gathered_row (frame wires : List Nat)
    (frameUnique : frame.Nodup) (wireUnique : wires.Nodup) (inside : wires ⊆ frame)
    (values : Nat → ℂ) (input : Nat) (inputBound : input < 2^frame.length) :
    let kept := frame.filter (fun wire => !wires.contains wire)
    let consumedAxes := wires.map frame.idxOf
    let keptAxes := kept.map frame.idxOf
    erase frame.length consumedAxes (gather input consumedAxes) values (gather input keptAxes) =
      values input := by
  intro kept consumedAxes keptAxes
  have part : frame.Perm (kept ++ wires) := remaining_partition frame wires frameUnique wireUnique inside
  have geometry := erasure_frame_geometry frame wires frameUnique wireUnique inside
  have keptEq : keptAxes = (List.range frame.length).filter (fun axis => !consumedAxes.contains axis) :=
    geometry.1
  unfold erase
  change ((List.range (2^frame.length)).map fun candidate =>
    if gather candidate consumedAxes = gather input consumedAxes ∧
      gather candidate ((List.range frame.length).filter (fun axis => !consumedAxes.contains axis)) =
        gather input keptAxes then values candidate else 0).sum = _
  rw [← keptEq]
  calc
    _ = ((List.range (2^frame.length)).map fun candidate =>
        if input = candidate then values candidate else 0).sum := by
      apply Qleisli.Exact.sum_map_congr
      intro candidate present
      have equal := split_eq part frameUnique inputBound (List.mem_range.mp present)
      have same : (gather candidate consumedAxes = gather input consumedAxes ∧
          gather candidate keptAxes = gather input keptAxes) ↔ input = candidate := by
        constructor
        · rintro ⟨consumed,retained⟩
          exact equal.mpr ⟨retained.symm,consumed.symm⟩
        · rintro rfl
          exact ⟨rfl,rfl⟩
      simp only [same]
    _ = values input := Qleisli.Exact.range_delta_sum _ _ _ inputBound

/-- Summing all actual erasure branches and retained rows is equivalent to
one fixed-frame sum. The two coefficient columns may carry distinct arbitrary
reference coordinates. The weight can use both the branch and retained row,
for example to condition on this measurement or on a later public result. -/
theorem sum_erasure (frame wires : List Nat)
    (frameUnique : frame.Nodup) (wireUnique : wires.Nodup) (inside : wires ⊆ frame)
    (left right : Nat → ℂ) (weight : Nat → Nat → ℂ) :
    let kept := frame.filter (fun wire => !wires.contains wire)
    let consumedAxes := wires.map frame.idxOf
    let keptAxes := kept.map frame.idxOf
    ((List.range (2^wires.length)).map fun outcome =>
      ((List.range (2^kept.length)).map fun row =>
        erase frame.length consumedAxes outcome left row *
          star (erase frame.length consumedAxes outcome right row) * weight outcome row).sum).sum =
    ((List.range (2^frame.length)).map fun input =>
      left input * star (right input) * weight (gather input consumedAxes) (gather input keptAxes)).sum := by
  intro kept consumedAxes keptAxes
  let term := fun (row outcome : Nat) =>
    erase frame.length consumedAxes outcome left row *
      star (erase frame.length consumedAxes outcome right row) * weight outcome row
  have part : frame.Perm (kept ++ wires) := remaining_partition frame wires frameUnique wireUnique inside
  change ((List.range (2^wires.length)).map fun outcome =>
    ((List.range (2^kept.length)).map fun row => term row outcome).sum).sum = _
  rw [← sum_split part frameUnique term]
  apply Qleisli.Exact.sum_map_congr
  intro input present
  have bound := List.mem_range.mp present
  change erase frame.length consumedAxes (gather input consumedAxes) left (gather input keptAxes) *
    star (erase frame.length consumedAxes (gather input consumedAxes) right (gather input keptAxes)) *
      weight (gather input consumedAxes) (gather input keptAxes) = _
  rw [erase_gathered_row frame wires frameUnique wireUnique inside left input bound,
    erase_gathered_row frame wires frameUnique wireUnique inside right input bound]

#print axioms erase_gathered_row
#print axioms sum_erasure
end Qleisli.RuntimeTerminalRawMarginal

/-! The exact independent history sum for a terminal sequence of erasures.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeTerminalRawMarginal
open QleisliKernel.Semantics.Finite (Dependency gather)
open QleisliKernel.Semantics.Observation (Event)
open Qleisli.Semantics.ObservingAction (History run erase)
open Qleisli.RuntimeLiteralHistory (run_single)
open Qleisli.RuntimeObservingComposition (runHistories runHistories_append runHistories_singleton)
open Qleisli.RuntimeOriginalObservation (erasure_step_histories)

private def remaining (frame wires : List Nat) : List Nat :=
  frame.filter (fun wire => !wires.contains wire)

private def written (output : Option Nat) (outcome : Nat) : List (Nat × Bool) :=
  match output with
  | none => []
  | some id => [(id,outcome == 1)]

/-- An original ordered erasure sequence with no quantum row left at its end.
Structural ownership transitions contribute no event. Discard of an empty
owner does contribute its single zero-width outcome. -/
inductive TerminalErasure : List Nat → List Event → Type where
  | done : TerminalErasure [] []
  | consume {frame : List Nat} {events : List Event}
      (frameUnique : frame.Nodup) (wires : List Nat) (wireUnique : wires.Nodup)
      (inside : wires ⊆ frame) (output : Option Nat)
      (rest : TerminalErasure (remaining frame wires) events) :
      TerminalErasure frame (.erase frame.length (wires.map frame.idxOf) output :: events)

/-- Classical assignments incurred by the original terminal events, in their
execution order, on a given basis row of the current frame. -/
def TerminalErasure.basisWrites : {frame : List Nat} → {events : List Event} →
    TerminalErasure frame events → Nat → List (Nat × Bool)
  | _, _, .done, _ => []
  | frame, _, .consume _ wires _ _ output rest, row =>
    written output (gather row (wires.map frame.idxOf)) ++
      rest.basisWrites (gather row ((remaining frame wires).map frame.idxOf))

private theorem sum_mapped_results {α β : Type} (items : List α) (evaluate : α → Option (List β))
    (score : β → ℂ) (expected : α → ℂ)
    (each : ∀ item ∈ items, ∃ choices, evaluate item = some choices ∧ (choices.map score).sum = expected item) :
    ∃ groups : List (List β), items.mapM evaluate = some groups ∧
      (groups.flatten.map score).sum = (items.map expected).sum := by
  induction items with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons first rest ih =>
    obtain ⟨head,headRun,headSum⟩ := each first List.mem_cons_self
    obtain ⟨tail,tailRun,tailSum⟩ := ih (fun item member => each item (List.mem_cons_of_mem _ member))
    refine ⟨head :: tail,?_,?_⟩
    · simp [List.mapM_cons,headRun,tailRun,bind,Option.bind]
    · simp only [List.flatten_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,headSum,tailSum]

private noncomputable def historyScore (columnLeft columnRight : Nat)
    (weight : List (Nat × Bool) → ℂ) (history : History) : ℂ :=
  history.operator 0 columnLeft * star (history.operator 0 columnRight) * weight history.values

/-- Exact coefficient transport for the actual sequential Raw run. The weight
may read any subset of the classical outputs; every complete hidden history
contributes with its original multiplicity and without normalization. -/
theorem TerminalErasure.run_weighted {frame : List Nat} {events : List Event}
    (trace : TerminalErasure frame events) (dependencies : List Dependency) (fuel : Nat)
    (history : History) (columnLeft columnRight : Nat) (weight : List (Nat × Bool) → ℂ) :
    ∃ histories, run dependencies (fuel+1) events history = some histories ∧
      (histories.map (historyScore columnLeft columnRight weight)).sum =
      ((List.range (2^frame.length)).map fun row =>
        history.operator row columnLeft * star (history.operator row columnRight) *
          weight (history.values ++ trace.basisWrites row)).sum := by
  induction trace generalizing history with
  | done =>
    refine ⟨[history],rfl,?_⟩
    simp [historyScore,TerminalErasure.basisWrites]
  | @consume frame events frameUnique wires wireUnique inside output rest ih =>
    let axes := wires.map frame.idxOf
    let kept := remaining frame wires
    let event := Event.erase frame.length axes output
    let expected := fun outcome =>
      ((List.range (2^kept.length)).map fun row =>
        erase frame.length axes outcome (fun idx => history.operator idx columnLeft) row *
          star (erase frame.length axes outcome (fun idx => history.operator idx columnRight) row) *
          weight ((history.values ++ written output outcome) ++ rest.basisWrites row)).sum
    obtain ⟨branch,branched,branchFacts⟩ :=
      erasure_step_histories dependencies frame.length axes output (run dependencies fuel) history
    have writes (outcome : Nat) : (branch outcome).values = history.values ++ written output outcome := by
      cases output <;> simpa only [written,List.append_nil] using (branchFacts outcome).1
    have one (outcome : Nat) (_ : outcome ∈ List.range (2^wires.length)) :
        ∃ histories, run dependencies (fuel+1) events (branch outcome) = some histories ∧
          (histories.map (historyScore columnLeft columnRight weight)).sum = expected outcome := by
      obtain ⟨histories,executed,equal⟩ := ih (branch outcome)
      exact ⟨histories,executed,by simpa only [expected,writes,(branchFacts outcome).2.2] using equal⟩
    obtain ⟨groups,groupRun,groupSum⟩ := sum_mapped_results (List.range (2^wires.length))
      (fun outcome => run dependencies (fuel+1) events (branch outcome))
      (historyScore columnLeft columnRight weight) expected one
    have head : run dependencies (fuel+1) [event] history =
        some ((List.range (2^wires.length)).map branch) := by
      rw [run_single]
      simpa only [event,axes,List.length_map] using branched
    refine ⟨groups.flatten,?_,?_⟩
    · change run dependencies (fuel+1) ([event] ++ events) history = _
      rw [← runHistories_singleton,runHistories_append,runHistories_singleton,head]
      simp [runHistories,List.mapM_map,Function.comp_def,groupRun,bind,Option.bind]
    · rw [groupSum]
      simpa only [expected,TerminalErasure.basisWrites,List.append_assoc] using
        sum_erasure frame wires frameUnique wireUnique inside
          (fun row => history.operator row columnLeft) (fun row => history.operator row columnRight)
          (fun outcome row => weight ((history.values ++ written output outcome) ++ rest.basisWrites row))

#print axioms TerminalErasure.run_weighted

open QleisliKernel.Semantics.Finite (bit)
open Qleisli.RuntimeOriginalObservation (gather_retained)

/-- List the only classical writes of the terminal trace in execution order.
A selected measurement has one original logical wire. -/
def TerminalErasure.measurementWires : {frame : List Nat} → {events : List Event} →
    TerminalErasure frame events → Option (List (Nat × Nat))
  | _, _, .done => some []
  | _, _, .consume _ wires _ _ output rest =>
    match output,wires with
    | none,_ => rest.measurementWires
    | some id,[wire] => rest.measurementWires.map ((id,wire) :: ·)
    | _,_ => none

private theorem retained_write_bit (frame kept : List Nat) (row wire : Nat) (inside : wire ∈ kept) :
    bit (gather row (kept.map frame.idxOf)) (kept.idxOf wire) = bit row (frame.idxOf wire) := by
  have same := gather_retained frame kept [wire] (kept.map frame.idxOf) rfl
    (fun _ member => List.mem_singleton.mp member ▸ inside) row
  simpa [gather] using same

/-- The literal write order can be evaluated in the initial frame. Erased
wires never shift the selected bit: each surviving coordinate is compressed
by its own gather and read at precisely the corresponding new axis. -/
theorem TerminalErasure.basisWrites_original_frame {frame : List Nat} {events : List Event}
    (erasure : TerminalErasure frame events) {measurements : List (Nat × Nat)}
    (found : erasure.measurementWires = some measurements) :
    (∀ pair ∈ measurements, pair.2 ∈ frame) ∧
    ∀ row, erasure.basisWrites row =
      measurements.map (fun pair => (pair.1,bit row (frame.idxOf pair.2) == 1)) := by
  induction erasure generalizing measurements with
  | done =>
    have empty : [] = measurements := Option.some.inj found
    subst measurements
    exact ⟨by simp,fun _ => rfl⟩
  | @consume frame events unique wires wireUnique inside output rest ih =>
    let kept := remaining frame wires
    have liftTail {pairs : List (Nat × Nat)} (tail : rest.measurementWires = some pairs) :
        (∀ pair ∈ pairs, pair.2 ∈ frame) ∧
        ∀ row, rest.basisWrites (gather row (kept.map frame.idxOf)) =
          pairs.map (fun pair => (pair.1,bit row (frame.idxOf pair.2) == 1)) := by
      obtain ⟨members,evaluated⟩ := ih tail
      refine ⟨fun pair member => (List.mem_filter.mp (members pair member)).1,?_⟩
      intro row
      rw [evaluated]
      apply List.map_congr_left
      intro pair member
      rw [retained_write_bit frame kept row pair.2 (members pair member)]
    cases output with
    | none =>
      change rest.measurementWires = some measurements at found
      exact liftTail found
    | some id =>
      cases wires with
      | nil => cases found
      | cons wire others =>
        cases others with
        | cons _ _ => cases found
        | nil =>
          change rest.measurementWires.map ((id,wire) :: ·) = some measurements at found
          rw [Option.map_eq_some_iff] at found
          obtain ⟨tail,tailFound,rfl⟩ := found
          obtain ⟨members,evaluated⟩ := liftTail tailFound
          refine ⟨?_,?_⟩
          · intro pair member
            rcases List.mem_cons.mp member with rfl | later
            · exact inside (by simp)
            · exact members pair later
          · intro row
            simp only [TerminalErasure.basisWrites,written,List.map_cons,List.map_nil,List.singleton_append]
            rw [evaluated]
            simp [gather]

#print axioms TerminalErasure.basisWrites_original_frame
end Qleisli.RuntimeTerminalRawMarginal

/-! The literal reader erases each terminal owner in its current compressed
frame. The placement reader retains the entry frame for physical lookups.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeTerminalRawMarginal
open QleisliKernel
open QleisliKernel.Semantics
open QleisliKernel.Target.CanonicalOpenQasmPlacement (Readout ReadoutTrace)
open QleisliKernel.Target.CanonicalOpenQasmWorkspace (placedWires)
open QleisliKernel.Raw.ObservationAgreement (read_succ readStep layer)

private theorem take_reframe (state : RawTrace.Interface) (frame : List Nat) (token : Nat) :
    RawTrace.take {state with frame := frame} token =
      (RawTrace.take state token).map (fun (port,next) => (port,{next with frame := frame})) := by
  unfold RawTrace.take
  cases state.live.find? (fun port => port.token == token) <;> rfl

private theorem take_live {state next : RawTrace.Interface} {token port}
    (take : RawTrace.take state token = some (port,next)) :
    next.live = state.live.filter (fun port => port.token != token) := by
  unfold RawTrace.take at take
  obtain ⟨_,_,returned⟩ := Option.bind_eq_some_iff.mp take
  exact (congrArg (fun pair : Semantics.Raw.Port × RawTrace.Interface => pair.2.live)
    (Option.some.inj returned)).symm

private theorem reframe_structural {state next : RawTrace.Interface} {operation : Semantics.Raw.Op}
    (read : RawTrace.step state operation = some (next,[])) (frame : List Nat) :
    RawTrace.step {state with frame := frame} operation = some ({next with frame := frame},[]) := by
  cases operation <;> simp only [RawTrace.step] at read
  case split input left right bits =>
    obtain ⟨⟨port,middle⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp read
    obtain rfl := congrArg Prod.fst (Option.some.inj returned)
    simp [RawTrace.step,take_reframe,taken,RawTrace.insert,bind,Option.bind,pure]
  case join left right output =>
    obtain ⟨⟨l,middle⟩,leftRead,rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨r,last⟩,rightRead,returned⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := congrArg Prod.fst (Option.some.inj returned)
    simp [RawTrace.step,take_reframe,leftRead,rightRead,RawTrace.insert,bind,Option.bind,pure]
  case packUnit output =>
    obtain rfl := congrArg Prod.fst (Option.some.inj read)
    rfl
  case unpackUnit input =>
    obtain ⟨⟨port,middle⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp read
    split at returned
    · rename_i empty
      obtain rfl := congrArg Prod.fst (Option.some.inj returned)
      have emptyPort : port.bits = 0 ∧ port.wires = [] := by simpa using empty
      simp [RawTrace.step,take_reframe,taken,emptyPort.1,emptyPort.2,bind,Option.bind,pure]
    · cases returned
  all_goals repeat' first
    | cases (congrArg Prod.snd (Option.some.inj read))
    | obtain ⟨⟨_,_⟩,_,read⟩ := Option.bind_eq_some_iff.mp read

private theorem erase_read {before after : Ownership.State} {input port}
    (valid : Ownership.Valid before) (erase : Ownership.Erase before input port after)
    (output : Option Nat) (fuel : Nat) :
    readStep (Observation.readOps fuel) before.interface
      (match output with | some id => .measure input id | none => .discard input) =
      some (after.interface,[.erase before.frame.length (port.wires.map before.frame.idxOf) output]) := by
  have lookup := Qirf.RuntimeNamedFrameAxes.tokenLookup before.live port valid.owners erase.present
  rw [erase.owner] at lookup
  cases output <;>
    simp [readStep,RawTrace.take,Ownership.State.interface,Observation.remaining,RawTrace.axes,
      lookup,erase.result,bind,Option.bind,pure]

private theorem erase_live {before after : Ownership.State}
    {state next : RawTrace.Interface} {input rawPort ownerPort}
    (same : before.live = state.live)
    (taken : RawTrace.take state input = some (rawPort,next))
    (erased : Ownership.Erase before input ownerPort after) :
    after.live = next.live := by
  rw [erased.result,take_live taken]
  simp [same]

private theorem erase_port_geometry {before after : Ownership.State} {input port}
    (valid : Ownership.Valid before) (erase : Ownership.Erase before input port after) :
    port.wires.Nodup ∧ port.wires ⊆ before.frame := by
  exact ⟨(List.nodup_flatMap.mp valid.exclusive).1 port erase.present,
    fun wire member => valid.covered wire (List.mem_flatMap.mpr ⟨port,erase.present,member⟩)⟩

private theorem read_cons {state middle final : RawTrace.Interface}
    {op : Observation.Op} {rest : List Observation.Op} {events tail : List Observation.Event}
    {fuel : Nat}
    (head : readStep (Observation.readOps fuel) state op = some (middle,events))
    (readTail : Observation.readOps (fuel+1) middle rest = some (final,tail)) :
    Observation.readOps (fuel+1) state (op :: rest) = some (final,events ++ tail) := by
  change Observation.readOps (fuel+1) state ([op] ++ rest) = _
  rw [Qleisli.RuntimeAdjacentSlices.readOps_append]
  have one : Observation.readOps (fuel+1) state [op] = some (middle,events) := by
    simp [read_succ,layer,head,bind,Option.bind,pure]
  simp [one,readTail,bind,Option.bind,pure]

private theorem erase_same_port {before after : Ownership.State}
    {state next : RawTrace.Interface} {input rawPort ownerPort}
    (same : before.live = state.live) (valid : Ownership.Valid before)
    (taken : RawTrace.take state input = some (rawPort,next))
    (erased : Ownership.Erase before input ownerPort after) : ownerPort = rawPort := by
  have lookup := Qirf.RuntimeNamedFrameAxes.tokenLookup before.live ownerPort valid.owners erased.present
  rw [erased.owner] at lookup
  unfold RawTrace.take at taken
  rw [← same,lookup] at taken
  exact congrArg Prod.fst (Option.some.inj taken)

private theorem TerminalErasure.measurementWires_cast {frame other : List Nat} {events : List Observation.Event}
    (equal : frame = other) (trace : TerminalErasure frame events) :
    ((equal ▸ trace) : TerminalErasure other events).measurementWires = trace.measurementWires := by
  cases equal
  rfl

private theorem TerminalErasure.measurementWires_consume_single {frame : List Nat}
    {events : List Observation.Event} {wires : List Nat} {wire output : Nat}
    (single : wires = [wire]) (frameUnique : frame.Nodup) (wireUnique : wires.Nodup)
    (inside : wires ⊆ frame)
    (tail : TerminalErasure (frame.filter (fun w => !wires.contains w)) events) :
    (TerminalErasure.consume frameUnique wires wireUnique inside (some output) tail).measurementWires =
      tail.measurementWires.map ((output,wire) :: ·) := by
  subst wires
  rfl

/-- Lockstep replay records the same original measured identifier, logical
wire and selected physical wire for each chronologically ordered write. -/
theorem readoutTrace_erasure_measured {frame locations before after operations}
    (readout : ReadoutTrace frame locations before operations after)
    {entry exit : Ownership.State} (run : Ownership.Run entry operations exit)
    (sameLive : entry.live = before.1.live) (done : after.1.live = [])
    (fuel : Nat) :
    ∃ events, ∃ erasure : TerminalErasure entry.frame events,
      Observation.readOps (fuel+1) entry.interface operations = some (exit.interface,events) ∧
      exit.live = [] ∧ exit.frame = [] ∧
      ∃ measurements : List (Nat × Nat × Nat),
        erasure.measurementWires = some (measurements.map (fun pair => (pair.1,pair.2.1))) ∧
        after.2 = (measurements.map (fun pair => (pair.1,pair.2.2))).reverse ++ before.2 ∧
        (∀ pair ∈ measurements, placedWires frame locations [pair.2.1] = some [pair.2.2]) := by
  induction readout generalizing entry exit with
  | empty state =>
    cases run with
    | nil owner valid =>
      have noLive := sameLive.trans done
      have noFrame := List.length_eq_zero_iff.mp (by
        simpa only [noLive,List.flatMap_nil,List.length_nil] using valid.count.symm)
      refine ⟨[],noFrame.symm ▸ TerminalErasure.done,rfl,noLive,noFrame,[],?_,rfl,by simp⟩
      rw [TerminalErasure.measurementWires_cast]
      rfl
  | cons step _ ih =>
    cases run with
    | cons entry operation middle rest exit valid head tail =>
      cases step with
      | @measure state next measured input output wire location rawPort taken single placed fresh =>
        cases head with
        | measure _ _ _ ownerPort _ erased bit =>
          obtain ⟨events,history,read,emptyLive,emptyFrame,measurements,writes,order,coords⟩ :=
            ih tail (erase_live sameLive taken erased) done
          have geometry := erase_port_geometry valid erased
          have currentFrame : middle.frame =
              entry.frame.filter (fun wire => !ownerPort.wires.contains wire) := by
            rw [erased.result]
          have actualPort := erase_same_port sameLive valid taken erased
          have ownerWire : ownerPort.wires = [wire] := actualPort.symm ▸ single
          let nextHistory : TerminalErasure
              (entry.frame.filter (fun wire => !ownerPort.wires.contains wire)) events :=
            currentFrame ▸ history
          let consumed := TerminalErasure.consume valid.frame ownerPort.wires geometry.1 geometry.2
            (some output) nextHistory
          refine ⟨_,consumed,read_cons (erase_read valid erased (some output) fuel) read,
            emptyLive,emptyFrame,(output,wire,location) :: measurements,?_,?_,?_⟩
          · have nextWrites : nextHistory.measurementWires = _ :=
              (TerminalErasure.measurementWires_cast currentFrame history).trans writes
            unfold consumed
            rw [TerminalErasure.measurementWires_consume_single ownerWire]
            simp [nextWrites]
          · rw [order]
            simp [List.reverse_cons,List.append_assoc]
          · intro pair member
            rcases List.mem_cons.mp member with rfl | later
            · exact placed
            · exact coords pair later
      | @discard state next measured input rawPort taken =>
        cases head with
        | discard _ _ ownerPort _ erased =>
          obtain ⟨events,history,read,emptyLive,emptyFrame,measurements,writes,order,coords⟩ :=
            ih tail (erase_live sameLive taken erased) done
          have geometry := erase_port_geometry valid erased
          have currentFrame : middle.frame =
              entry.frame.filter (fun wire => !ownerPort.wires.contains wire) := by
            rw [erased.result]
          let nextHistory : TerminalErasure
              (entry.frame.filter (fun wire => !ownerPort.wires.contains wire)) events :=
            currentFrame ▸ history
          let consumed := TerminalErasure.consume valid.frame ownerPort.wires geometry.1 geometry.2 none nextHistory
          refine ⟨_,consumed,read_cons (erase_read valid erased none fuel) read,
            emptyLive,emptyFrame,measurements,?_,order,coords⟩
          exact (TerminalErasure.measurementWires_cast currentFrame history).trans writes
      | @structural state next measured op transition =>
        cases head with
        | pure _ _ _ pureStep =>
          have compressed := reframe_structural transition entry.frame
          have same : {state with frame := entry.frame} = entry.interface := by
            cases state
            simp [Ownership.State.interface] at sameLive ⊢
            exact sameLive.symm
          rw [same] at compressed
          obtain ⟨_,original⟩ := pureStep.action
          have matched := congrArg Prod.fst (Option.some.inj (original.symm.trans compressed))
          change middle.interface = { next with frame := entry.frame } at matched
          have nextLive : middle.live = next.live := congrArg RawTrace.Interface.live matched
          have nextFrame : middle.frame = entry.frame := congrArg RawTrace.Interface.frame matched
          obtain ⟨events,history,read,emptyLive,emptyFrame,measurements,writes,order,coords⟩ :=
            ih tail nextLive done
          have one : readStep (Observation.readOps fuel) entry.interface (.pure op) =
              some (middle.interface,[]) := by
            simp [readStep,compressed,← matched,bind,Option.bind,pure]
          refine ⟨events,nextFrame ▸ history,by simpa only [List.nil_append] using read_cons one read,
            emptyLive,emptyFrame,measurements,?_,order,coords⟩
          exact (TerminalErasure.measurementWires_cast nextFrame history).trans writes

#print axioms readoutTrace_erasure_measured

open QleisliKernel.Semantics.Finite (bit)

private theorem measured_lookup {values : List (Nat × Bool)} {id : Nat} {result : Bool}
    (unique : (values.map Prod.fst).Nodup) (present : (id,result) ∈ values) :
    Semantics.RawInstrument.value values id = some result := by
  induction values with
  | nil => cases present
  | cons first later ih =>
    obtain ⟨firstFresh,tailUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp present with rfl | inTail
    · simp [Semantics.RawInstrument.value]
    · have different : first.1 ≠ id := by
        intro same
        apply firstFresh
        rw [same]
        exact List.mem_map_of_mem inTail
      simpa [Semantics.RawInstrument.value,different] using ih tailUnique inTail

private theorem mapped_word (value : Nat → Option Bool) (bits : Nat → Bool)
    (ids axes : List Nat) (sameLength : ids.length = axes.length)
    (pointwise : ∀ index id axis : Nat, ids[index]? = some id → axes[index]? = some axis →
      value id = some (bits axis)) :
    ids.mapM value = some (axes.map bits) := by
  induction ids generalizing axes with
  | nil => cases axes <;> simp_all
  | cons id ids ih =>
    cases axes with
    | nil => cases sameLength
    | cons axis axes =>
      have first := pointwise 0 id axis rfl rfl
      have rest := ih axes (by simpa using sameLength)
        (fun index nextId nextAxis source target => pointwise (index+1) nextId nextAxis source target)
      simp [List.mapM_cons,first,rest,bind,Option.bind,pure]

/-- Actual source SSA lookup sees the same entire output word as the decoded
physical measurement list in the ordered entry frame. -/
theorem readout_original_word {bytes capacity}
    {target : Target.CanonicalOpenQasmResources.Checked bytes capacity}
    {program : Observation.Program} {state : Target.CanonicalOpenQasmPlacement.State}
    (readout : Readout target program state) (distinct : state.locations.Nodup)
    {entry exit : Ownership.State}
    (run : Ownership.Run entry (program.operations.drop state.rawIndex) exit)
    (same : entry.interface = state.raw) (fuel : Nat) :
    ∃ events, ∃ erasure : TerminalErasure state.raw.frame events,
      Observation.readOps (fuel+1) state.raw (program.operations.drop state.rawIndex) =
        some (exit.interface,events) ∧ exit.frame = [] ∧
      ∀ row : Nat, program.classicalOutputs.mapM (Semantics.RawInstrument.value (erasure.basisWrites row)) =
        some (target.circuit.measurements.map (fun location => bit row (state.locations.idxOf location) == 1)) := by
  obtain ⟨_,_,finished,measured,trace,done,_,idUnique,_,lengthEq,physicalAt⟩ := readout.original_trace
  obtain ⟨events,history,executed,_,endFrame,measurements,converted,coordsMeasured,coords⟩ :=
    readoutTrace_erasure_measured trace run (congrArg RawTrace.Interface.live same) done fuel
  have sameFrame : entry.frame = state.raw.frame := congrArg RawTrace.Interface.frame same
  let finalTrace : TerminalErasure state.raw.frame events := sameFrame ▸ history
  refine ⟨events,finalTrace,by rw [← same]; exact executed,endFrame,?_⟩
  have converted' : finalTrace.measurementWires = _ :=
    (TerminalErasure.measurementWires_cast sameFrame history).trans converted
  obtain ⟨liveWire,originalWrites⟩ := finalTrace.basisWrites_original_frame converted'
  have originalIds : (measurements.map fun pair => pair.1).Nodup := by
    change measured = _ at coordsMeasured
    simp only [List.append_nil] at coordsMeasured
    rw [coordsMeasured,List.map_reverse,List.map_map] at idUnique
    exact List.nodup_reverse.mp idUnique
  intro row
  refine mapped_word _ _ _ _ lengthEq.symm ?_
  intro index id location source emitted
  obtain ⟨actual,physical,member⟩ := physicalAt index id source
  have equal : actual = location := Option.some.inj (physical.symm.trans emitted)
  subst actual
  have chronological : (id,location) ∈ measurements.map (fun pair => (pair.1,pair.2.2)) := by
    change measured = _ at coordsMeasured
    rw [coordsMeasured,List.append_nil] at member
    exact List.mem_reverse.mp member
  obtain ⟨pair,actualPair,equal⟩ := List.mem_map.mp chronological
  rcases pair with ⟨writtenId,wire,actualLocation⟩
  change (writtenId,actualLocation) = (id,location) at equal
  obtain ⟨sameId,sameLocation⟩ := Prod.mk.inj equal
  subst writtenId
  subst actualLocation
  have kept : wire ∈ state.raw.frame := liveWire (id,wire) (List.mem_map_of_mem actualPair)
  have placed := coords (id,wire,location) actualPair
  have stored : state.locations[state.raw.frame.idxOf wire]? = some location := by
    simp [placedWires,List.mapM_cons,kept,bind,Option.bind,pure] at placed
    cases lookup : state.locations[state.raw.frame.idxOf wire]? with
    | none => simp [lookup] at placed
    | some recorded => simpa [lookup] using placed
  have lookback := Qirf.RuntimeNamedFrameAxes.wireLookup state.locations (List.mem_of_getElem? stored)
  have axis : state.locations.idxOf location = state.raw.frame.idxOf wire :=
    (List.getElem?_inj (List.idxOf_lt_length_of_mem (List.mem_of_getElem? stored)) distinct).mp
      (lookback.trans stored.symm)
  rw [axis]
  apply measured_lookup
  · simpa only [originalWrites,List.map_map,Function.comp_def] using originalIds
  · rw [originalWrites,List.map_map]
    exact List.mem_map_of_mem actualPair

#print axioms readout_original_word
end Qleisli.RuntimeTerminalRawMarginal

/-! Recover the actual original ownership state at a pure literal reader cut.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeTerminalRawMarginal
open QleisliKernel
open QleisliKernel.Semantics
open QleisliKernel.Raw.ObservationAgreement (read_succ readStep layer)

private theorem one_step_read (fuel : Nat) (state : RawTrace.Interface) (op : Observation.Op) :
    Observation.readOps (fuel+1) state [op] = readStep (Observation.readOps fuel) state op := by
  rw [read_succ]
  unfold layer
  cases read : readStep (Observation.readOps fuel) state op with
  | none => simp [read,bind,Option.bind,pure]
  | some result =>
    obtain ⟨next,events⟩ := result
    simp [read,bind,Option.bind,pure]

private theorem pure_step_of_read {recurse : QleisliKernel.Raw.ObservationAgreement.Reader} {before after : RawTrace.Interface}
    {op : Observation.Op} {events : List Observation.Event}
    (read : readStep recurse before op = some (after,events))
    (onlyPure : ∀ event ∈ events, ∃ raw, event = .pure raw) : ∃ raw, op = .pure raw := by
  cases op <;> simp only [readStep] at read
  case pure operation => exact ⟨operation,rfl⟩
  all_goals repeat' first
    | (have shape := congrArg Prod.snd (Option.some.inj read)
       change _ = events at shape
       rw [← shape] at onlyPure
       obtain ⟨_,impossible⟩ := onlyPure _ List.mem_cons_self
       cases impossible)
    | obtain ⟨⟨_,_⟩,_,read⟩ := Option.bind_eq_some_iff.mp read

/-- When the actual original reader at an ownership cut returns only pure
events, its exact final ordered interface is the one in the original
ownership derivation. Even branch/reset constructors with empty inner
events cannot be mistaken for pure here. -/
theorem ownership_pure_read_interface {entry exit : Ownership.State} {operations : List Observation.Op}
    (owned : Ownership.Run entry operations exit) (fuel : Nat)
    {result : RawTrace.Interface} {events : List Observation.Event}
    (read : Observation.readOps (fuel+1) entry.interface operations = some (result,events))
    (onlyPure : ∀ event ∈ events, ∃ raw, event = .pure raw) : result = exit.interface := by
  induction operations generalizing entry exit result events with
  | nil =>
    cases owned
    exact (congrArg Prod.fst (Option.some.inj read)).symm
  | cons op rest ih =>
    cases owned with
    | cons entry operation next ops exit valid head tail =>
      change Observation.readOps (fuel+1) entry.interface ([op] ++ rest) = some (result,events) at read
      rw [Qleisli.RuntimeAdjacentSlices.readOps_append,one_step_read] at read
      obtain ⟨⟨middle,earlier⟩,original,continued⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨⟨after,later⟩,readTail,done⟩ := Option.bind_eq_some_iff.mp continued
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj done)
      have earlierPure (event : Observation.Event) (member : event ∈ earlier) : ∃ raw, event = .pure raw :=
        onlyPure event (List.mem_append_left _ member)
      obtain ⟨raw,rfl⟩ := pure_step_of_read original earlierPure
      cases head with
      | pure _ _ _ ownerStep =>
        obtain ⟨_,ownRead⟩ := ownerStep.action
        simp only [readStep,ownRead,bind,Option.bind,pure] at original
        have same : next.interface = middle := congrArg Prod.fst (Option.some.inj original)
        rw [← same] at readTail
        exact ih tail readTail (fun event member => onlyPure event (List.mem_append_right _ member))

/-- Split the exact original ownership derivation at the successful literal
pure prefix. The suffix begins at the precise terminal Raw interface. -/
theorem ownership_after_closed_pure_prefix {program : Observation.Program} {cursor : Nat}
    {state : RawTrace.Interface} {events : List Semantics.Raw.Event}
    (owned : Ownership.OwnershipSafe program) (closed : program.inputs = [])
    (read : Observation.readOps 65 (RawTrace.initial program.inputs) (program.operations.take cursor) =
      some (state,events.map Observation.Event.pure)) :
    ∃ entry exit, Ownership.Run entry (program.operations.drop cursor) exit ∧ entry.interface = state := by
  obtain ⟨initial,exit,params,whole,_⟩ := owned
  rw [← List.take_append_drop cursor program.operations] at whole
  obtain ⟨entry,prefixOwn,_,suffixOwn⟩ := Ownership.Run.split _ _ whole
  refine ⟨entry,exit,suffixOwn,?_⟩
  rw [closed] at params read
  have emptyInitial : initial = {} := by cases params; rfl
  have startup : RawTrace.initial ([] : List Semantics.Raw.Port) = initial.interface := by
    rw [emptyInitial]
    rfl
  rw [startup] at read
  symm
  apply ownership_pure_read_interface prefixOwn 64 read
  intro event member
  obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
  exact ⟨raw,rfl⟩

#print axioms ownership_pure_read_interface
#print axioms ownership_after_closed_pure_prefix
end Qleisli.RuntimeTerminalRawMarginal
