import QleisliKernel.Raw.BranchFunction
import QleisliKernel.SourceTypes.NaturalAffine

/-! Resources of the emitted finite workspace interval. The model counts
literal Raw events, including the hidden width of certified clean events.
Referenced circuits contribute their independently checked expansion bounds.
Physical target routing and gate costs have separate models.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.WorkspaceResources
open QleisliKernel Finite
private abbrev RawEvent := Semantics.Raw.Event

structure Counts where
  peakWires : Nat := 0
  preparedWires : Nat := 0
  releasedCleanWires : Nat := 0
  predicatePasses : Nat := 0
  circuitSteps : Nat := 0
  framePermutations : Nat := 0
  deriving BEq, DecidableEq, Repr

def Counts.then_ (left right : Counts) : Counts :=
  ⟨max left.peakWires right.peakWires,left.preparedWires + right.preparedWires,
    left.releasedCleanWires + right.releasedCleanWires,left.predicatePasses + right.predicatePasses,
    left.circuitSteps + right.circuitSteps,left.framePermutations + right.framePermutations⟩

def eventCounts : RawEvent → Counts
  | .computed bits _ _ scratch _ steps _ => ⟨bits + scratch,scratch,scratch,2,steps.length,0⟩
  | .protectedComputed bits _ _ scratch _ uses => ⟨bits + scratch,scratch,scratch,2,uses.length,0⟩
  | .circuit bits steps => { peakWires := bits, circuitSteps := steps.length }
  | .reorder bits axes => { peakWires := bits, framePermutations := if axes == List.range bits then 0 else 1 }
  | .init0 bits => { peakWires := bits+1, preparedWires := 1 }
  | .liftBasis before after _ _ _ => { peakWires := max before after, preparedWires := after-before }

def readCounts (entryWidth : Nat) (events : List RawEvent) : Counts :=
  events.foldl (fun counts event => counts.then_ (eventCounts event)) { peakWires := entryWidth }

theorem peak_bounds_event (events : List RawEvent) (initial : Counts) (event : RawEvent) (member : event ∈ events) :
    (eventCounts event).peakWires ≤
      (events.foldl (fun counts item => counts.then_ (eventCounts item)) initial).peakWires := by
  have accumulate (remaining : List RawEvent) (counts : Counts) :
      counts.peakWires ≤ (remaining.foldl (fun acc item => acc.then_ (eventCounts item)) counts).peakWires := by
    induction remaining generalizing counts with
    | nil => exact Nat.le_refl _
    | cons item more recur =>
      exact Nat.le_trans (Nat.le_max_left counts.peakWires (eventCounts item).peakWires)
        (recur (counts.then_ (eventCounts item)))
  induction events generalizing initial with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with rfl | rest
    · exact Nat.le_trans (Nat.le_max_right initial.peakWires (eventCounts event).peakWires)
        (accumulate tail (initial.then_ (eventCounts event)))
    · exact ih _ rest

@[simp] theorem clean_counts (entryWidth : Nat) (axes : List Nat) (sourceBits : Nat)
    (table : List Nat) (body logical : List Semantics.Finite.Step) :
    readCounts entryWidth [.computed entryWidth axes sourceBits 1 table body logical] =
      ⟨entryWidth+1,1,1,2,body.length,0⟩ := by
  simp [readCounts,Counts.then_,eventCounts,Nat.max_eq_right (Nat.le_succ _)]

@[simp] theorem dirty_counts (entryWidth : Nat) (body : List Semantics.Finite.Step) :
    readCounts entryWidth [.circuit entryWidth body] = ⟨entryWidth,0,0,0,body.length,0⟩ := by
  simp [readCounts,Counts.then_,eventCounts]

def physicalSteps : RawEvent → List Semantics.Finite.Step
  | .computed _ _ _ _ _ body _ | .circuit _ body => body
  | _ => []

def bodyExpansion (receipts : List Semantics.ObservingFunction.Receipt) (events : List RawEvent) : WorkM Nat := do
  let steps := events.flatMap physicalSteps
  exactWork (Exact.charge (16*(steps.length+1)*(receipts.length+1)))
  lift (readOption (steps.foldlM (Semantics.Function.countStep (receipts.map (·.expandedSteps))) 0))

theorem bodyExpansion_value (receipts : List Semantics.ObservingFunction.Receipt) (events : List RawEvent)
    (count work left : Nat) (ok : (bodyExpansion receipts events).run work = (.ok count,left)) :
    (events.flatMap physicalSteps).foldlM (Semantics.Function.countStep (receipts.map (·.expandedSteps))) 0 =
      some count := by
  obtain ⟨_,paid,_,ran⟩ := bind_success _ _ work left count ok
  have read := (lift_success _ _ paid left ran).1
  cases found : (events.flatMap physicalSteps).foldlM
      (Semantics.Function.countStep (receipts.map (·.expandedSteps))) 0 <;> simp_all [readOption]

structure Checked (receipts : List Semantics.ObservingFunction.Receipt)
    (before after : Semantics.RawTrace.Interface) (operations : List Semantics.Raw.Op) where
  trace : Semantics.RawTrace.Prepared
  originalTrace : Semantics.RawTrace.interval before operations = some trace
  finalFrame : trace.state = after
  counts : Counts
  measured : counts = readCounts before.frame.length trace.events
  expandedBodySteps : Nat
  expansionRead : ∃ first last,(bodyExpansion receipts trace.events).run first = (.ok expandedBodySteps,last)

theorem Checked.bounds_each_event {receipts before after operations} (checked : Checked receipts before after operations)
    (actual : RawEvent) (member : actual ∈ checked.trace.events) :
    (eventCounts actual).peakWires ≤ checked.counts.peakWires := by
  rw [checked.measured]
  exact peak_bounds_event _ _ actual member

theorem Checked.clean {receipts before after input output wire table body logical}
    (checked : Checked receipts before after [.certifiedCompute input output [wire] table body logical]) :
    checked.counts = ⟨before.frame.length+1,1,1,2,body.length,0⟩ := by
  have traced := checked.originalTrace
  simp only [Semantics.RawTrace.interval,List.foldlM_cons,List.foldlM_nil,Semantics.RawTrace.advance,
    Semantics.RawTrace.step,bind,Option.bind,pure] at traced
  cases inputRead : Semantics.RawTrace.take before input with
  | none => simp [inputRead] at traced
  | some found =>
    rcases found with ⟨port,next⟩
    simp [inputRead] at traced
    rw [checked.measured,← traced]
    exact clean_counts _ _ _ _ _ _

private theorem take_frame {state next : Semantics.RawTrace.Interface} {token : Nat}
    {port : Semantics.Raw.Port} (ran : Semantics.RawTrace.take state token = some (port,next)) :
    next.frame = state.frame := by
  unfold Semantics.RawTrace.take at ran
  cases read : state.live.find? (fun port => port.token == token) <;> simp_all
  rw [← ran.2]

theorem Checked.dirty {receipts before after data scratch joined packed output returned bits steps}
    (checked : Checked receipts before after [.join data scratch joined,.applyUnitary joined packed steps,
      .split packed output returned bits]) :
    checked.counts = ⟨before.frame.length,0,0,0,steps.length,0⟩ := by
  have traced := checked.originalTrace
  simp only [Semantics.RawTrace.interval,List.foldlM_cons,List.foldlM_nil,Semantics.RawTrace.advance,
    Semantics.RawTrace.step,bind,Option.bind,pure] at traced
  cases hd : Semantics.RawTrace.take before data with
  | none => simp [hd] at traced
  | some dataEntry =>
    rcases dataEntry with ⟨dataPort,afterData⟩
    cases hs : Semantics.RawTrace.take afterData scratch with
    | none => simp [hd,hs] at traced
    | some scratchEntry =>
      rcases scratchEntry with ⟨scratchPort,afterScratch⟩
      cases hj : Semantics.RawTrace.take
          (Semantics.RawTrace.insert afterScratch joined (dataPort.wires ++ scratchPort.wires)) joined with
      | none => simp [hd,hs,hj] at traced
      | some joinedEntry =>
        rcases joinedEntry with ⟨port,afterJoined⟩
        cases ha : Semantics.RawTrace.take (Semantics.RawTrace.insert afterJoined packed port.wires) packed with
        | none => simp [hd,hs,hj,ha] at traced
        | some appliedEntry =>
          rcases appliedEntry with ⟨applied,final⟩
          simp [hd,hs,hj,ha] at traced
          rw [checked.measured,← traced]
          have same := (take_frame hs).trans (take_frame hd)
          simp only [Semantics.RawTrace.insert,same,dirty_counts,List.length_map]

/-- The workspace checker already bounds the supported packets and their gate axes.
Reserve for scanning the full live frame, including zero-width owners. -/
def read (receipts : List Semantics.ObservingFunction.Receipt)
    (before after : Semantics.RawTrace.Interface) (operations : List Semantics.Raw.Op) :
    WorkM (Checked receipts before after operations) := do
  exactWork (Exact.charge (32*(Raw.rawFields ⟨[],operations,[],.unitary⟩+1)*
    (before.live.length+before.frame.length+1)))
  match trace : Semantics.RawTrace.interval before operations with
  | none => throw .request
  | some result =>
    if final : result.state = after then
      let expanded ← SourceTypes.NaturalAffine.witness (bodyExpansion receipts result.events)
      return ⟨result,trace,final,readCounts before.frame.length result.events,rfl,
        expanded.val,by with_reducible exact expanded.property⟩
    else throw .request

end QleisliKernel.Raw.WorkspaceResources
