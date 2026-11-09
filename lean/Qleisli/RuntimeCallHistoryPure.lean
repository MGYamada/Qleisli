import Qleisli.RuntimeCallHistoryRead
import Qleisli.RuntimeCallTraceCircuit

/-! Lift a checked pure action into the same ordered observing-history
relation. The actual finite input rows suffice for every reference column.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel
open Semantics.Finite (Dependency)
open Semantics.Raw (Port)
open Semantics.RawTrace (Interface)
open Raw.Observation (checkStep checkOps)
open Raw.ObservationAgreement (readStep)
open RuntimeCallTraceFrames (Partition WireOrder)
open Qleisli.Semantics.ObservingAction (History)
open Qleisli.Semantics.RawAction (events)
open Qleisli.RuntimeNamedThreePackedInstrument (pureHistory run_pure pureHistory_operator_congr)

/-- A pair of actual pure event lists acts on the same local coefficients.
The row bound uses the final parent frame, so this law also supports growth. -/
def PureAction (dependencies : List Dependency) (parent child parentAfter childAfter : Interface)
    (spectators : List Port) (parentEvents childEvents : List Semantics.Raw.Event) : Prop :=
  ∀ (joint : Nat → Nat → ℂ) row, row < 2^parentAfter.frame.length →
    events dependencies parentEvents (fun input =>
      joint (project parent child.frame input) (project parent (WireOrder spectators) input)) row =
    events dependencies childEvents (fun input => joint input (project parentAfter (WireOrder spectators) row))
      (project parentAfter childAfter.frame row)

theorem pure_histories (dependencies : List Dependency) (fuel : Nat)
    (parent child parentAfter childAfter : Interface) (spectators : List Port)
    (parentEvents childEvents : List Semantics.Raw.Event)
    (bounds : RawFiniteRows.BoundedEvents parent.frame.length parentEvents parentAfter.frame.length)
    (action : PureAction dependencies parent child parentAfter childAfter spectators parentEvents childEvents)
    (actual : History) (localHistory : Nat → History)
    (agrees : Agrees parent child spectators actual localHistory) :
    Results dependencies (fuel+1) parentAfter childAfter spectators
      (parentEvents.map Semantics.Observation.Event.pure) (childEvents.map Semantics.Observation.Event.pure)
      actual localHistory [pureHistory dependencies parentEvents actual]
      [fun high => pureHistory dependencies childEvents (localHistory high)] := by
  refine ⟨run_pure dependencies fuel parentEvents actual,
    fun high => run_pure dependencies fuel childEvents (localHistory high),
    .cons ⟨agrees.values,agrees.hidden,?_⟩ .nil⟩
  intro row col bound
  let joint := fun low high => (localHistory high).operator low col
  let input := fun low column =>
    (localHistory (project parent (WireOrder spectators) low)).operator (project parent child.frame low) column
  exact (pureHistory_operator_congr bounds dependencies actual input
    (fun column low bounded => agrees.operator low column bounded) col row bound).trans
      (action joint row bound)

/-- The pair of native pure reads determines the event lists and all frame
bounds. A local coefficient law for those exact transitions supplies the
observing-history result, without any extra execution premise. -/
theorem checked_pure (dependencies : List Dependency) (fuel : Nat)
    (parent child parentAfter childAfter : Raw.Observation.State) (spectators : List Port)
    (operation : Semantics.Raw.Op) {parentWork parentLeft childWork childLeft : Nat}
    (parentRead : (checkStep dependencies (checkOps dependencies fuel) parent (.pure operation)).run
      parentWork = (.ok parentAfter,parentLeft))
    (childRead : (checkStep dependencies (checkOps dependencies fuel) child (.pure operation)).run
      childWork = (.ok childAfter,childLeft))
    (action : ∀ (p c : Raw.Transition),
      Raw.step (dependencies.map (·.signature)) parent.quantum operation = .ok p →
      Raw.step (dependencies.map (·.signature)) child.quantum operation = .ok c →
      Partition p.state.reference c.state.reference spectators ∧
      PureAction dependencies parent.quantum.reference child.quantum.reference
        p.state.reference c.state.reference spectators p.events c.events)
    (actual : History) (localHistory : Nat → History)
    (agrees : Agrees parent.quantum.reference child.quantum.reference spectators actual localHistory) :
    ∃ parents children, CheckedResults dependencies fuel parent child parentAfter childAfter spectators
      (.pure operation) actual localHistory parents children := by
  obtain ⟨p,pStep,pAfter,_,_⟩ := RuntimeIntervalRawFold.checkStep_pure_raw _ _ _ _ _ _ _ parentRead
  obtain ⟨c,cStep,cAfter,_,_⟩ := RuntimeIntervalRawFold.checkStep_pure_raw _ _ _ _ _ _ _ childRead
  obtain ⟨pEvents,pTrace,pBounds⟩ := RawFiniteRows.checked_step _ _ _ _ _ _ _ parentRead
  subst parentAfter
  subst childAfter
  have pOriginal := Raw.step_reference _ _ _ _ pStep
  have cOriginal := Raw.step_reference _ _ _ _ cStep
  have eventEq : pEvents = p.events := congrArg Prod.snd (Option.some.inj (pTrace.symm.trans pOriginal))
  subst pEvents
  obtain ⟨partition,law⟩ := action p c pStep cStep
  refine ⟨[pureHistory dependencies p.events actual],[fun high => pureHistory dependencies c.events (localHistory high)],
    ⟨partition,p.events.map Semantics.Observation.Event.pure,c.events.map Semantics.Observation.Event.pure,?_,?_,?_,?_,?_⟩⟩
  · simp [readStep,pOriginal]
  · simp [readStep,cOriginal]
  · exact Qleisli.RuntimeObservingWrites.WritesWithin.pures _ _
  · exact Qleisli.RuntimeObservingWrites.WritesWithin.pures _ _
  · exact pure_histories dependencies fuel _ _ _ _ spectators _ _ pBounds law actual localHistory agrees

/-- Promote the fixed circuit law to the event-list law used by the observing
fold, retaining the actual post interfaces. -/
theorem _root_.Qleisli.RuntimeCallTraceCircuit.Transfer.pure_action
    {dependencies : List Dependency} {parent child : Raw.State} {spectators : List Port}
    {p c : Raw.Transition}
    (fixed : RuntimeCallTraceCircuit.Transfer dependencies parent child spectators p c) :
    PureAction dependencies parent.reference child.reference p.state.reference c.state.reference
      spectators p.events c.events := by
  intro joint row _
  have pFrame : p.state.reference.frame = parent.reference.frame := fixed.parentFrame
  have cFrame : c.state.reference.frame = child.reference.frame := fixed.childFrame
  unfold project Semantics.RawTrace.axes
  rw [pFrame,cFrame]
  exact fixed.operator joint row

#print axioms pure_histories
#print axioms checked_pure
end Qleisli.RuntimeCallHistory
