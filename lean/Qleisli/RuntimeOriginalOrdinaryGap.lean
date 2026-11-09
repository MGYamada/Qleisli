import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeOriginalClassicalJoin
import Qleisli.RuntimeObservingValueRetention
import Qleisli.RawInstrumentDenotation

/-! Interpret the exact classical interval recorded by the original checker.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalOrdinaryGap
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open QleisliKernel.Semantics.Observation (Event)
open Raw.Observation (checkOps checkStep insertClassical)
open RuntimeInterval (Computed)
open RuntimeOrdinarySSA (Agreement Action Sequence)
open Qleisli.RuntimeObservingPrefix (Issued checkOps_reference)
open Qleisli.RuntimeObservingWrites (WritesWithin)
open Qleisli.RuntimeObservingValueRetention (Supports)
open Qleisli.Semantics.ObservingAction (History run step)

private theorem insertion {dependencies recurse state next table operation}
    (action : Action table operation)
    (checked : Computed (checkStep dependencies recurse state operation) next) :
    insertClassical state action.output = .ok next := by
  obtain ⟨_,_,read⟩ := checked
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨result,_,body,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,done_⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success _ _ _ _ done_).1
  subst next
  rw [action.literal] at body
  cases raw : action.raw <;>
    simp only [raw,RuntimeOrdinarySSA.instruction,Raw.Observation.checkAction] at body
  case constant bit => exact (lift_success _ _ _ _ body).1
  all_goals
    obtain ⟨_,_,_,inserted⟩ := bind_success _ _ _ _ _ body
    exact (lift_success _ _ _ _ inserted).1

private theorem lookup_eq {values : RuntimeOrdinarySSA.Values} {id : Nat} {bit : Bool}
    (found : Semantics.OrdinaryValue.lookup values id = some bit) :
    Raw.Instrument.lookup values id = pure bit := by
  change lift (readOption (Semantics.OrdinaryValue.lookup values id)) = _
  rw [found]
  rfl

private theorem evaluate {table raw source reference actual}
    (definition : RuntimeOrdinarySSA.Definition table raw source)
    (agrees : Agreement reference actual table) :
    ∃ bit, (Raw.Instrument.expression actual raw).run 0 = (.ok bit,0) := by
  cases definition with
  | constant bit => exact ⟨bit,rfl⟩
  | not input operand =>
    obtain ⟨bit,present,_⟩ := agrees input operand.expression operand.member
    simp only [Raw.Instrument.expression,lookup_eq present]
    exact ⟨!bit,rfl⟩
  | xor first second left right | and first second left right =>
    obtain ⟨a,ha,_⟩ := agrees first left.expression left.member
    obtain ⟨b,hb,_⟩ := agrees second right.expression right.member
    simp only [Raw.Instrument.expression,lookup_eq ha,lookup_eq hb]
    exact ⟨_,rfl⟩

private theorem read_one {table operation} (action : Action table operation)
    (fuel : Nat) (state : Raw.Observation.State) :
    Semantics.Observation.readOps (fuel+1) state.quantum.reference [operation] =
      some (state.quantum.reference,[.classical action.raw action.output]) := by
  conv_lhs => rw [action.literal,Raw.ObservationAgreement.read_succ]
  cases action.raw <;> rfl

private theorem run_cons (dependencies : List Semantics.Finite.Dependency) (fuel : Nat)
    (event : Event) (events : List Event) (initial middle final : History)
    (first : step dependencies (run dependencies fuel) event initial = some [middle])
    (rest : run dependencies (fuel+1) events middle = some [final]) :
    run dependencies (fuel+1) (event::events) initial = some [final] := by
  let advance := RuntimeNamedThreePackedInstrument.advance dependencies (run dependencies fuel)
  change (event::events).foldlM advance [initial] = _
  have one : advance [initial] event = some [middle] := by
    change ((do
      let groups ← [initial].mapM (step dependencies (run dependencies fuel) event)
      pure groups.flatten) : Option (List History)) = some [middle]
    simp [first]
  rw [List.foldlM_cons,one]
  exact rest

private theorem checked_sequence {table operations after} (sequence : Sequence table operations after)
    (dependencies : List Semantics.Finite.Dependency) (fuel : Nat)
    (state next : Raw.Observation.State) (history : History) (reference : RuntimeOrdinarySSA.Valuation)
    (inherited : Nat → Prop) (agrees : Agreement reference history.values table)
    (supported : Supports (fun id => inherited id ∨ Issued state id) history)
    (checked : Computed (operations.foldlM (checkStep dependencies (checkOps dependencies fuel)) state) next)
    {events : List Event}
    (literal : Semantics.Observation.readOps (fuel+1) state.quantum.reference operations =
      some (next.quantum.reference,events))
    (avoids : WritesWithin events (fun id => ¬ inherited id)) :
    ∃ result, run dependencies (fuel+1) events history = some [result] ∧
      result.hidden = history.hidden ∧ result.operator = history.operator ∧
      Agreement reference result.values after ∧
      Supports (fun id => inherited id ∨ Issued next id) result := by
  induction sequence generalizing state next history events with
  | nil table =>
    obtain ⟨work,left,read⟩ := checked
    have same := (pure_success _ _ work left read).1
    subst next
    have noEvents : [] = events := congrArg Prod.snd (Option.some.inj literal)
    subst events
    exact ⟨history,rfl,rfl,rfl,agrees,supported⟩
  | @cons table operation operations after action tail ih =>
    obtain ⟨work,left,read⟩ := checked
    rw [List.foldlM_cons] at read
    obtain ⟨middle,middleWork,headRead,tailRead⟩ := bind_success _ _ _ _ _ read
    have inserted := insertion action ⟨work,middleWork,headRead⟩
    obtain ⟨fresh,ids⟩ := Raw.Observation.classical_fresh _ _ _ inserted
    have quantum : middle.quantum = state.quantum := by
      obtain ⟨_,_,finish⟩ := except_bind_success _ _ _ inserted
      have same := congrArg Raw.Observation.State.quantum (Except.ok.inj finish).symm
      exact same
    let event := Event.classical action.raw action.output
    change Semantics.Observation.readOps (fuel+1) state.quantum.reference ([operation] ++ operations) = _ at literal
    rw [RuntimeAdjacentSlices.readOps_append,read_one action] at literal
    change (Semantics.Observation.readOps (fuel+1) state.quantum.reference operations >>= fun pair =>
      some (pair.1,event::pair.2)) = some (next.quantum.reference,events) at literal
    obtain ⟨⟨last,rest⟩,restRead,returned⟩ := Option.bind_eq_some_iff.mp literal
    cases Option.some.inj returned
    have noInherited := avoids List.mem_cons_self (Qleisli.RuntimeObservingWrites.WritesId.classical action.raw action.output)
    have unused : Semantics.OrdinaryValue.lookup history.values action.output = none :=
      RuntimeOriginalClassicalJoin.lookup_unissued (fun member => (supported member).elim noInherited fresh)
    obtain ⟨bit,computed⟩ := evaluate action.definition agrees
    have independent := Qleisli.Raw.Instrument.Denotation.expression_reference _ _ _ _ _ computed
    let intermediate : History := {history with values := history.values ++ [(action.output,bit)]}
    have nextAgrees : Agreement reference intermediate.values action.after :=
      action.preserves agrees bit 0 0 unused computed
    have nextSupported : Supports (fun id => inherited id ∨ Issued middle id) intermediate := by
      intro id member
      change id ∈ (history.values ++ [(action.output,bit)]).map Prod.fst at member
      change inherited id ∨ id ∈ middle.classical.map Prod.fst
      rw [ids,List.map_append]
      rw [List.map_append] at member
      rcases List.mem_append.mp member with old | new
      · exact (supported old).imp (fun proof => proof) (fun present => List.mem_append.mpr (.inl present))
      · exact .inr (List.mem_append.mpr (.inr new))
    have restLiteral : Semantics.Observation.readOps (fuel+1) middle.quantum.reference operations =
        some (next.quantum.reference,rest) := by rwa [quantum]
    have restAvoids : WritesWithin rest (fun id => ¬ inherited id) :=
      fun _ present _ write => avoids (List.mem_cons_of_mem _ present) write
    obtain ⟨result,restRun,hidden,operator,afterAgrees,afterSupported⟩ :=
      ih middle next intermediate nextAgrees nextSupported ⟨middleWork,left,tailRead⟩ restLiteral restAvoids
    refine ⟨result,?_,hidden,operator,afterAgrees,afterSupported⟩
    apply run_cons dependencies fuel event rest history intermediate result _ restRun
    change (do
      let value ← Qleisli.Semantics.RawInstrument.expression history.values action.raw
      some [{history with values := history.values ++ [(action.output,value)]}]) = _
    rw [independent]
    rfl

/-- An actual ordinary gap may carry inherited values outside its local
issued set. Its own literal writes must avoid those inherited identities. -/
theorem original_gap_with_inherited {dependencies program block start count before ssa}
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count before ssa)
    (history : History) (reference : RuntimeOrdinarySSA.Valuation) (inherited : Nat → Prop)
    (agrees : Agreement reference history.values ssa.table)
    (supported : Supports (fun id => inherited id ∨ Issued gap.checked.interval.before id) history)
    {events : List Event}
    (literal : Semantics.Observation.readOps block.fuel gap.checked.interval.before.quantum.reference
      ((block.operations.drop start).take count) = some (gap.checked.interval.after.quantum.reference,events))
    (avoids : WritesWithin events (fun id => ¬ inherited id)) :
    ∃ result, run dependencies block.fuel events history = some [result] ∧
      result.hidden = history.hidden ∧ result.operator = history.operator ∧
      Agreement reference result.values gap.ssa.table ∧
      Supports (fun id => inherited id ∨ Issued gap.checked.interval.after id) result := by
  have checked := gap.checked.interval.intervalRead
  cases depth : block.fuel with
  | zero =>
    rw [depth] at literal
    cases literal
  | succ fuel =>
    rw [depth] at checked literal
    exact checked_sequence gap.checked.sequence dependencies fuel _ _ history reference inherited
      agrees supported (RuntimeAdjacentSlices.underlying checked) literal avoids

/-- The independent run of the exact original ordinary gap preserves the
operator and hidden outcomes, and returns the checked source SSA values. -/
theorem original_gap {dependencies program block start count before ssa}
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count before ssa)
    (history : History) (reference : RuntimeOrdinarySSA.Valuation)
    (agrees : Agreement reference history.values ssa.table)
    (supported : Supports (Issued gap.checked.interval.before) history) :
    ∃ events result,
      Semantics.Observation.readOps block.fuel gap.checked.interval.before.quantum.reference
        ((block.operations.drop start).take count) =
        some (gap.checked.interval.after.quantum.reference,events) ∧
      run dependencies block.fuel events history = some [result] ∧
      result.hidden = history.hidden ∧ result.operator = history.operator ∧
      Agreement reference result.values gap.ssa.table ∧
      Supports (Issued gap.checked.interval.after) result := by
  obtain ⟨work,left,checked⟩ := gap.checked.interval.intervalRead
  obtain ⟨events,literal⟩ := checkOps_reference _ _ _ _ _ work left checked
  obtain ⟨result,executed,hidden,operator,ordinary,support⟩ :=
    original_gap_with_inherited gap history reference (fun _ => False) agrees
      (fun _ member => .inr (supported member)) literal (fun _ _ _ _ impossible => impossible)
  exact ⟨events,result,literal,executed,hidden,operator,ordinary,fun _ member => (support member).resolve_left id⟩

#print axioms original_gap_with_inherited
#print axioms original_gap

end Qleisli.RuntimeOriginalOrdinaryGap
