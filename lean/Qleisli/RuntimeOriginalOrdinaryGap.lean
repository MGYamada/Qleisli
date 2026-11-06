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
open Qleisli.RuntimeObservingPrefix (Issued)
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
    (agrees : Agreement reference history.values table) (supported : Supports (Issued state) history)
    (checked : Computed (operations.foldlM (checkStep dependencies (checkOps dependencies fuel)) state) next) :
    ∃ events result,
      Semantics.Observation.readOps (fuel+1) state.quantum.reference operations =
        some (next.quantum.reference,events) ∧
      run dependencies (fuel+1) events history = some [result] ∧
      result.hidden = history.hidden ∧ result.operator = history.operator ∧
      Agreement reference result.values after ∧ Supports (Issued next) result := by
  induction sequence generalizing state next history with
  | nil table =>
    obtain ⟨work,left,read⟩ := checked
    have same := (pure_success _ _ work left read).1
    subst next
    exact ⟨[],history,rfl,rfl,rfl,rfl,agrees,supported⟩
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
    have unused : Semantics.OrdinaryValue.lookup history.values action.output = none :=
      RuntimeOriginalClassicalJoin.lookup_unissued (fun member => fresh (supported member))
    obtain ⟨bit,computed⟩ := evaluate action.definition agrees
    have independent := Qleisli.Raw.Instrument.Denotation.expression_reference _ _ _ _ _ computed
    let intermediate : History := {history with values := history.values ++ [(action.output,bit)]}
    have nextAgrees : Agreement reference intermediate.values action.after :=
      action.preserves agrees bit 0 0 unused computed
    have nextSupported : Supports (Issued middle) intermediate := by
      intro id member
      change id ∈ (history.values ++ [(action.output,bit)]).map Prod.fst at member
      change id ∈ middle.classical.map Prod.fst
      rw [ids,List.map_append]
      rw [List.map_append] at member
      rcases List.mem_append.mp member with old | new
      · exact List.mem_append.mpr (Or.inl (supported old))
      · exact List.mem_append.mpr (Or.inr new)
    obtain ⟨events,result,restRead,restRun,hidden,operator,afterAgrees,afterSupported⟩ :=
      ih middle next intermediate nextAgrees nextSupported ⟨middleWork,left,tailRead⟩
    let event := Event.classical action.raw action.output
    refine ⟨event::events,result,?_,?_,hidden,operator,afterAgrees,afterSupported⟩
    · change Semantics.Observation.readOps (fuel+1) state.quantum.reference ([operation] ++ operations) = _
      rw [RuntimeAdjacentSlices.readOps_append,read_one action]
      rw [quantum] at restRead
      change (do
        let (last,later) ← Semantics.Observation.readOps (fuel+1) state.quantum.reference operations
        pure (last,event::later)) = _
      rw [restRead]
      rfl
    · apply run_cons dependencies fuel event events history intermediate result _ restRun
      change (do
        let value ← Qleisli.Semantics.RawInstrument.expression history.values action.raw
        some [{history with values := history.values ++ [(action.output,value)]}]) = _
      rw [independent]
      rfl

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
  have checked := gap.checked.interval.intervalRead
  cases depth : block.fuel with
  | zero =>
    rw [depth] at checked
    obtain ⟨_,_,impossible⟩ := checked
    cases impossible
  | succ fuel =>
    rw [depth] at checked
    exact checked_sequence gap.checked.sequence dependencies fuel _ _ history reference
      agrees supported (RuntimeAdjacentSlices.underlying checked)

#print axioms original_gap

end Qleisli.RuntimeOriginalOrdinaryGap
