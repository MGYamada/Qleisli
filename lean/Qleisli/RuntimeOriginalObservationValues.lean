import Qleisli.RuntimeOriginalOrdinaryGap

/-! The source valuation keeps successful reads when an original observing
step appends an actual SSA value and its transported measurement key.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeOriginalObservationValues
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Semantics.SourceOrdinary
open RuntimeOrdinaryBody (Measurement valuation)
open RuntimeOrdinarySSA (Agreement Values Table bitValue)

private def Keeps {α : Type} (before after : Option α) : Prop :=
  ∀ ⦃value⦄, before = some value → after = some value

private theorem Keeps.same {α : Type} (value : Option α) : Keeps value value :=
  fun {_} read => read

private theorem Keeps.bind {α β : Type} {before after : Option α}
    {first second : α → Option β} (entry : Keeps before after)
    (body : ∀ value, Keeps (first value) (second value)) :
    Keeps (before >>= first) (after >>= second) := by
  intro result read
  cases found : before with
  | none => simp [found] at read
  | some value =>
    rw [entry found]
    exact body value (by simpa [found] using read)

structure Extends (before after : Valuation) : Prop where
  inputs : ∀ ordinal, Keeps (before.inputs ordinal) (after.inputs ordinal)
  basisInputs : ∀ ordinal, Keeps (before.basisInputs ordinal) (after.basisInputs ordinal)
  measured : ∀ origin calls owner, Keeps (before.measured origin calls owner) (after.measured origin calls owner)

theorem Extends.evaluates {before after : Valuation} (extends_ : Extends before after)
    (expression : Expression) : Keeps (evaluate before expression) (evaluate after expression) := by
  induction expression <;> rw [evaluate_unfold before,evaluate_unfold after]
  case input ordinal => exact extends_.inputs ordinal
  case basisInput ordinal => exact extends_.basisInputs ordinal
  case measured origin calls owner => exact extends_.measured origin calls owner
  case unit | bit _ | ordinal _ | project _ _ => exact Keeps.same _
  case combine stride first second firstIH secondIH =>
    simp only [evaluateStep]
    split
    · exact Keeps.same _
    · exact firstIH.bind (fun _ => secondIH.bind (fun _ => Keeps.same _))
  case field stride dimension receiver ih =>
    simp only [evaluateStep]
    split
    · exact Keeps.same _
    · exact ih.bind (fun _ => Keeps.same _)
  case equalsOrdinal ordinal value ih | not value ih =>
    exact ih.bind (fun _ => Keeps.same _)
  case xor first second firstIH secondIH | and first second firstIH secondIH =>
    exact firstIH.bind (fun _ => secondIH.bind (fun _ => Keeps.same _))
  case choose condition thenValue elseValue conditionIH thenIH elseIH =>
    apply conditionIH.bind
    intro value
    split
    · exact Keeps.same _
    · split
      · exact thenIH
      · exact elseIH

/-- Each defined source key retains its value when the original history
retains its reads and new measurement keys are appended. -/
theorem valuation_extend (inputs : List Nat) (before extra : List Measurement)
    {values next : Values} (retains : Semantics.OrdinaryValue.Extends values next) :
    Extends (valuation inputs before values) (valuation inputs (before++extra) next) := by
  refine ⟨fun _ => Keeps.same _,fun _ => Keeps.same _,?_⟩
  intro origin calls owner
  let key (entry : Measurement) := decide (entry.origin = origin ∧ entry.calls = calls ∧ entry.owner = owner)
  have found : Keeps (before.find? key) ((before++extra).find? key) := by
    intro entry read
    simp [List.find?_append,read]
  exact found.bind (fun entry =>
    (show Keeps (Semantics.OrdinaryValue.lookup values entry.output)
      (Semantics.OrdinaryValue.lookup next entry.output) from
        fun {_} read => retains _ _ read).bind
      (fun _ => Keeps.same _))

theorem agreement_extend_values (inputs : List Nat) (before extra : List Measurement)
    {values next actual : Values} {table : Table} (retains : Semantics.OrdinaryValue.Extends values next)
    (agrees : Agreement (valuation inputs before values) actual table) :
    Agreement (valuation inputs (before++extra) next) actual table := by
  intro id expression member
  obtain ⟨bit,present,computed⟩ := agrees id expression member
  exact ⟨bit,present,(valuation_extend inputs before extra retains).evaluates expression computed⟩

theorem agreement_append_values (inputs : List Nat) (before extra : List Measurement)
    (values added : Values) {table : Table}
    (agrees : Agreement (valuation inputs before values) values table) :
    Agreement (valuation inputs (before++extra) (values++added)) (values++added) table := by
  apply agreement_extend_values inputs before extra (Semantics.OrdinaryValue.append_extends values added)
  intro id expression member
  obtain ⟨bit,present,computed⟩ := agrees id expression member
  exact ⟨bit,Semantics.OrdinaryValue.append_extends values added _ _ present,computed⟩


open QleisliKernel.Finite
open Qleisli.RuntimeObservingPrefix (Issued issued_mono)
open Qleisli.RuntimeObservingValueRetention (Supports run_retains_values)
open Qleisli.Semantics.ObservingAction (History run)
open RuntimeInterval (Computed)

/-- The original classical gap agrees with the valuation of its returned
history, ready for the next checked instruction. -/
theorem original_gap_values {dependencies program block start count before ssa}
    (gap : @RuntimeOrdinaryBody.Gap dependencies program block start count before ssa)
    (inputs : List Nat) (history : History)
    (agrees : Agreement (valuation inputs ssa.measurements history.values) history.values ssa.table)
    (supported : Supports (Issued gap.checked.interval.before) history) :
    ∃ events result,
      Semantics.Observation.readOps block.fuel gap.checked.interval.before.quantum.reference
        ((block.operations.drop start).take count) =
        some (gap.checked.interval.after.quantum.reference,events) ∧
      run dependencies block.fuel events history = some [result] ∧
      result.hidden = history.hidden ∧ result.operator = history.operator ∧
      Agreement (valuation inputs gap.ssa.measurements result.values) result.values gap.ssa.table ∧
      Supports (Issued gap.checked.interval.after) result := by
  obtain ⟨events,result,read,executed,hidden,operator,after,support⟩ :=
    RuntimeOriginalOrdinaryGap.original_gap gap history _ agrees supported
  have retains := run_retains_values dependencies block.fuel events history executed result List.mem_cons_self
  refine ⟨events,result,read,executed,hidden,operator,?_,support⟩
  simpa only [List.append_nil,RuntimeOrdinaryBody.Gap.ssa] using
    agreement_extend_values inputs ssa.measurements [] retains after

private theorem measurement_step_ids {dependencies recurse state next input output}
    (checked : Computed (Raw.Observation.checkStep dependencies recurse state (.measure input output)) next) :
    ¬ Issued state output ∧ next.classical.map Prod.fst = state.classical.map Prod.fst ++ [output] := by
  obtain ⟨_,_,read⟩ := checked
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨result,_,body,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨_,_,_,done_⟩ := bind_success _ _ _ _ _ rest
  have same := (pure_success _ _ _ _ done_).1
  subst next
  obtain ⟨⟨port,consumed⟩,_,taken,rest⟩ := bind_success _ _ _ _ _ body
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ rest
  obtain ⟨updated,_,inserted,finish⟩ := bind_success _ _ _ _ _ rest
  have shape := (pure_success _ _ _ _ finish).1
  subst result
  have original := (lift_success _ _ _ _ taken).1
  unfold Raw.Observation.consume at original
  obtain ⟨_,_,returned⟩ := except_bind_success _ _ _ original
  have classical := congrArg (fun pair : Semantics.Raw.Port × Raw.Observation.State => pair.2.classical)
    (Except.ok.inj returned).symm
  obtain ⟨fresh,ids⟩ := Raw.Observation.classical_fresh consumed updated output (lift_success _ _ _ _ inserted).1
  change consumed.classical = state.classical at classical
  refine ⟨?_,?_⟩
  · simpa only [Issued,classical] using fresh
  · change updated.classical.map Prod.fst = _
    rw [ids,classical,List.map_append]
    rfl

private theorem measurement_ids {dependencies fuel state next input output}
    (checked : Computed (Raw.Observation.checkOps dependencies fuel state [.measure input output]) next) :
    ¬ Issued state output ∧ next.classical.map Prod.fst = state.classical.map Prod.fst ++ [output] := by
  cases fuel with
  | zero =>
    obtain ⟨_,_,impossible⟩ := checked
    cases impossible
  | succ fuel =>
    obtain ⟨work,left,folded⟩ := RuntimeAdjacentSlices.underlying checked
    rw [List.foldlM_cons] at folded
    obtain ⟨middle,budget,one,done_⟩ := bind_success _ _ _ _ _ folded
    have same := (pure_success _ _ budget left done_).1
    subst next
    exact measurement_step_ids ⟨work,budget,one⟩

private theorem checked_measurement {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    {output : Nat} (selected : observation.checked.measured = some output) :
    ∃ binding : Measurement, binding.output = output ∧
      path.transport (RuntimeObservationAction.expression functionName event observation.checked.operand) =
        .ok binding.expression ∧
      ssa.measurements.find? (fun entry =>
        decide (entry.origin = binding.origin ∧ entry.calls = binding.calls ∧ entry.owner = binding.owner)) = none ∧
      observation.ordinary =
        ⟨ssa.table ++ [(output,binding.expression)],ssa.measurements ++ [binding]⟩ := by
  obtain ⟨_,_,read⟩ := observation.ordinaryRead
  simp only [RuntimeOrdinaryBody.extendObservation,RuntimeObservationAction.Checked.measurement,selected,Option.map] at read
  obtain ⟨_,_,_,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨expression,_,transported,rest⟩ := bind_success _ _ _ _ _ rest
  have mapped := (lift_success _ _ _ _ transported).1
  have real : path.transport (RuntimeObservationAction.expression functionName event observation.checked.operand) =
      .ok expression := by
    cases found : path.transport (RuntimeObservationAction.expression functionName event observation.checked.operand) with
    | error reason => simp [found,Except.mapError] at mapped
    | ok result => simpa [found,Except.mapError] using mapped
  cases expression with
  | measured origin calls owner =>
    obtain ⟨_,_,keyGuard,rest⟩ := bind_success _ _ _ _ _ rest
    obtain ⟨_,_,_,finish⟩ := bind_success _ _ _ _ _ rest
    have shape := (pure_success _ _ _ _ finish).1
    have key := (guard_success _ _ _ _ keyGuard).1
    refine ⟨⟨origin,calls,owner,output⟩,rfl,real,?_,shape⟩
    rw [List.find?_eq_none,← List.any_eq_false]
    cases any : ssa.measurements.any (fun entry =>
        decide (entry.origin = origin ∧ entry.calls = calls ∧ entry.owner = owner)) with
    | false => rfl
    | true =>
      rw [any] at key
      cases key
  | _ => cases rest

private theorem reading_measure {input kind operations output}
    (reading : RuntimeObservationAction.Reading input kind operations (some output)) :
    operations = [.measure input output] := by
  cases reading
  rfl

/-- The value recorded by the actual erasure history is the value of the
transported source measurement. Discard keeps the source table and valuation. -/
theorem observation_agreement {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    (inputs : List Nat) (history : History) (outcome : Nat)
    (agrees : Agreement (valuation inputs ssa.measurements history.values) history.values ssa.table)
    (supported : Supports (Issued observation.checked.interval.before) history) :
    let values := match observation.checked.measured with
      | none => history.values
      | some id => history.values ++ [(id,outcome == 1)]
    Agreement (valuation inputs observation.ordinary.measurements values) values observation.ordinary.table ∧
      Supports (Issued observation.checked.interval.after) {history with values} := by
  cases measured : observation.checked.measured with
  | none =>
    obtain ⟨work,left,read⟩ := observation.ordinaryRead
    simp only [RuntimeOrdinaryBody.extendObservation,RuntimeObservationAction.Checked.measurement,measured,Option.map] at read
    rw [(pure_success _ _ work left read).1]
    refine ⟨agrees,?_⟩
    obtain ⟨_,_,checked⟩ := observation.checked.interval.intervalRead
    have keeps := (Raw.Observation.checkOps_history _ _ _ _ _ _ _ checked).2.2
    intro id member
    exact issued_mono keeps (supported member)
  | some id =>
    obtain ⟨binding,rfl,_,newKey,shape⟩ := checked_measurement observation measured
    let bit : Bool := outcome == 1
    have literal : ((block.operations.drop position.start).take position.count) =
        [.measure observation.checked.input.port.token binding.output] := by
      have instruction := observation.checked.instruction
      rw [measured] at instruction
      exact reading_measure instruction
    have interval := observation.checked.interval.intervalRead
    rw [literal] at interval
    obtain ⟨fresh,ids⟩ := measurement_ids interval
    have unused : Semantics.OrdinaryValue.lookup history.values binding.output = none :=
      RuntimeOriginalClassicalJoin.lookup_unissued (fun member => fresh (supported member))
    have found := Semantics.OrdinaryValue.lookup_append_fresh bit unused
    have value : evaluate (valuation inputs (ssa.measurements++[binding])
        (history.values++[(binding.output,bit)])) binding.expression = some (bitValue bit) := by
      rw [evaluate_unfold]
      simp only [Measurement.expression,evaluateStep,valuation,List.find?_append,newKey]
      simp [List.find?,found]
    have retained := agreement_append_values inputs ssa.measurements [binding] history.values
      [(binding.output,bit)] agrees
    change Agreement (valuation inputs observation.ordinary.measurements
      (history.values++[(binding.output,bit)])) (history.values++[(binding.output,bit)])
      observation.ordinary.table ∧
      Supports (Issued observation.checked.interval.after)
        {history with values := history.values++[(binding.output,bit)]}
    constructor
    · rw [shape]
      intro id expression member
      rcases List.mem_append.mp member with earlier | added
      · exact retained id expression earlier
      · have same : (id,expression) = (binding.output,binding.expression) := List.mem_singleton.mp added
        cases same
        exact ⟨bit,found,value⟩
    · intro id member
      change id ∈ (history.values++[(binding.output,bit)]).map Prod.fst at member
      change id ∈ observation.checked.interval.after.classical.map Prod.fst
      rw [ids]
      rw [List.map_append] at member
      rcases List.mem_append.mp member with old | new
      · exact List.mem_append.mpr (Or.inl (supported old))
      · exact List.mem_append.mpr (Or.inr new)

/-- Each result of the actual erasure event has the checked ordinary state. -/
theorem observation_step_values {sources rootOwner rootName caller functionName dependencies program
    path event block position before ssa}
    (observation : @RuntimeOrdinaryBody.Observation sources rootOwner rootName caller functionName dependencies
      program path event block position before ssa)
    (inputs : List Nat) (history : History)
    (agrees : Agreement (valuation inputs ssa.measurements history.values) history.values ssa.table)
    (supported : Supports (Issued observation.checked.interval.before) history)
    (recurse : List Semantics.Observation.Event → History → Option (List History))
    {results : List History}
    (executed : Qleisli.Semantics.ObservingAction.step dependencies recurse
      (.erase observation.checked.interval.before.quantum.reference.frame.length
        (observation.checked.input.port.wires.map
          observation.checked.interval.before.quantum.reference.frame.idxOf) observation.checked.measured)
      history = some results) :
    ∀ result ∈ results,
      Agreement (valuation inputs observation.ordinary.measurements result.values) result.values
        observation.ordinary.table ∧ Supports (Issued observation.checked.interval.after) result := by
  simp only [Qleisli.Semantics.ObservingAction.step] at executed
  rw [← Option.some.inj executed]
  intro result member
  obtain ⟨outcome,_,rfl⟩ := List.mem_map.mp member
  have after := observation_agreement observation inputs history outcome agrees supported
  cases measured : observation.checked.measured <;> simpa only [measured] using after

#print axioms original_gap_values
#print axioms observation_step_values

end Qleisli.RuntimeOriginalObservationValues
