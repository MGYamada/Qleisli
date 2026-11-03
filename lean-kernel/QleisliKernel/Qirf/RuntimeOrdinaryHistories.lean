import QleisliKernel.Qirf.RuntimeOrdinaryInputs
import QleisliKernel.Raw.StreamedInstrument

/-! Complete actual lazy histories for the common source/runtime body loop.
The exact original input/storage wrapper and final typed owner boundary are
required. Every canonical ordinary input and every actual hidden history is
retained; output equality is checked even for a zero operator. This gate does
not inspect coefficients, normalize probabilities, allocate a quantum matrix
or replace source-condition/local-action/code/Gram composition obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOrdinaryHistories
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open RuntimeOrdinarySSA
abbrev Stored := Semantics.RuntimeStorage.Value
abbrev SourceValue := SourceRuntimeValues.Value

private def outputOrdinal (values : Values) (basis : Semantics.FiniteCarrier.Basis)
    (storage : Semantics.OrdinaryValue.Storage) : WorkM Nat := do
  let _ ← OrdinaryStorage.read values basis storage
  let layout ← FiniteCarrier.read basis
  let ids ← OrdinaryFamily.storageIds [storage]
  guard (ids.length == layout.bits) .request
  let bits ← ids.mapM (Raw.Instrument.lookup values)
  exactWork (Exact.charge (32*(layout.labels.length+bits.length+1)))
  let code := Semantics.OrdinaryValue.littleEndian bits
  let ordinal := layout.labels.idxOf code
  guard (layout.labels[ordinal]? == some code) .equation
  return ordinal

private def result (bindings : RuntimeOwnerMap.Map) (reference : Valuation) (values : Values)
    (stored : Stored) : SourceValue → WorkM SourceValue :=
  WellFounded.fix (measure (fun current : Stored => current.length)).wf
    (C := fun _ => SourceValue → WorkM SourceValue) (fun current => match current with
      | [] => fun _ source => pure source
      | stored :: rest => fun visit source => do
        exactWork (Exact.charge (32*(SourceRuntimeValues.valueFields source+bindings.length+values.length+1)))
        match stored with
        | .tuple arity =>
          let .tuple sourceArity :: source := source | throw .request
          guard (sourceArity == arity) .request
          visit rest (by decreasing_tactic) source
        | .quantum owner =>
          let .owner role :: source := source | throw .request
          let some binding := RuntimeOwnerMap.byOwner bindings role | throw .request
          guard (binding.owner == role && binding.port == owner.port && role.basis == owner.basis) .request
          visit rest (by decreasing_tactic) source
        | .ordinary basis storage =>
          let (subtree,source) ← lift ((SourceRuntimeValues.splitValue source).mapError fun _ => .request)
          let (actual,expression) ← lift ((SourceRuntimeNominalValue.collapse subtree).mapError fun _ => .request)
          guard (actual == basis) .request
          let actual ← outputOrdinal values basis storage
          exactWork (Exact.charge (32*(SourceRuntimeValues.expressionSize expression+
            SourceRuntimeValues.expressionFields expression+1)*(values.length+1)))
          let expected ← lift (readOption (Semantics.SourceOrdinary.evaluate reference expression))
          guard (expected == actual) .equation
          visit rest (by decreasing_tactic) source) stored

def checkResult (bindings : RuntimeOwnerMap.Map) (reference : Valuation) (values : Values)
    (source : SourceValue) (stored : Stored) : WorkM Unit := do
  let remaining ← result bindings reference values stored source
  guard remaining.isEmpty .request

structure History (inputs : List Nat) (ssa : RuntimeOrdinaryBody.State)
    (bindings : RuntimeOwnerMap.Map) (source : SourceValue) (stored : Stored)
    (history : Raw.StreamedInstrument.History) where
  agreement : CheckedAgreement (RuntimeOrdinaryBody.valuation inputs ssa.measurements history.values)
    history.values ssa.table
  output : RuntimeInterval.Computed (checkResult bindings
    (RuntimeOrdinaryBody.valuation inputs ssa.measurements history.values) history.values source stored) ()

inductive Histories (inputs : List Nat) (ssa : RuntimeOrdinaryBody.State)
    (bindings : RuntimeOwnerMap.Map) (source : SourceValue) (stored : Stored) :
    List Raw.StreamedInstrument.History → Type where
  | nil : Histories inputs ssa bindings source stored []
  | cons {history rest} (head : History inputs ssa bindings source stored history)
      (tail : Histories inputs ssa bindings source stored rest) :
      Histories inputs ssa bindings source stored (history :: rest)

def readHistories (inputs : List Nat) (ssa : RuntimeOrdinaryBody.State)
    (bindings : RuntimeOwnerMap.Map) (source : SourceValue) (stored : Stored)
    (histories : List Raw.StreamedInstrument.History) : WorkM (Histories inputs ssa bindings source stored histories) :=
  WellFounded.fix (measure (fun current : List Raw.StreamedInstrument.History => current.length)).wf
    (C := fun current => WorkM (Histories inputs ssa bindings source stored current))
    (fun current => match current with
      | [] => fun _ => pure .nil
      | history :: rest => fun visit => do
        let reference := RuntimeOrdinaryBody.valuation inputs ssa.measurements history.values
        let agreement ← RuntimeOrdinarySSA.readAgreement reference history.values ssa.table
        let output ← NaturalAffine.witness (checkResult bindings reference history.values source stored)
        have unit : output.val = () := by cases output.val; rfl
        let tail ← visit rest (by decreasing_tactic)
        return .cons ⟨agreement,by with_reducible simpa only [unit] using output.property⟩ tail) histories

structure Row {sources owner name signature dependencies program body prepared runtime inputs}
    (initial : @RuntimeOrdinaryInputs.Checked sources owner name signature dependencies program body prepared runtime inputs)
    (ssa : RuntimeOrdinaryBody.State) (bindings : RuntimeOwnerMap.Map) (assignment : List Bool) where
  input : RuntimeOrdinaryInputs.Row initial assignment
  histories : List Raw.StreamedInstrument.History
  original : RuntimeInterval.Computed
    (Raw.StreamedInstrument.run dependencies 65 prepared.whole.prepared.events
      (Raw.StreamedInstrument.initial (program.classicalInputs.zip assignment))) histories
  nonempty : histories.isEmpty = false
  checked : Histories input.ordinals ssa bindings (RuntimeSourceBoundary.summary body).value runtime.storage histories

inductive Rows {sources owner name signature dependencies program body prepared runtime inputs}
    (initial : @RuntimeOrdinaryInputs.Checked sources owner name signature dependencies program body prepared runtime inputs)
    (ssa : RuntimeOrdinaryBody.State) (bindings : RuntimeOwnerMap.Map) : List (List Bool) → Type where
  | nil : Rows initial ssa bindings []
  | cons {assignment rest} (head : Row initial ssa bindings assignment) (tail : Rows initial ssa bindings rest) :
      Rows initial ssa bindings (assignment :: rest)

def readRows {sources owner name signature dependencies program body prepared runtime inputs}
    (initial : @RuntimeOrdinaryInputs.Checked sources owner name signature dependencies program body prepared runtime inputs)
    (ssa : RuntimeOrdinaryBody.State) (bindings : RuntimeOwnerMap.Map) (assignments : List (List Bool)) :
    WorkM (Rows initial ssa bindings assignments) :=
  WellFounded.fix (measure (fun current : List (List Bool) => current.length)).wf
    (C := fun current => WorkM (Rows initial ssa bindings current)) (fun current => match current with
      | [] => fun _ => pure .nil
      | assignment :: rest => fun visit => do
        let input ← RuntimeOrdinaryInputs.readRow initial assignment
        let histories ← NaturalAffine.witness
          (Raw.StreamedInstrument.run dependencies 65 prepared.whole.prepared.events
            (Raw.StreamedInstrument.initial (program.classicalInputs.zip assignment)))
        if nonempty : histories.val.isEmpty = false then
          let checked ← readHistories input.ordinals ssa bindings (RuntimeSourceBoundary.summary body).value
            runtime.storage histories.val
          let tail ← visit rest (by decreasing_tactic)
          return .cons ⟨input,histories.val,by with_reducible exact histories.property,nonempty,checked⟩ tail
        else throw .equation) assignments

structure Checked {sources owner name signature dependencies program body prepared runtime inputs}
    (initial : @RuntimeOrdinaryInputs.Checked sources owner name signature dependencies program body prepared runtime inputs)
    (ssa : RuntimeOrdinaryBody.State)
    {owners : RuntimeOwnerMap.Checked (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary body).value)
      prepared.whole.state}
    (outputs : RuntimeSourceBoundary.Outputs (RuntimeSourceBoundary.summary body).value
      prepared.whole.state owners runtime.storage program.outputs) where
  visible : RuntimeOrdinaryBody.Visible prepared.whole.state ssa
  outputIds : RuntimeInterval.Computed
    (OrdinaryFamily.storageIds ((RuntimeFamily.outputValues runtime).map Prod.snd)) program.classicalOutputs
  rows : Rows initial visible.ssa owners.bindings (OrdinaryDomain.assignments initial.domain)

/-- Consume the same typed final owner/storage boundary and every independent
canonical input row. The event loop must additionally retain all source/actual
condition checks and its complete local quantum/instrument composition proof. -/
def read {sources owner name signature dependencies program body prepared runtime inputs}
    (initial : @RuntimeOrdinaryInputs.Checked sources owner name signature dependencies program body prepared runtime inputs)
    (ssa : RuntimeOrdinaryBody.State)
    {owners : RuntimeOwnerMap.Checked (SourceRuntimeValues.valueOwners (RuntimeSourceBoundary.summary body).value)
      prepared.whole.state}
    (outputs : RuntimeSourceBoundary.Outputs (RuntimeSourceBoundary.summary body).value
      prepared.whole.state owners runtime.storage program.outputs) : WorkM (Checked initial ssa outputs) := do
  let visible ← RuntimeOrdinaryBody.readVisible prepared.whole.state ssa
  let outputIds ← NaturalAffine.witness
    (OrdinaryFamily.storageIds ((RuntimeFamily.outputValues runtime).map Prod.snd))
  if originalIds : outputIds.val = program.classicalOutputs then
    let rows ← readRows initial visible.ssa owners.bindings (OrdinaryDomain.assignments initial.domain)
    return ⟨visible,by with_reducible simpa only [originalIds] using outputIds.property,rows⟩
  else throw .request

theorem Histories.every {inputs ssa bindings source stored histories}
    (checked : Histories inputs ssa bindings source stored histories)
    (history : Raw.StreamedInstrument.History) (member : history ∈ histories) :
    Nonempty (History inputs ssa bindings source stored history) := by
  induction checked with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst history; exact ⟨head⟩
    · exact ih later

theorem Rows.every {sources owner name signature dependencies program body prepared runtime inputs initial ssa bindings assignments}
    (checked : @Rows sources owner name signature dependencies program body prepared runtime inputs initial ssa bindings assignments)
    (assignment : List Bool) (member : assignment ∈ assignments) : Nonempty (Row initial ssa bindings assignment) := by
  induction checked with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst assignment; exact ⟨head⟩
    · exact ih later

end QleisliKernel.Qirf.RuntimeOrdinaryHistories
