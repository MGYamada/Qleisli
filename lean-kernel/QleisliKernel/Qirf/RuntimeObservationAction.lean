import QleisliKernel.Qirf.RuntimeOwnerMap
import QleisliKernel.Qirf.SourceSequence
import QleisliKernel.SourceTypes.SourceRuntimeContext

/-! Original destructive primitive events bound to actual observing intervals.
The exact source owner selects the consumed token. Its measurement expression
is bound to the actual SSA output; every caller spectator survives unchanged.
This component neither erases observation nor replaces complete ordinary
expression/history, source traversal or final-root obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeObservationAction
open QleisliKernel QleisliKernel.Finite SourceTypes
open SourceRuntimeValues RuntimeOwnerMap
abbrev Position := SourceSequence.Position
abbrev Primitive := CallName.Primitive

def spectators {sources caller} (event : SourceRuntimeContext.PrimitiveEvent sources caller) : List Owner :=
  event.held ++ owners event.remaining

def expression {sources caller} (functionName : String)
    (event : SourceRuntimeContext.PrimitiveEvent sources caller) (operand : Owner) : Expression :=
  .measured ⟨caller,functionName,event.call.calleeOffset⟩ [] operand

def result {sources caller} (functionName : String)
    (event : SourceRuntimeContext.PrimitiveEvent sources caller) (operand : Owner) : Option Nat → Value
  | none => [.ordinary [.unit] .unit]
  | some _ => [.ordinary [.bit] (expression functionName event operand)]

inductive Reading (input : Nat) : Primitive → List Semantics.Observation.Op → Option Nat → Prop where
  | measure (output : Nat) : Reading input .measureZ [.measure input output] (some output)
  | discard : Reading input .discard [.discard input] none

def boundary (roles : List Owner) (state : Raw.Observation.State) (previous : Map) :
    WorkM (RuntimeOwnerMap.Checked roles state) := do
  let ordered ← RuntimeOwnerMap.order roles previous
  RuntimeOwnerMap.check roles state ordered

structure Checked {sources caller dependencies program} (functionName : String)
    (event : SourceRuntimeContext.PrimitiveEvent sources caller)
    (block : RuntimeInterval.Block dependencies program) (position : Position) (previous : Map) where
  originalOffset : position.offset = event.call.calleeOffset
  operand : Owner
  arguments : event.arguments = [[.owner operand]]
  consumed : event.consumed = [operand]
  allocated : event.allocated = []
  sourceType : event.kind = .measureZ → operand.basis = [.bit]
  interval : RuntimeInterval.Checked block position.start position.count
  before : RuntimeOwnerMap.Checked (operand :: spectators event) interval.before
  beforeRead : RuntimeInterval.Computed (boundary (operand :: spectators event) interval.before previous) before
  input : Binding
  inputRead : byOwner before.bindings operand = some input
  originalOwner : input.owner = operand
  inputMember : input ∈ before.bindings
  after : RuntimeOwnerMap.Checked (spectators event) interval.after
  afterRead : RuntimeInterval.Computed (boundary (spectators event) interval.after previous) after
  measured : Option Nat
  instruction : Reading input.port.token event.kind
    ((block.operations.drop position.start).take position.count) measured
  sourceValue : event.value = result functionName event operand measured
  observing : interval.after.observe = true

/-- A literal destructive primitive is checked in the authentic observing
block, with its exact original source occurrence and role. Other primitive
kinds refuse here; they do not acquire an observing or pure fallback. -/
def check {sources caller dependencies program} (functionName : String)
    (event : SourceRuntimeContext.PrimitiveEvent sources caller)
    (block : RuntimeInterval.Block dependencies program) (position : Position) (previous : Map) :
    WorkM (Checked functionName event block position previous) := do
  exactWork (Exact.charge (32*(valueFields event.value+(event.arguments.map valueFields).sum+
    Raw.OwnerFlow.fields (spectators event)+previous.length+1)))
  if originalOffset : position.offset = event.call.calleeOffset then
    match arguments : event.arguments with
    | [[.owner operand]] =>
      if histories : event.consumed = [operand] ∧ event.allocated = [] ∧
          (event.kind = .measureZ → operand.basis = [.bit]) then
        let interval ← RuntimeInterval.check block position.start position.count
        let before ← NaturalAffine.witness (boundary (operand :: spectators event) interval.before previous)
        match inputRead : byOwner before.val.bindings operand with
        | none => throw .request
        | some input =>
          if inputBound : input.owner = operand ∧ input ∈ before.val.bindings then
            let after ← NaturalAffine.witness (boundary (spectators event) interval.after previous)
            if observing : interval.after.observe = true then
              match kind : event.kind, literal : (block.operations.drop position.start).take position.count with
              | .measureZ,[.measure token output] =>
                if selected : token = input.port.token then
                  if sourceValue : event.value = result functionName event operand (some output) then
                    have instruction : Reading input.port.token event.kind
                        ((block.operations.drop position.start).take position.count) (some output) := by
                      rw [kind,literal,selected]
                      exact .measure output
                    return ⟨originalOffset,operand,arguments,histories.1,histories.2.1,histories.2.2,interval,
                      before.val,by with_reducible exact before.property,input,inputRead,inputBound.1,inputBound.2,
                      after.val,by with_reducible exact after.property,some output,instruction,sourceValue,observing⟩
                  else throw .request
                else throw .request
              | .discard,[.discard token] =>
                if selected : token = input.port.token then
                  if sourceValue : event.value = result functionName event operand none then
                    have instruction : Reading input.port.token event.kind
                        ((block.operations.drop position.start).take position.count) none := by
                      rw [kind,literal,selected]
                      exact .discard
                    return ⟨originalOffset,operand,arguments,histories.1,histories.2.1,histories.2.2,interval,
                      before.val,by with_reducible exact before.property,input,inputRead,inputBound.1,inputBound.2,
                      after.val,by with_reducible exact after.property,none,instruction,sourceValue,observing⟩
                  else throw .request
                else throw .request
              | _,_ => throw .request
            else throw .request
          else throw .request
      else throw .request
    | _ => throw .request
  else throw .request

def Checked.measurement {sources caller dependencies program functionName event block position previous}
    (checked : @Checked sources caller dependencies program functionName event block position previous) :
    Option (Expression × Nat) :=
  checked.measured.map fun output => (expression functionName event checked.operand,output)

theorem Reading.kind {input kind operations measured} (reading : Reading input kind operations measured) :
    kind = .measureZ ∨ kind = .discard := by
  cases reading with
  | measure => exact Or.inl rfl
  | discard => exact Or.inr rfl

theorem Checked.doesObserve {sources caller dependencies program functionName event block position previous}
    (checked : @Checked sources caller dependencies program functionName event block position previous) :
    event.kind = .measureZ ∨ event.kind = .discard :=
  checked.instruction.kind

end QleisliKernel.Qirf.RuntimeObservationAction
