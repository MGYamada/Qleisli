import QleisliKernel.Qirf.RuntimeComputedUse
import QleisliKernel.CodeSpace

/-! Read both independent original actions for a certified computed scope.
The Raw interval must separately establish the same logical/use actions and
the complete clean-return equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeCertifiedComputed
open QleisliKernel Finite SourceTypes SourceRuntimeContext SourceRuntimeValues
open Semantics.Exact
open RuntimeComputedUse (Action sourceAction)
abbrev Owner := Semantics.SourceOwners.Owner

private def identity (dimension : Nat) : WorkM Matrix := do
  exactWork (Exact.charge ((dimension+1)^2))
  lift (arithmetic (Exact.Matrix.identity dimension))

def logicalAction {sources caller callerName} {signature : Signature sources caller callerName}
    {naturals scope basis reference}
    (logical : ComputedLogical signature naturals scope basis reference) (dimension : Nat) : WorkM Action := do
  match reference,logical with
  | none,.protectedScope => throw .request
  | some _,.certified operation .. =>
    match operation.description.nodes with
    | [.primitive kind actual] =>
      guard (actual == basis) .request
      RuntimeComputedUse.primitive
        (match kind with | .h => .h | .globalPhaseEighth => .globalPhaseEighth)
        actual operation.rows
    | [.provider owner name [] [] []] => do
      let some provider := operation.graph.root.provider | throw .request
      guard (provider.moduleName == owner && provider.declarationName == name) .request
      let signature ← SourceRuntimeContext.readSignature sources owner name {} (.source caller)
        signature.operations.catalogue
      guard (signature.parameters.map (·.tree) == [Semantics.RuntimeType.owner basis] &&
        signature.result.tree == Semantics.RuntimeType.owner basis) .request
      let body ← SourceRuntimeTrace.readBodyWithSignature signature
      let summary := body.checked.summary
      let [[.owner operand]] := summary.parameterValues | throw .request
      let [.owner returned] := summary.value | throw .request
      guard (operand.basis == basis && returned.basis == operand.basis &&
        summary.inferredEffect == .unitary) .request
      let action ← sourceAction sources false (SourceTrace.sourceFuel sources) [operand] [returned] (← identity dimension)
        body.checked.events
      return {action with rows := operation.rows ++ signature.sourceRows ++ summary.staticRows ++ action.rows}
    | _ => throw .request

private def useAction {sources caller} {event : ComputedEvent sources caller}
    (body : SourceRuntimeTrace.ComputedBody event) (dimension : Nat) : WorkM Action := do
  let auxiliary := event.initial.auxiliary
  let data := event.input
  exactWork (Exact.charge (32*(valueFields body.result.value + Raw.OwnerFlow.fields [data,auxiliary]+1)))
  guard (event.written.parts.logical.isSome && auxiliary.basis == [.bit] &&
    body.result.value == [.tuple 2,.owner event.returned.data,.owner event.returned.auxiliary] &&
    inferredEffect body.result.events == .unitary) .request
  let action ← sourceAction sources false (SourceTrace.sourceFuel sources) [data,auxiliary]
    [event.returned.data,event.returned.auxiliary] (← identity (2*dimension)) body.result.events
  return {action with rows := body.result.staticRows ++ action.rows}

structure Prepared {sources caller} (event : ComputedEvent sources caller) where
  predicate : RuntimeComputedPredicate.Source event
  body : SourceRuntimeTrace.ComputedBody event
  bodyRead : RuntimeInterval.Computed (SourceRuntimeTrace.readComputedSource event) body
  used : Action
  useRead : RuntimeInterval.Computed (useAction body predicate.layout.labels.length) used
  logical : Action
  logicalRead : RuntimeInterval.Computed (logicalAction event.logical predicate.layout.labels.length) logical

def prepare {sources caller} (event : ComputedEvent sources caller) : WorkM (Prepared event) := do
  let predicate ← RuntimeComputedPredicate.readSource event
  guard (predicate.layout.bits < 6) .limit
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readComputedSource event)
  let used ← NaturalAffine.witness (useAction body.val predicate.layout.labels.length)
  let logical ← NaturalAffine.witness (logicalAction event.logical predicate.layout.labels.length)
  return ⟨predicate,body.val,by with_reducible exact body.property,used.val,by with_reducible exact used.property,
    logical.val,by with_reducible exact logical.property⟩

def Prepared.rows {sources caller} {event : ComputedEvent sources caller} (prepared : Prepared event) :
    List (String × String) :=
  event.naturals.sourceRows ++ event.predicate.target.sourceRows ++
    prepared.predicate.body.checked.summary.staticRows ++ prepared.used.rows ++ prepared.logical.rows


open RuntimeStructuralAction (SourceState)
open RuntimePrimitiveSource (PortAt readPort)

structure Literal {sources caller dependencies program block start count}
    (event : ComputedEvent sources caller) (source : RuntimeComputedPredicate.Source event)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) where
  certifiedScope : event.written.parts.logical.isSome = true
  sourceOwner : event.nextOrdinal = before.nextOrdinal ∧
    event.initial.auxiliary ∉ before.issued
  frame : RuntimeOwnerMap.Checked (before.bindings.map (·.owner)) interval.before
  sameFrame : frame.bindings = before.bindings
  input : PortAt event.input before.bindings
  output : Semantics.Raw.Port
  auxiliary : Nat
  table : List Nat
  useSteps : List Semantics.Finite.Step
  logicalSteps : List Semantics.Finite.Step
  original : (block.operations.drop start).take count =
    [.pure (.certifiedCompute input.port.token output.token [auxiliary] table useSteps logicalSteps)]
  outputRead : PureInterval.ports interval.after [output.token] = some [output]
  wires : output.wires = input.port.wires
  exactTable : table = source.table
  width : input.port.bits = source.layout.bits
  spectators : PureInterval.spectators interval.before [input.port.token] =
    PureInterval.spectators interval.after [output.token]
  after : RuntimeOwnerMap.Checked ((RuntimeComputedPredicate.continued event before output).bindings.map (·.owner)) interval.after
  afterBindings : after.bindings = (RuntimeComputedPredicate.continued event before output).bindings

private def readLiteral {sources caller dependencies program block start count}
    (event : ComputedEvent sources caller) (source : RuntimeComputedPredicate.Source event)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) :
    WorkM (Literal event source interval before) := do
  exactWork (Exact.charge (64*(Raw.OwnerFlow.fields (event.input :: event.initial.auxiliary ::
    event.returned.data :: before.issued) + block.operations.length+before.bindings.length+1)))
  if certifiedScope : event.written.parts.logical.isSome = true then
    if sourceOwner : event.nextOrdinal = before.nextOrdinal ∧
        event.initial.auxiliary ∉ before.issued then
      let frame ← RuntimeOwnerMap.checkBindings (before.bindings.map (·.owner)) interval.before before.bindings
      let input ← readPort event.input before.bindings
      match original : (block.operations.drop start).take count with
      | [.pure (.certifiedCompute inputToken outputToken [auxiliary] table useSteps logicalSteps)] =>
        match returned : PureInterval.ports interval.after [outputToken] with
        | some [output] =>
          if ports : inputToken = input.port.token ∧ outputToken = output.token ∧ output.wires = input.port.wires then
            let tableRead ← RuntimeComputedPredicate.checkTable source table
            if width : input.port.bits = source.layout.bits then
              if spectators : PureInterval.spectators interval.before [input.port.token] =
                  PureInterval.spectators interval.after [output.token] then
                let next := RuntimeComputedPredicate.continued event before output
                let after ← RuntimeOwnerMap.checkBindings (next.bindings.map (·.owner)) interval.after next.bindings
                return ⟨certifiedScope,sourceOwner,frame.val,frame.property,input,output,auxiliary,table,useSteps,logicalSteps,
                  by simpa only [ports.1,ports.2.1] using original,
                  by simpa only [ports.2.1] using returned,ports.2.2,tableRead.down,width,spectators,
                  after.val,after.property⟩
              else throw .request
            else throw .request
          else throw .request
        | _ => throw .request
      | _ => throw .request
    else throw .request
  else throw .request

def Literal.operation {sources caller dependencies program block start count event source interval before}
    (literal : @Literal sources caller dependencies program block start count event source interval before) :
    Semantics.Raw.Op :=
  .certifiedCompute literal.input.port.token literal.output.token [literal.auxiliary] literal.table
    literal.useSteps literal.logicalSteps

structure Equation (basis : Semantics.FiniteCarrier.Basis) (readPhysical : WorkM Matrix) (expected : Matrix) where
  code : Matrix
  codeRead : RuntimeInterval.Computed (FiniteCarrier.code basis) code
  emitted : Matrix
  emittedRead : RuntimeInterval.Computed readPhysical emitted
  action : CodeSpace.Map code code emitted
  equation : action.logical = expected

private def readEquation (basis : Semantics.FiniteCarrier.Basis) (readPhysical : WorkM Matrix) (expected : Matrix) :
    WorkM (Equation basis readPhysical expected) := do
  let code ← NaturalAffine.witness (FiniteCarrier.code basis)
  let emitted ← NaturalAffine.witness readPhysical
  let action ← CodeSpace.readMap code.val code.val emitted.val
  exactWork (Exact.charge (8*(action.logical.entries.length+expected.entries.length+1)))
  if equation : action.logical = expected then
    return ⟨code.val,by with_reducible exact code.property,emitted.val,by with_reducible exact emitted.property,action,equation⟩
  else throw .equation

structure Checked {sources caller dependencies program block start count}
    {event : ComputedEvent sources caller} (prepared : Prepared event)
    (interval : @RuntimeInterval.Checked dependencies program block start count) (before : SourceState) where
  literal : Literal event prepared.predicate interval before
  used : Equation (.pair :: event.input.basis ++ [.bit])
    (circuitMatrix dependencies (Raw.circuit (literal.input.port.bits+1) literal.useSteps)) prepared.used.matrix
  logical : Equation event.input.basis
    (Raw.clean dependencies literal.input.port.bits literal.input.port.bits 1 literal.table
      literal.useSteps literal.logicalSteps) prepared.logical.matrix

def read {sources caller dependencies program block start count} {event : ComputedEvent sources caller}
    (prepared : Prepared event) (interval : @RuntimeInterval.Checked dependencies program block start count)
    (before : SourceState) : WorkM (Checked prepared interval before) := do
  let literal ← readLiteral event prepared.predicate interval before
  let bits := literal.input.port.bits
  let used ← readEquation (.pair :: event.input.basis ++ [.bit])
    (circuitMatrix dependencies (Raw.circuit (bits+1) literal.useSteps)) prepared.used.matrix
  let logical ← readEquation event.input.basis
    (Raw.clean dependencies bits bits 1 literal.table literal.useSteps literal.logicalSteps) prepared.logical.matrix
  return ⟨literal,used,logical⟩

end QleisliKernel.Qirf.RuntimeCertifiedComputed
