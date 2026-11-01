import QleisliKernel.SourceTypes.SourceSyntax
import QleisliKernel.SourceTypes.SourceContext
import QleisliKernel.SourceTypes.PhaseApplication
import QleisliKernel.Raw.OwnerFlow

/-! Complete original quantum-body traversal with primitive/qmatch events.
General expressions have checked syntax rules. Qmatch uses its existing structural
operand rule and retains its arm table without validating arm implementations.
This source traversal alone
does not check qmatch arm implementations, actual Raw intervals, body semantics
or public-effect containment, and issues no execution handle or effect label.
Ordinary-value contexts and named/constructed/generic calls remain unsupported;
they must extend the same source traversal with their own checked rules.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceTrace
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Semantics.SourceOwners

private def adapt {α : Type} (value : Except String α) : Finite.WorkM α :=
  Finite.lift (value.mapError fun _ => .request)

inductive PrimitiveKind where
  | h | globalPhaseEighth
  deriving BEq, DecidableEq, Repr

def PrimitiveKind.name : PrimitiveKind → String
  | .h => "h"
  | .globalPhaseEighth => "global_phase_eighth"

def primitiveKind {sources caller scope tokens}
    (checked : CallName.Checked sources caller scope tokens) : Option PrimitiveKind :=
  match checked.decision with
  | .primitive _ _ _ _ _ _ .h _ => some .h
  | .primitive _ _ _ _ _ _ .globalPhaseEighth _ => some .globalPhaseEighth
  | _ => none

def typeMatches (kind : PrimitiveKind) (owner : Owner) : Bool :=
  match kind with | .h => owner.basis == [.bit] | .globalPhaseEighth => true

structure PrimitiveEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  scope : List String
  candidate : CallName.Checked sources caller scope call.call.callee
  kind : PrimitiveKind
  selected : primitiveKind candidate = some kind
  operand : Owner
  sourceType : typeMatches kind operand = true
  held : List Owner
  before : Environment
  remaining : Environment
  frame : (held ++ owners before).Perm ([operand] ++ held ++ owners remaining)

structure PhaseEvent (sources : Sources) (caller : String) where
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  scope : List String
  naturals : PhaseApplication.Naturals sources
  application : PhaseApplication.Checked sources caller naturals scope call
  operand : Owner
  bit : operand.basis = [.bit]
  held : List Owner
  before : Environment
  remaining : Environment
  frame : (held ++ owners before).Perm ([operand] ++ held ++ owners remaining)

inductive Event (sources : Sources) (caller : String) where
  | selection (event : QuantumSequence.Event) (held : List Owner) (scope : List String)
      (frame : (held ++ owners event.before).Perm
        ([event.selector,event.target] ++ held ++ owners event.remaining))
  | primitive (event : PrimitiveEvent sources caller)
  | phase (event : PhaseEvent sources caller)

def Event.qmatchOffset {sources caller} : Event sources caller → Option Nat
  | .selection event _ _ _ => some event.parsed.keyword.span.startByte
  | .primitive _ => none
  | .phase _ => none

def Event.callOffset {sources caller} : Event sources caller → Option Nat
  | .selection .. => none
  | .primitive event => some event.call.calleeOffset
  | .phase event => some event.call.calleeOffset

structure Outcome (sources : Sources) (caller : String) (before : Environment) where
  value : Value
  remaining : Environment
  events : List (Event sources caller)
  conserved : (owners before).Perm (valueOwners value ++ owners remaining)

namespace Meter

def tokenFields (tokens : List LocatedToken) : Nat :=
  (tokens.map fun token => token.text.utf8ByteSize+4).sum

def nameFields (names : List String) : Nat :=
  (names.map fun name => name.utf8ByteSize+1).sum

/-- Count actual delimiter ancestry before parsing. This adds no grammar/depth
limit: the existing readers still reject their own malformed/deep forms. Prefix
sharing removes repeated flat-let suffix scans; nested call/group and child-index
comparisons remain charged, retaining the previous 128 coefficient. -/
def syntaxWork (tokens : List LocatedToken) : Nat :=
  let (_,fields) := tokens.foldl (fun (depth,total) token =>
    let total := total+(token.text.utf8ByteSize+4)*(depth+2)
    let depth := if ["(","[","{"].contains token.text then depth+1
      else if [")","]","}"].contains token.text then depth-1 else depth
    (depth,total)) (0,0)
  128*(fields+1)

def environmentCells (environment : Environment) : Nat :=
  (environment.map fun cell => cell.name.utf8ByteSize+cell.value.length+2).sum

/-- Pairwise owner comparisons include full nominal origins and value forests,
not just widths or owner counts. Each actual permutation check is charged. -/
def permutationWork (left right : List Owner) : Nat :=
  8*((left.length+1)*(Raw.OwnerFlow.fields right+1)+
    (right.length+1)*(Raw.OwnerFlow.fields left+1))

def moveWork (tokens : List LocatedToken) (environment : Environment) : Nat :=
  128+8*(tokenFields tokens+environmentCells environment+1)*(environment.length+1)

end Meter

private def outcome {sources caller} (before : Environment) (value : Value)
    (remaining : Environment) (events : List (Event sources caller)) :
    Finite.WorkM (Outcome sources caller before) := do
  Finite.exactWork (Exact.charge (8*(Meter.environmentCells before+
    Meter.environmentCells remaining+value.length+1)+
    Meter.permutationWork (owners before) (valueOwners value ++ owners remaining)))
  if conserved : (owners before).Perm (valueOwners value ++ owners remaining) then
    return ⟨value,remaining,events,conserved⟩
  else throw .request

private def trees {parts} (children : SourceSyntax.Children parts) : List (Sigma SourceSyntax.Tree) :=
  children.trees

private def boundNames (pattern : List LocatedToken) : Except String (List String) := do
  let term ← QuantumMoves.parse 65 (pattern.map (·.text))
  return term.filterMap fun atom => match atom with | .name name => some name | _ => none

/-- Live bindings, persistent lexical names and held expression values remain
separate. The actual lookup context follows evaluation left-to-right. Reuse never
replaces the current lexical check or an original call/event occurrence. -/
def evalWithNaturals (sources : Sources) (caller : String) : Nat →
    Option (PhaseApplication.Naturals sources) → List Owner → List String →
    (environment : Environment) → {tokens : List LocatedToken} → SourceSyntax.Tree tokens →
    SourceContext.Context sources caller →
    Finite.WorkM (Outcome sources caller environment × SourceContext.Context sources caller) :=
  Nat.rec (fun _ _ _ _ _ _ _ => throw .limit)
    (fun _ next naturals held scope environment tokens tree context => do
    match tree with
    | .move tokens _ _ =>
      Finite.exactWork (Exact.charge (Meter.moveWork tokens environment))
      let (value,remaining) ← adapt (QuantumMoves.eval (tokens.map (·.text)) environment)
      return (← outcome environment value remaining [],context)
    | .selection tokens parsed _ =>
      -- The structural selection reader reparses this actual site, checks its
      -- arm names against persistent scope and checks its own owner partition.
      Finite.exactWork (Exact.charge (Meter.syntaxWork tokens+
        Meter.moveWork tokens environment+
        8*(Meter.nameFields scope+Meter.tokenFields tokens+1)*(parsed.arms.length+1)+
        Meter.permutationWork (owners environment) (owners environment)))
      let selected ← adapt (QuantumSequence.expression tokens environment scope)
      let [event] := selected.events | throw .request
      Finite.guard (event.parsed == parsed) .request
      Finite.exactWork (Exact.charge (Meter.permutationWork (held ++ owners event.before)
        ([event.selector,event.target] ++ held ++ owners event.remaining)))
      if frame : (held ++ owners event.before).Perm
          ([event.selector,event.target] ++ held ++ owners event.remaining) then
        return (← outcome environment selected.value selected.remaining
          [.selection event held scope frame],context)
      else throw .request
    | .binding statement expression rest =>
      let (first,context) ← next naturals held scope environment expression context
      let pattern := statement.statement.pattern
      -- Bind may grow intermediate zero-owner cells before its final capacity
      -- check; include the actual pattern, value atoms and existing names now.
      Finite.exactWork (Exact.charge (2*Meter.syntaxWork pattern+
        8*(Meter.tokenFields pattern+Meter.environmentCells first.remaining+first.value.length+1)*
          (pattern.length+first.value.length+first.remaining.length+1)))
      let after ← adapt (QuantumMoves.bind (pattern.map (·.text)) first.value first.remaining)
      Finite.exactWork (Exact.charge (Meter.permutationWork (owners environment) (owners after)))
      Finite.guard (decide ((owners environment).Perm (owners after))) .request
      let names ← adapt (boundNames pattern)
      Finite.exactWork (Exact.charge (Meter.nameFields names+1))
      -- Static names and live quantum owners are separate. A runtime pattern
      -- must not hide an earlier static binding, even when that alias is unused.
      match naturals with
      | some current =>
        Finite.exactWork (Exact.charge
          (8*(Meter.nameFields names+1)*(Meter.nameFields current.staticNames+1)))
        Finite.guard (names.all fun name => !current.staticNames.contains name) .request
      | none => pure ()
      let (last,context) ← next naturals held (names ++ scope) after rest context
      Finite.exactWork (Exact.charge (first.events.length+1))
      return (← outcome environment last.value last.remaining (first.events ++ last.events),context)
    | .staticBindings leading _ rest =>
      let some current := naturals | throw .request
      let (updated,scope) ← PhaseApplication.extend sources caller leading current scope
      next (some updated) held scope environment rest context
    | .group group children =>
      let (values,remaining,events,context) ← (trees children).foldlM
          (fun (values,current,events,context) child => do
        Finite.exactWork (Exact.charge (8*(held.length+(values.map List.length).sum+
          values.length+events.length+1)))
        let holding := held ++ values.flatMap valueOwners
        let (result,context) ← next naturals holding scope current child.2 context
        return (values ++ [result.value],result.remaining,events ++ result.events,context))
        (([] : List Value),environment,([] : List (Event sources caller)),context)
      Finite.exactWork (Exact.charge (8*((values.map List.length).sum+values.length+1)))
      let value := if values.length == 1 &&
          (group.group.arguments.head?.bind (·.followingComma)).isNone then
          values.flatten
        else .tuple values.length :: values.flatten
      Finite.guard (value.length ≤ 128) .limit
      return (← outcome environment value remaining events,context)
    | .call call children =>
      if call.call.callee.getLast?.map (·.text) == some "]" then
        let some current := naturals | throw .request
        let application ← PhaseApplication.read sources caller current scope call
        Finite.exactWork (Exact.charge (8*(call.call.arguments.length+1)))
        let [child] := trees children | throw .request
        let (argument,context) ← next naturals held scope environment child.2 context
        let [.owner operand] := argument.value | throw .request
        Finite.exactWork (Exact.charge (Raw.OwnerFlow.fields [operand]+1))
        if bit : operand.basis = [.bit] then
          Finite.exactWork (Exact.charge (Meter.permutationWork (held ++ owners environment)
            ([operand] ++ held ++ owners argument.remaining)))
          if frame : (held ++ owners environment).Perm
              ([operand] ++ held ++ owners argument.remaining) then
            let event : PhaseEvent sources caller :=
              ⟨tokens,call,scope,current,application,operand,bit,held,environment,argument.remaining,frame⟩
            Finite.exactWork (Exact.charge (argument.events.length+1))
            return (← outcome environment [.owner operand] argument.remaining
              (argument.events ++ [.phase event]),context)
          else throw .request
        else throw .request
      let lookup ← SourceContext.read sources caller context scope call.call.callee
      let candidate ← Finite.lift lookup.answer.checked
      match selected : primitiveKind candidate with
      | none => throw .request
      | some kind =>
        Finite.exactWork (Exact.charge (8*(call.call.arguments.length+1)))
        let [child] := trees children | throw .request
        let (argument,context) ← next naturals held scope environment child.2 lookup.context
        let [.owner operand] := argument.value | throw .request
        Finite.exactWork (Exact.charge (Raw.OwnerFlow.fields [operand]+1))
        if sourceType : typeMatches kind operand = true then
          Finite.exactWork (Exact.charge (Meter.permutationWork (held ++ owners environment)
            ([operand] ++ held ++ owners argument.remaining)))
          if frame : (held ++ owners environment).Perm
              ([operand] ++ held ++ owners argument.remaining) then
            let event : PrimitiveEvent sources caller :=
              ⟨tokens,call,scope,candidate,kind,selected,operand,sourceType,held,
                environment,argument.remaining,frame⟩
            Finite.exactWork (Exact.charge (argument.events.length+1))
            return (← outcome environment [.owner operand] argument.remaining
              (argument.events ++ [.primitive event]),context)
          else throw .request
        else throw .request)

/-- Prepare static helpers once only when the original body contains static
syntax. Plain primitive bodies retain their existing lookup/work path. Aliases
remain local to the checked rest of the same original block. -/
def evalCached (sources : Sources) (caller : String) (fuel : Nat) (held : List Owner)
    (scope : List String) (environment : Environment) {tokens : List LocatedToken}
    (tree : SourceSyntax.Tree tokens) (context : SourceContext.Context sources caller) :
    Finite.WorkM (Outcome sources caller environment × SourceContext.Context sources caller) := do
  let naturals : Option (PhaseApplication.Naturals sources) ←
    if tokens.any (fun token => token.text == "static" || token.text == "[") then
      Option.some <$> PhaseApplication.prepare sources
    else pure none
  evalWithNaturals sources caller fuel naturals held scope environment tree context

/-- A complete original-body evaluation always starts its own empty context.
The public outcome and the Checked.traversed witness remain the actual reader. -/
def eval (sources : Sources) (caller : String) (fuel : Nat) (held : List Owner)
    (scope : List String) (environment : Environment) {tokens : List LocatedToken}
    (tree : SourceSyntax.Tree tokens) : Finite.WorkM (Outcome sources caller environment) := do
  let (result,_) ← evalCached sources caller fuel held scope environment tree {}
  return result

structure Checked (sources : Sources) (owner name : String) where
  signature : QuantumSignature.Checked sources owner name
  patterns : List (List String)
  parameters : QuantumOperands.parameterPatterns signature.original = .ok patterns
  initial : Environment
  seeded : QuantumOperands.seed signature patterns = .ok initial
  tree : SourceSyntax.Tree signature.original.occurrence.body
  parsed : SourceSyntax.read (signature.original.occurrence.body.length+1) 0 true
    signature.original.occurrence.body = .ok tree
  result : Outcome sources owner initial
  traversed : ∃ before after,
    (eval sources owner (signature.original.occurrence.body.length+1) []
      (initial.map (·.name)) initial tree).run before = (.ok result,after)
  complete : owners result.remaining = []
  returned : (owners initial).Perm (valueOwners result.value)
  shape : QuantumBody.resultShape signature.parts result.value = true
  resultTypes : (valueOwners result.value).map (·.basis) = signature.outputs
  everyQmatch : result.events.filterMap Event.qmatchOffset =
    QuantumSequence.originalOffsets signature.original.occurrence.body
  uniqueQmatches : (QuantumSequence.originalOffsets signature.original.occurrence.body).Nodup
  boundedQmatches : (result.events.filterMap Event.qmatchOffset).length ≤ 128
  callOffsets : List Nat
  originalCalls : tree.calls = .ok callOffsets
  everyCall : result.events.filterMap Event.callOffset = callOffsets
  uniqueCalls : callOffsets.Nodup

/-- Original signature/types/patterns seed all owners. Complete source traversal
returns every owner with its exact nominal basis and result shape. Event coverage
is separate for qmatch sites and postorder calls; no total-expression cap exists. -/
def read (sources : Sources) (owner name : String) : Finite.WorkM (Checked sources owner name) := do
  let signature ← QuantumSignature.read sources owner name
  let tokens := signature.original.occurrence.body
  -- Original signature work is unchanged. Parsing is precharged from actual
  -- token ancestry before SourceSyntax runs; source lookup pays only on misses.
  let roles := signature.inputs.zipIdx.map fun (basis,ordinal) => (⟨ordinal,basis⟩ : Owner)
  Finite.exactWork (Exact.charge (Meter.syntaxWork tokens+
    Meter.syntaxWork signature.original.occurrence.header+
    8*(Raw.OwnerFlow.fields roles+1)*(roles.length+1)))
  match parameters : QuantumOperands.parameterPatterns signature.original with
  | .error _ => throw .request
  | .ok patterns =>
    match seeded : QuantumOperands.seed signature patterns with
    | .error _ => throw .request
    | .ok initial =>
      match parsed : SourceSyntax.read (tokens.length+1) 0 true tokens with
      | .error _ => throw .request
      | .ok tree =>
        let result ← NaturalAffine.witness
          (eval sources owner (tokens.length+1) [] (initial.map (·.name)) initial tree)
        -- Complete filtering/traversal and ordered nominal result comparisons.
        -- Both uniqueness checks use a pairwise decider; no call-count cap is
        -- substituted for their actual quadratic work.
        let eventCount := result.val.events.length
        let outputs := valueOwners result.val.value
        let resultRoles := signature.outputs.zipIdx.map fun (basis,ordinal) => (⟨ordinal,basis⟩ : Owner)
        Finite.exactWork (Exact.charge (8*(Meter.tokenFields tokens+result.val.value.length+
          Meter.environmentCells result.val.remaining+1)+
          Meter.permutationWork (owners initial) outputs+
          8*(Raw.OwnerFlow.fields outputs+Raw.OwnerFlow.fields resultRoles+1)+
          16*(eventCount+1)^2))
        if complete : owners result.val.remaining = [] then
          if returned : (owners initial).Perm (valueOwners result.val.value) then
            if shape : QuantumBody.resultShape signature.parts result.val.value = true then
              if resultTypes : (valueOwners result.val.value).map (·.basis) = signature.outputs then
                if everyQmatch : result.val.events.filterMap Event.qmatchOffset =
                    QuantumSequence.originalOffsets tokens then
                  if uniqueQmatches : (QuantumSequence.originalOffsets tokens).Nodup then
                    if boundedQmatches : (result.val.events.filterMap Event.qmatchOffset).length ≤ 128 then
                      match originalCalls : tree.calls with
                      | .error _ => throw .request
                      | .ok callOffsets =>
                        if everyCall : result.val.events.filterMap Event.callOffset = callOffsets then
                          if uniqueCalls : callOffsets.Nodup then
                            return ⟨signature,patterns,parameters,initial,seeded,tree,parsed,result.val,
                              by with_reducible exact result.property,complete,returned,shape,resultTypes,
                              everyQmatch,uniqueQmatches,boundedQmatches,
                              callOffsets,originalCalls,everyCall,uniqueCalls⟩
                          else throw .request
                        else throw .request
                    else throw .limit
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
          else throw .request
        else throw .request

theorem Checked.allOriginalQmatches {sources owner name} (checked : Checked sources owner name) :
    checked.result.events.filterMap Event.qmatchOffset =
      QuantumSequence.originalOffsets checked.signature.original.occurrence.body := checked.everyQmatch

theorem Checked.allOriginalCalls {sources owner name} (checked : Checked sources owner name) :
    checked.result.events.filterMap Event.callOffset = checked.callOffsets := checked.everyCall

theorem Checked.completeOwnerReturn {sources owner name} (checked : Checked sources owner name) :
    (owners checked.initial).Perm (valueOwners checked.result.value) := checked.returned

theorem PrimitiveEvent.originalTokens {sources caller} (event : PrimitiveEvent sources caller) :
    event.call.call.render = event.tokens := event.call.original

theorem PrimitiveEvent.hRequiresBit {sources caller} (event : PrimitiveEvent sources caller)
    (kind : event.kind = .h) : event.operand.basis = [.bit] := by
  have sourceType := event.sourceType
  simpa [typeMatches,kind] using sourceType

end QleisliKernel.SourceTypes.SourceTrace
