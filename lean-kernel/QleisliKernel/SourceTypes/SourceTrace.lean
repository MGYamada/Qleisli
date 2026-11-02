import QleisliKernel.SourceTypes.SourceSyntax
import QleisliKernel.SourceTypes.QuantumSequence
import QleisliKernel.SourceTypes.SourceContext
import QleisliKernel.SourceTypes.PhaseApplication
import QleisliKernel.SourceTypes.SourceCalls
import QleisliKernel.SourceTypes.SourceOperationApplication
import QleisliKernel.SourceTypes.SourceRows
import QleisliKernel.Raw.OwnerFlow

/-! Complete original quantum-body traversal with primitive/qmatch events.
General expressions have checked syntax rules. Qmatch uses its existing structural
operand rule and retains its arm table without validating arm implementations.
This source traversal alone
does not check qmatch arm implementations, actual Raw intervals, body semantics
or public-effect containment, and issues no execution handle or effect label.
Named calls reuse this traversal on each complete original callee before exact
owner transport. Ordinary/observing runtime contexts have their separate typed
value/history rule; constructed operation access remains an independent check.
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

private theorem primitiveKind_transport {sources caller scope first second}
    (same : first = second) (candidate : CallName.Checked sources caller scope first) :
    primitiveKind (same ▸ candidate) = primitiveKind candidate := by
  cases same
  rfl

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
      (naturals : Option (PhaseApplication.Naturals sources))
  | primitive (event : PrimitiveEvent sources caller)
  | phase (event : PhaseEvent sources caller)
  | named (event : SourceCalls.Event sources caller)
  | operation (event : SourceOperationApplication.Event sources caller)

def Event.qmatchOffset {sources caller} : Event sources caller → Option Nat
  | .selection event .. => some event.parsed.keyword.span.startByte
  | .primitive _ => none
  | .phase _ => none
  | .named _ => none
  | .operation _ => none

def Event.callOffset {sources caller} : Event sources caller → Option Nat
  | .selection .. => none
  | .primitive event => some event.call.calleeOffset
  | .phase event => some event.call.calleeOffset
  | .named event => some event.call.calleeOffset
  | .operation event => some event.call.calleeOffset

def Event.effect {sources caller} : Event sources caller → Semantics.Raw.Effect
  | .named event => event.effect
  | .operation event => event.effect
  | _ => .unitary

def inferredEffect {sources caller} (events : List (Event sources caller)) : Semantics.Raw.Effect :=
  events.foldl (fun effect event => SourceEffect.join effect event.effect) .unitary

def Event.staticRows {sources caller} : Event sources caller → List (String × String)
  | .selection _ _ _ _ naturals => naturals.map (·.sourceRows) |>.getD []
  | .primitive _ => []
  | .phase event => event.naturals.sourceRows
  | .named event => event.target.naturals.sourceRows ++ event.target.signature.sourceRows ++
      event.target.selected.operationActuals.rows ++ event.target.selected.actuals.actuals.flatMap (·.sourceRows) ++
      ResolutionProvenance.sourceRows event.target.resolved ++ event.canonical.staticRows
  | .operation event => event.naturals.sourceRows ++ event.operation.rows

structure Outcome (sources : Sources) (caller : String) (before : Environment) where
  value : Value
  remaining : Environment
  events : List (Event sources caller)
  conserved : (owners before).Perm (valueOwners value ++ owners remaining)
  staticRows : List (String × String)

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

/-- Aggregate only already authenticated source rows. Charge full byte-sensitive
comparisons before deduplication so wrapper depth cannot duplicate row forests. -/
def retainStaticRows (rows : List (String × String)) : Finite.WorkM (List (String × String)) :=
  SourceRows.retain rows

private def outcome {sources caller} (before : Environment) (value : Value)
    (remaining : Environment) (events : List (Event sources caller)) (rows : List (String × String) := []) :
    Finite.WorkM (Outcome sources caller before) := do
  let staticRows ← retainStaticRows (rows ++ events.flatMap Event.staticRows)
  Finite.exactWork (Exact.charge (8*(Meter.environmentCells before+
    Meter.environmentCells remaining+value.length+1)+
    Meter.permutationWork (owners before) (valueOwners value ++ owners remaining)))
  if conserved : (owners before).Perm (valueOwners value ++ owners remaining) then
    return ⟨value,remaining,events,conserved,staticRows⟩
  else throw .request

private def trees {parts} (children : SourceSyntax.Children parts) : List (Sigma SourceSyntax.Tree) :=
  children.trees

private def boundNames (pattern : List LocatedToken) : Except String (List String) := do
  let term ← QuantumMoves.parsePattern 65 (pattern.map (·.text))
  return term.filterMap fun atom => match atom with | .name name => some name | _ => none

/-- Live bindings, persistent lexical names and held expression values remain
separate. The actual lookup context follows evaluation left-to-right. Reuse never
replaces the current lexical check or an original call/event occurrence. -/
def evalWithReader (sources : Sources) (caller : String)
    (readCallee : {owner name : String} → (signature : QuantumSignature.Checked sources owner name) →
      Finite.WorkM (SourceCalls.Canonical signature))
    (callerSignature : Option (Sigma (QuantumSignature.Checked sources caller))) : Nat →
    Option (PhaseApplication.Naturals sources) → List Owner → List String →
    (environment : Environment) → {tokens : List LocatedToken} → SourceSyntax.Tree tokens →
    SourceContext.Context sources caller →
    Finite.WorkM (Outcome sources caller environment × SourceContext.Context sources caller) :=
  Nat.rec (fun _ _ _ _ _ _ _ => throw .limit)
    (fun _ next naturals held scope environment tokens tree context => do
    match tree with
    | .empty .. => return (← outcome environment [.tuple 0] environment [],context)
    | .literal .. | .boolean .. | .conditional .. | .staticConditional .. | .basis .. |
        .variant .. | .record .. | .projection .. | .matching .. | .computed .. => throw .request
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
      let operationNames := callerSignature.map (fun signature => signature.2.operationNames) |>.getD []
      let selected ← adapt (QuantumSequence.expression tokens environment scope operationNames)
      let [event] := selected.events | throw .request
      let _ ← QuantumMatch.checkSelector parsed event.selector.basis
      Finite.guard (event.parsed == parsed) .request
      Finite.exactWork (Exact.charge (Meter.permutationWork (held ++ owners event.before)
        ([event.selector,event.target] ++ held ++ owners event.remaining)))
      if frame : (held ++ owners event.before).Perm
          ([event.selector,event.target] ++ held ++ owners event.remaining) then
        return (← outcome environment selected.value selected.remaining
          [.selection event held scope frame naturals],context)
      else throw .request
    | .selectionExpression tokens parsed _ selectorTree targetTree =>
      Finite.exactWork (Exact.charge (Meter.syntaxWork tokens+Meter.moveWork tokens environment+
        8*(Meter.nameFields scope+Meter.tokenFields tokens+1)*(parsed.arms.length+1)))
      let (selected,context) ← next naturals held scope environment selectorTree context
      let [.owner selector] := selected.value | throw .request
      let (targeted,context) ← next naturals (held ++ [selector]) scope selected.remaining targetTree context
      let [.owner target] := targeted.value | throw .request
      let _ ← QuantumMatch.checkSelector parsed selector.basis
      Finite.exactWork (Exact.charge (Meter.permutationWork (owners environment)
        ([selector,target] ++ owners targeted.remaining)+
        Meter.permutationWork (held ++ owners environment)
          ([selector,target] ++ held ++ owners targeted.remaining)+
        selected.events.length+targeted.events.length+1))
      let operationNames := callerSignature.map (fun signature => signature.2.operationNames) |>.getD []
      if unshadowed : QuantumSequence.armsAllowed scope operationNames parsed.arms = true then
        if distinct : selector.ordinal ≠ target.ordinal then
          if partition : (owners environment).Perm ([selector,target] ++ owners targeted.remaining) then
            if frame : (held ++ owners environment).Perm
                ([selector,target] ++ held ++ owners targeted.remaining) then
              let event : QuantumSequence.Event :=
                ⟨parsed,scope,operationNames,unshadowed,environment,selector,target,targeted.remaining,distinct,partition⟩
              return (← outcome environment [.tuple 2,.owner selector,.owner target] targeted.remaining
                (selected.events ++ targeted.events ++ [.selection event held scope frame naturals]),context)
            else throw .request
          else throw .request
        else throw .request
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
      return (← outcome environment last.value last.remaining (first.events ++ last.events)
        (first.staticRows ++ last.staticRows),context)
    | .sequence _ expression rest =>
      let (first,context) ← next naturals held scope environment expression context
      Finite.guard (valueOwners first.value == []) .request
      let (last,context) ← next naturals held scope first.remaining rest context
      Finite.exactWork (Exact.charge (first.events.length+1))
      return (← outcome environment last.value last.remaining (first.events ++ last.events)
        (first.staticRows ++ last.staticRows),context)
    | .staticBindings leading _ rest =>
      let some current := naturals | throw .request
      let (updated,scope) ← PhaseApplication.extend sources caller leading current scope
      let (result,context) ← next (some updated) held scope environment rest context
      let staticRows ← retainStaticRows (updated.sourceRows ++ result.staticRows)
      return ({result with staticRows := staticRows},context)
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
      let operationNames := callerSignature.map (fun signature => signature.2.operationNames) |>.getD []
      if SourceOperationApplication.selected operationNames call.call.callee then
        let some callerInfo := callerSignature | throw .request
        let current ← match naturals with
          | some current => pure current
          | none => PhaseApplication.prepareWithSignature callerInfo.2
        let (values,remaining,events,context) ← (trees children).foldlM
            (fun (values,current,events,context) child => do
          let (argument,context) ← next naturals (held ++ values.flatMap valueOwners)
            scope current child.2 context
          return (values ++ [argument.value],argument.remaining,events ++ argument.events,context))
          (([] : List Value),environment,([] : List (Event sources caller)),context)
        let arguments := values.map SourceOperationApplication.ofQuantum
        let targetBasis ← adapt (SourceOperationApplication.targetBasis call.call.callee arguments)
        let application ← SourceOperation.readWithInstantiation callerInfo.2.instantiation current.helpers.val
          current.environment scope call.call.callee current.generic (some targetBasis) (some callerInfo.2.supply)
        if applicable : application.graph.root.paths.applicable = true then
          Finite.exactWork (Exact.charge (16*(Raw.OwnerFlow.fields (values.flatMap valueOwners)+
            Raw.OwnerFlow.fields [⟨0,application.graph.root.input⟩,⟨0,application.graph.root.output⟩]+1)))
          match applied : SourceOperationApplication.apply application.graph.root.input application.graph.root.output
              (SourceOperationApplication.controlled call.call.callee) arguments callerInfo.2.inputs.length with
          | .error _ => throw .request
          | .ok (value,allocated,consumed,after) =>
            Finite.guard (allocated.isEmpty && consumed.isEmpty) .request
            let event : SourceOperationApplication.Event sources caller :=
              ⟨tokens,call,callerInfo.1,callerInfo.2.original,callerInfo.2.instantiation,current,scope,
                application,applicable,arguments,callerInfo.2.inputs.length,value,allocated,consumed,after,
                applied,held,owners remaining⟩
            let returned ← adapt (SourceOperationApplication.toQuantum value)
            return (← outcome environment returned remaining (events ++ [.operation event]),context)
        else throw .request
      let written ← adapt (StaticApplication.readSyntax call.call.callee)
      let lookup ← SourceContext.read sources caller context scope written.callee
      let candidate ← Finite.lift lookup.answer.checked
      if PhaseApplication.selected candidate then
        let some current := naturals | throw .request
        let application ← PhaseApplication.read sources caller current scope call
        Finite.exactWork (Exact.charge (8*(call.call.arguments.length+1)))
        let [child] := trees children | throw .request
        let (argument,context) ← next naturals held scope environment child.2 lookup.context
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
      match selected : primitiveKind candidate with
      | none =>
        let some callerInfo := callerSignature | throw .request
        let current ← match naturals with
          | some current => pure current
          | none => PhaseApplication.prepareWithSignature callerInfo.2
        let target ← SourceCalls.readTarget callerInfo.2 current written candidate
        let (values,remaining,events,context) ← (trees children).foldlM
            (fun (values,current,events,context) child => do
          Finite.exactWork (Exact.charge (8*(held.length+(values.map List.length).sum+
            values.length+events.length+1)))
          let holding := held ++ values.flatMap valueOwners
          let (argument,context) ← next naturals holding scope current child.2 context
          return (values ++ [argument.value],argument.remaining,events ++ argument.events,context))
            (([] : List Value),environment,([] : List (Event sources caller)),lookup.context)
        Finite.exactWork (Exact.charge (8*(Meter.environmentCells environment+
          (values.map List.length).sum+Raw.OwnerFlow.fields (values.flatMap valueOwners)+1)))
        match matched : SourceCalls.argumentOwners target.signature.inputs values with
        | .error _ => throw .request
        | .ok inputs =>
          let canonical ← readCallee target.signature
          match transported : SourceCalls.transport inputs canonical.value with
          | .error _ => throw .request
          | .ok value =>
            Finite.exactWork (Exact.charge (Meter.permutationWork (held ++ owners environment)
              (inputs ++ held ++ owners remaining)))
            if frame : (held ++ owners environment).Perm (inputs ++ held ++ owners remaining) then
              let event : SourceCalls.Event sources caller :=
                ⟨tokens,call,scope,target,canonical,values,inputs,matched,value,transported,
                  held,environment,remaining,frame⟩
              return (← outcome environment value remaining (events ++ [.named event]),context)
            else throw .request
      | some kind =>
        if same : written.callee = call.call.callee then
          let fullCandidate : CallName.Checked sources caller scope call.call.callee := same ▸ candidate
          have fullSelected : primitiveKind fullCandidate = some kind :=
            (primitiveKind_transport same candidate).trans selected
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
                ⟨tokens,call,scope,fullCandidate,kind,fullSelected,operand,sourceType,held,
                  environment,argument.remaining,frame⟩
              Finite.exactWork (Exact.charge (argument.events.length+1))
              return (← outcome environment [.owner operand] argument.remaining
                (argument.events ++ [.primitive event]),context)
            else throw .request
          else throw .request
        else throw .request)

/-- Independent call-chain fuel comes from the complete original source table,
not the token count of a small caller expression. Active declaration identities
reject cycles before they can become a fuel/work-exhaustion observation. -/
def sourceFuel (sources : Sources) : Nat :=
  (sources.toList.map fun row => row.2.utf8ByteSize+1).sum+1

def readNested (sources : Sources) (fuel : Nat) (active : List (String × String))
    {owner name : String} (signature : QuantumSignature.Checked sources owner name) :
    Finite.WorkM (SourceCalls.Canonical signature) :=
  match fuel with
  | 0 => throw .limit
  | fuel+1 => do
    Finite.exactWork (Exact.charge (8*(Meter.nameFields (active.flatMap fun (a,b) => [a,b])+
      owner.utf8ByteSize+name.utf8ByteSize+1)))
    Finite.guard (!(active.contains (owner,name))) .request
    let tokens := signature.original.occurrence.body
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
        Finite.guard (initial.all fun cell => !signature.staticNames.contains cell.name) .request
        match parsed : SourceSyntax.read (tokens.length+1) 0 true tokens with
        | .error _ => throw .request
        | .ok tree =>
          let generic ← NaturalAffine.witness (GenericTypeTrace.readWithTree signature.instantiation tree)
          let originalAsserted : PLift (SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true) ←
            if asserted : SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true then
              pure (⟨asserted⟩ : PLift (SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true))
            else throw .request
          let naturals ← if signature.staticNames.isEmpty &&
              !(tokens.any fun token => token.text == "static" || token.text == "[") then
            pure none
            else Option.some <$> PhaseApplication.prepareWithSignature signature
          let (result,_) ← evalWithReader sources owner
            (fun callee => readNested sources fuel ((owner,name) :: active) callee) (some ⟨name,signature⟩)
            (tokens.length+1) naturals []
            (signature.staticNames ++ initial.map (·.name)) initial tree {}
          Finite.exactWork (Exact.charge (8*(Meter.tokenFields tokens+result.value.length+
            Meter.environmentCells result.remaining+1)+
            Meter.permutationWork (owners initial) (valueOwners result.value)+
            8*(Raw.OwnerFlow.fields (valueOwners result.value)+Raw.OwnerFlow.fields roles+1)+
            16*(result.events.length+1)^2))
          if complete : owners result.remaining = [] then
            if returned : (owners initial).Perm (valueOwners result.value) then
              if shape : QuantumBody.resultShape signature.parts result.value = true then
                if types : (valueOwners result.value).map (·.basis) = signature.outputs then
                  Finite.guard (result.events.filterMap Event.qmatchOffset ==
                    QuantumSequence.originalOffsets tokens) .request
                  Finite.guard (decide ((QuantumSequence.originalOffsets tokens).Nodup)) .request
                  Finite.guard ((result.events.filterMap Event.qmatchOffset).length ≤ 128) .limit
                  let offsets ← adapt tree.calls
                  Finite.guard (result.events.filterMap Event.callOffset == offsets) .request
                  Finite.guard (decide offsets.Nodup) .request
                  if asserted : SourceEffect.permits signature.original.parsedHeader.effect
                      (inferredEffect result.events) = true then
                    let rows ← retainStaticRows (generic.val.sourceRows ++ result.staticRows)
                    return ⟨patterns,parameters,initial,seeded,tree,parsed,generic.val,
                      by with_reducible exact generic.property,originalAsserted.down,result.value,result.remaining,
                      complete,returned,shape,types,inferredEffect result.events,asserted,rows⟩
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
          else throw .request
termination_by fuel

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
  evalWithReader sources caller (fun signature => readNested sources (sourceFuel sources) [] signature)
    none fuel naturals held scope environment tree context

/-- Generic entry actuals seed the same lexical arithmetic used at every phase
and named call site. Plain nongeneric bodies keep the existing zero-setup path. -/
def evalSignature {sources owner name} (signature : QuantumSignature.Checked sources owner name)
    (initial : Environment) (tree : SourceSyntax.Tree signature.original.occurrence.body) :
    Finite.WorkM (Outcome sources owner initial) := do
  let tokens := signature.original.occurrence.body
  let naturals ← if signature.staticNames.isEmpty &&
      !(tokens.any fun token => token.text == "static" || token.text == "[") then pure none
    else Option.some <$> PhaseApplication.prepareWithSignature signature
  let (result,_) ← evalWithReader sources owner
    (fun callee => readNested sources (sourceFuel sources) [(owner,name)] callee)
    (some ⟨name,signature⟩) (tokens.length+1) naturals []
    (signature.staticNames ++ initial.map (·.name)) initial tree {}
  return result

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
  generic : GenericTypeTrace.Checked signature.original
  genericRead : ∃ before after,
    (GenericTypeTrace.readWithTree signature.instantiation tree).run before = (.ok generic,after)
  originalAsserted : SourceEffect.permits signature.original.parsedHeader.effect generic.inferredEffect = true
  result : Outcome sources owner initial
  traversed : ∃ before after,
    (evalSignature signature initial tree).run before = (.ok result,after)
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
  asserted : SourceEffect.permits signature.original.parsedHeader.effect
    (inferredEffect result.events) = true

/-- Reuse the actual checked signature without replacing its declaration,
original body, types or byte envelope. -/
structure Body {sources owner name} (signature : QuantumSignature.Checked sources owner name) where
  checked : Checked sources owner name
  originalSignature : checked.signature = signature

/-- Original signature/types/patterns seed all owners. Complete source traversal
returns every owner with its exact nominal basis and result shape. Event coverage
is separate for qmatch sites and postorder calls; no total-expression cap exists.
The selected-entry and arm paths share this one original-body implementation. -/
def readWithSignature {sources owner name} (signature : QuantumSignature.Checked sources owner name) :
    Finite.WorkM (Body signature) := do
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
      Finite.guard (initial.all fun cell => !signature.staticNames.contains cell.name) .request
      match parsed : SourceSyntax.read (tokens.length+1) 0 true tokens with
      | .error _ => throw .request
      | .ok tree =>
        let generic ← NaturalAffine.witness (GenericTypeTrace.readWithTree signature.instantiation tree)
        let originalAsserted : PLift (SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true) ←
          if asserted : SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true then
            pure (⟨asserted⟩ : PLift (SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true))
          else throw .request
        let result ← NaturalAffine.witness
          (evalSignature signature initial tree)
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
                            if asserted : SourceEffect.permits signature.original.parsedHeader.effect
                                (inferredEffect result.val.events) = true then
                              return ⟨⟨signature,patterns,parameters,initial,seeded,tree,parsed,generic.val,
                                by with_reducible exact generic.property,originalAsserted.down,result.val,
                                by with_reducible exact result.property,complete,returned,shape,resultTypes,
                                everyQmatch,uniqueQmatches,boundedQmatches,
                                callOffsets,originalCalls,everyCall,uniqueCalls,asserted⟩,rfl⟩
                            else throw .request
                          else throw .request
                        else throw .request
                    else throw .limit
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
          else throw .request
        else throw .request

/-- Fresh entry lookup delegates to the same checked-signature continuation.
The extra wrapper adds no work charge or acceptance condition. -/
def read (sources : Sources) (owner name : String) : Finite.WorkM (Checked sources owner name) := do
  let signature ← QuantumSignature.read sources owner name
  let body ← readWithSignature signature
  return body.checked

def Checked.sourceRows {sources owner name} (checked : Checked sources owner name) : List (String × String) :=
  checked.signature.sourceRows ++ checked.generic.sourceRows ++ checked.result.staticRows

/-- Native call intervals re-enter the same original-body reader. The fresh
computed return is compared with the canonical result used for caller transport;
the event's summary cannot supply acceptance for an unchecked callee. -/
def readNamedSource {sources caller} (event : SourceCalls.Event sources caller) :
    Finite.WorkM (Body event.signature) := do
  let body ← readWithSignature event.signature
  Finite.exactWork (Exact.charge (8*(body.checked.result.value.length+
    event.canonical.value.length+body.checked.result.events.length+
    Raw.OwnerFlow.fields (valueOwners body.checked.result.value ++ valueOwners event.canonical.value)+1)))
  Finite.guard (body.checked.result.value == event.canonical.value &&
    inferredEffect body.checked.result.events == event.canonical.inferredEffect &&
    body.checked.generic.inferredEffect == event.canonical.generic.inferredEffect) .request
  return body

theorem Checked.allOriginalQmatches {sources owner name} (checked : Checked sources owner name) :
    checked.result.events.filterMap Event.qmatchOffset =
      QuantumSequence.originalOffsets checked.signature.original.occurrence.body := checked.everyQmatch

theorem Checked.allOriginalCalls {sources owner name} (checked : Checked sources owner name) :
    checked.result.events.filterMap Event.callOffset = checked.callOffsets := checked.everyCall

theorem Checked.completeOwnerReturn {sources owner name} (checked : Checked sources owner name) :
    (owners checked.initial).Perm (valueOwners checked.result.value) := checked.returned

theorem Checked.unitaryNoObservation {sources owner name} (checked : Checked sources owner name)
    (annotation : checked.signature.original.parsedHeader.effect = some .unitary)
    (event : Event sources owner) (member : event ∈ checked.result.events) : event.effect ≠ .observe := by
  have pureEffect : inferredEffect checked.result.events = .unitary :=
    SourceEffect.unitary_permits _ (by simpa only [annotation] using checked.asserted)
  have bound := SourceEffect.member_accumulate Event.effect checked.result.events .unitary event member
  change SourceEffect.rank event.effect ≤ SourceEffect.rank (inferredEffect checked.result.events) at bound
  intro observed
  simp [observed,pureEffect,SourceEffect.rank] at bound

theorem PrimitiveEvent.originalTokens {sources caller} (event : PrimitiveEvent sources caller) :
    event.call.call.render = event.tokens := event.call.original

theorem PrimitiveEvent.hRequiresBit {sources caller} (event : PrimitiveEvent sources caller)
    (kind : event.kind = .h) : event.operand.basis = [.bit] := by
  have sourceType := event.sourceType
  simpa [typeMatches,kind] using sourceType

end QleisliKernel.SourceTypes.SourceTrace
