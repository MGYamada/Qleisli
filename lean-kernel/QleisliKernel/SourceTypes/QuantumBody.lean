import QleisliKernel.SourceTypes.QuantumOperands

/-! Complete structural return flow around an original qmatch occurrence.
This stage retains returned owner order, including zero-width owners. It does
not bind that order to Raw outputs or prove arm/body lowering, and grants no
native dispatch, execution handle, source effect label or control capability.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumBody
open Semantics.SourceOwners Semantics.FiniteCarrier Finite

/-- Split only complete structural statements from the final expression.
Unknown expressions are subsequently refused by the existing structural reader;
this scan never skips a statement or manufactures an owner expression. -/
def lastStatement (tokens : List String) : List String × List String :=
  let start := (tokens.foldl (fun (index,start) token =>
    (index+1,if token == ";" then index+1 else start)) (0,0)).2
  (tokens.take start,tokens.drop start)

def pendingBinding (leading : List String) : Except String (Option (List String)) := do
  let (_,pending) := lastStatement leading
  if pending.isEmpty then return none
  let "let" :: rest := pending | throw "qmatch is not the focused result of a structural body"
  if rest.getLast? != some "=" then throw "incomplete qmatch result binding"
  let pattern := rest.dropLast
  let _ ← QuantumMoves.parse 65 pattern
  return some pattern

structure Outcome where
  value : Value
  remaining : Environment

/-- Evaluate the actual complete suffix, rather than treating the focused
qmatch as the function's result. Calls and observations need their separate
checked rules; no unknown suffix is silently accepted. -/
def finish (pattern : Option (List String)) (selector target : Owner)
    (afterOperands : Environment) (suffix : List String) : Except String Outcome := do
  let returned := [.tuple 2,.owner selector,.owner target]
  match pattern with
  | none =>
    if !suffix.isEmpty then throw "tokens remain after the focused qmatch result"
    return ⟨returned,afterOperands⟩
  | some pattern =>
    let ";" :: tail := suffix | throw "missing qmatch binding terminator"
    let environment ← QuantumMoves.bind pattern returned afterOperands
    let (statements,result) := lastStatement tail
    if result.isEmpty then throw "missing original function result"
    let frame ← QuantumMoves.replay 129 environment statements
    let (value,remaining) ← QuantumMoves.eval result frame
    return ⟨value,remaining⟩

/-- QuantumSignature's result grammar distinguishes an atomic Q owner from
the ordinary tuple collecting separate Q owners. No width or flattened owner
count erases that distinction. -/
def resultShape (parts : QuantumSignature.ResultParts) (value : Value) : Bool :=
  match parts,value with
  | .owner _,[.owner _] => true
  | .tuple clauses,.tuple arity :: fields =>
    arity == clauses.length && fields.length == arity &&
      fields.all (fun atom => match atom with | .owner _ => true | _ => false)
  | _,_ => false

structure Checked {sources owner name offset selectorBasis targetBasis}
    {site : QuantumMatch.Site sources owner name offset}
    (operands : QuantumOperands.Checked site selectorBasis targetBasis) where
  pattern : Option (List String)
  pending : pendingBinding (site.leading.map (·.text)) = .ok pattern
  outcome : Outcome
  finished : finish pattern operands.selector operands.target operands.afterTarget
    (site.suffix.map (·.text)) = .ok outcome
  complete : owners outcome.remaining = []
  ownerReturn : (owners operands.initial).Perm (valueOwners outcome.value)
  shape : resultShape operands.signature.parts outcome.value = true
  resultTypes : (valueOwners outcome.value).map (·.basis) = operands.signature.outputs

/-- Exact ordered source owner identities for later source-to-Raw composition.
This list is a derived source fact, not a proposed Raw mapping or a receipt. -/
def Checked.returnOrder {sources owner name offset selectorBasis targetBasis}
    {site : QuantumMatch.Site sources owner name offset}
    {operands : QuantumOperands.Checked site selectorBasis targetBasis}
    (checked : Checked operands) : List Nat :=
  (valueOwners checked.outcome.value).map (·.ordinal)

def read {sources owner name offset selectorBasis targetBasis}
    {site : QuantumMatch.Site sources owner name offset}
    (operands : QuantumOperands.Checked site selectorBasis targetBasis) : WorkM (Checked operands) := do
  let count := site.leading.length+site.suffix.length+1
  let bytes := site.original.source.utf8ByteSize
  let ownerCount := (owners operands.initial).length
  exactWork (Exact.charge (64*count^2+8*(bytes+1)*(ownerCount+1)^2))
  match pending : pendingBinding (site.leading.map (·.text)) with
  | .error _ => throw .request
  | .ok pattern =>
    match finished : finish pattern operands.selector operands.target operands.afterTarget
        (site.suffix.map (·.text)) with
    | .error _ => throw .request
    | .ok outcome =>
      if complete : owners outcome.remaining = [] then
        if returned : (owners operands.initial).Perm (valueOwners outcome.value) then
          if shape : resultShape operands.signature.parts outcome.value = true then
            if types : (valueOwners outcome.value).map (·.basis) = operands.signature.outputs then
              return ⟨pattern,pending,outcome,finished,complete,returned,shape,types⟩
            else throw .request
          else throw .request
        else throw .request
      else throw .request

theorem Checked.sourceOwnerReturn {sources owner name offset selectorBasis targetBasis}
    {site : QuantumMatch.Site sources owner name offset}
    {operands : QuantumOperands.Checked site selectorBasis targetBasis}
    (checked : Checked operands) :
    (owners operands.initial).Perm (valueOwners checked.outcome.value) := checked.ownerReturn

theorem Checked.originalBody {sources owner name offset selectorBasis targetBasis}
    {site : QuantumMatch.Site sources owner name offset}
    {operands : QuantumOperands.Checked site selectorBasis targetBasis}
    (_checked : Checked operands) :
    site.original.occurrence.body = site.leading ++ site.parsed.tokens ++ site.suffix := site.originalBody

end QleisliKernel.SourceTypes.QuantumBody
