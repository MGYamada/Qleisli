import QleisliKernel.SourceTypes.QuantumBody

/-! Read every original qmatch in a complete structural source body. The
source rule transfers the two distinct owners and retains the complete frame;
it does not check arm implementations, Raw intervals or grant a capability.
Unknown expressions require their own rules and are never skipped. No source
text, binding table or alternate function is synthesized by this reader.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumSequence
open Semantics.SourceOwners Semantics.FiniteCarrier Finite

/-- Static arm positions share the original lexical namespace. A consumed
runtime binding still blocks an unqualified function name; qualification keeps
the existing module selection and visibility checks in QuantumArms. -/
def armsUnshadowed (scope : List String) (arms : List QuantumMatch.Arm) : Bool :=
  arms.all fun arm => match arm.operation with
    | [name] => !scope.contains name.text
    | _ => true

private def boundNames (pattern : List LocatedToken) : Except String (List String) := do
  let term ← QuantumMoves.parse 65 (pattern.map (·.text))
  return term.filterMap fun atom => match atom with | .name name => some name | _ => none

structure Event where
  parsed : QuantumMatch.Parsed
  scope : List String
  unshadowed : armsUnshadowed scope parsed.arms = true
  before : Environment
  selector : Owner
  target : Owner
  remaining : Environment
  distinct : selector.ordinal ≠ target.ordinal
  partition : (owners before).Perm ([selector,target] ++ owners remaining)
  deriving DecidableEq, Repr

instance : BEq Event where
  beq first second := decide (first = second)

structure Outcome where
  value : Value
  remaining : Environment
  events : List Event
  deriving BEq, DecidableEq, Repr

/-- A source selection returns both actual operands in their fixed order.
The arm table remains intact for the enclosing independent arm/sector gate. -/
def expression (tokens : List LocatedToken) (environment : Environment)
    (scope : List String := environment.map (·.name)) : Except String Outcome := do
  if tokens.head?.map (·.text) == some "qmatch" then
    let (parsed,suffix) ← QuantumMatch.parse tokens
    if !suffix.isEmpty then throw "tokens remain after the original qmatch expression"
    if unshadowed : armsUnshadowed scope parsed.arms = true then
      let ([.owner selector],afterSelector) ← QuantumMoves.eval (parsed.selector.map (·.text)) environment
        | throw "qmatch selector is not one original owner"
      let ([.owner target],remaining) ← QuantumMoves.eval (parsed.target.map (·.text)) afterSelector
        | throw "qmatch target is not one original owner"
      if distinct : selector.ordinal ≠ target.ordinal then
        if partition : (owners environment).Perm ([selector,target] ++ owners remaining) then
          return ⟨[.tuple 2,.owner selector,.owner target],remaining,
            [⟨parsed,scope,unshadowed,environment,selector,target,remaining,distinct,partition⟩]⟩
        else throw "qmatch changes the complete source owner frame"
      else throw "qmatch aliases its source operands"
    else throw "qmatch arm is shadowed by an original local binding"
  else
    let (value,remaining) ← QuantumMoves.eval (tokens.map (·.text)) environment
    return ⟨value,remaining,[]⟩

/-- Traverse complete lets and the final expression, retaining source order.
Semicolons inside a supported qmatch are invalid arm syntax; unknown nested
expressions are refused by expression, never treated as an opaque move. -/
def replayWithScope : Nat → List String → Environment → List LocatedToken → Except String Outcome :=
  Nat.rec (fun _ _ _ => throw "source sequence capacity") (fun _ next scope environment tokens => do
    match tokens with
    | first :: rest =>
      if first.text == "let" then
        let pattern := rest.takeWhile (·.text != "=")
        let assignment :: tail := rest.drop pattern.length | throw "missing source let assignment"
        if assignment.text != "=" then throw "invalid source let assignment"
        let term := tail.takeWhile (·.text != ";")
        let terminator :: remaining := tail.drop term.length | throw "missing complete source let"
        if terminator.text != ";" then throw "invalid source let terminator"
        let value ← expression term environment scope
        let after ← QuantumMoves.bind (pattern.map (·.text)) value.value value.remaining
        if !(owners environment).Perm (owners after) then throw "source let changes the owner frame"
        let names ← boundNames pattern
        let result ← next (names ++ scope) after remaining
        let events := value.events ++ result.events
        if events.length > 128 then throw "source sequence capacity"
        return ⟨result.value,result.remaining,events⟩
      else expression tokens environment scope
    | [] => throw "missing original function result")

/-- Only complete original parameter seeding supplies this initial scope.
Internal replay retains every completed binder after its value is consumed. -/
def replay (fuel : Nat) (environment : Environment) (tokens : List LocatedToken) : Except String Outcome :=
  replayWithScope fuel (environment.map (·.name)) environment tokens

def originalOffsets (tokens : List LocatedToken) : List Nat :=
  (tokens.filter (·.text == "qmatch")).map (·.span.startByte)

structure Checked (sources : Sources) (owner name : String) where
  signature : QuantumSignature.Checked sources owner name
  patterns : List (List String)
  parameters : QuantumOperands.parameterPatterns signature.original = .ok patterns
  initial : Environment
  seeded : QuantumOperands.seed signature patterns = .ok initial
  outcome : Outcome
  traversed : replay 129 initial signature.original.occurrence.body = .ok outcome
  complete : owners outcome.remaining = []
  returned : (owners initial).Perm (valueOwners outcome.value)
  shape : QuantumBody.resultShape signature.parts outcome.value = true
  resultTypes : (valueOwners outcome.value).map (·.basis) = signature.outputs
  everyOccurrence : outcome.events.map (·.parsed.keyword.span.startByte) =
    originalOffsets signature.original.occurrence.body
  uniqueOccurrences : (originalOffsets signature.original.occurrence.body).Nodup

/-- Resolve the original signature and parameter patterns before replay.
The equality with every original keyword is checked independently of the
proposed event list; duplicate, missing and reordered occurrences cannot pass. -/
def read (sources : Sources) (owner name : String) : WorkM (Checked sources owner name) := do
  let signature ← QuantumSignature.read sources owner name
  let tokens := signature.original.occurrence.body
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  let steps := (tokens.filter fun token => token.text == "let" || token.text == "qmatch").length+1
  let arity := signature.inputs.length+1
  -- Scan complete arm tokens linearly; charge the full nominal identities at
  -- each actual environment transition, rather than squaring arm-table size.
  exactWork (Exact.charge (128*(tokens.length+1)*(arity+1)+16*(bytes+1)*arity^2*steps))
  match parameters : QuantumOperands.parameterPatterns signature.original with
  | .error _ => throw .request
  | .ok patterns =>
    match seeded : QuantumOperands.seed signature patterns with
    | .error _ => throw .request
    | .ok initial =>
      match traversed : replay 129 initial tokens with
      | .error _ => throw .request
      | .ok outcome =>
        if complete : owners outcome.remaining = [] then
          if returned : (owners initial).Perm (valueOwners outcome.value) then
            if shape : QuantumBody.resultShape signature.parts outcome.value = true then
              if types : (valueOwners outcome.value).map (·.basis) = signature.outputs then
                if every : outcome.events.map (·.parsed.keyword.span.startByte) = originalOffsets tokens then
                  if unique : (originalOffsets tokens).Nodup then
                    return ⟨signature,patterns,parameters,initial,seeded,outcome,traversed,
                      complete,returned,shape,types,every,unique⟩
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
          else throw .request
        else throw .request

theorem Checked.allOriginalOccurrences {sources owner name} (checked : Checked sources owner name) :
    checked.outcome.events.map (·.parsed.keyword.span.startByte) =
      originalOffsets checked.signature.original.occurrence.body := checked.everyOccurrence

theorem Checked.completeOwnerReturn {sources owner name} (checked : Checked sources owner name) :
    (owners checked.initial).Perm (valueOwners checked.outcome.value) := checked.returned

end QleisliKernel.SourceTypes.QuantumSequence
