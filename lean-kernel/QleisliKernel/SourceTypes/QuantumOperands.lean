import QleisliKernel.SourceTypes.QuantumMoves
import QleisliKernel.SourceTypes.QuantumMatch

/-! Original structural operand binding at an actual qmatch occurrence. Fresh
source parameters seed distinct logical identities even at zero physical width.
General expression rules and source-to-Raw port mapping remain separate duties.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumOperands
open Semantics.SourceOwners Semantics.FiniteCarrier Finite

/-- Recover patterns from the exact original header and compare every complete
type clause with the shared header reader. No supplied parameter-name table is
accepted, and no second type grammar supplies signature metadata. -/
def parameterPatterns {sources owner name} (original : OrdinarySignature.Original sources owner name) :
    Except String (List (List String)) := do
  let suffix := original.occurrence.header.dropWhile (· != original.occurrence.nameToken)
  let nameToken :: opener :: tail := suffix | throw "missing original parameter clause"
  if nameToken != original.occurrence.nameToken || opener.text != "(" then throw "parameter occurrence mismatch"
  let result := original.parsedHeader.resultTokens
  if tail.length < result.length+3 then throw "incomplete original parameter envelope"
  let raw := tail.take (tail.length-result.length-3)
  let ending := tail.drop raw.length
  if ending.map (·.text) != [")","-",">"] ++ result.map (·.text) then throw "original parameter boundary mismatch"
  let clauses ← splitMembers (raw.map (·.text))
  let pairs ← clauses.mapM fun clause => do
    let pattern := clause.takeWhile (· != ":")
    let ":" :: ty := clause.drop pattern.length | throw "missing original parameter type"
    if pattern.isEmpty || ty.isEmpty then throw "empty original parameter pattern/type"
    return (pattern,ty)
  if pairs.map Prod.snd != original.parsedHeader.parameterTypes then throw "original type clause mismatch"
  return pairs.map Prod.fst

def seed {sources owner name} (signature : QuantumSignature.Checked sources owner name)
    (patterns : List (List String)) : Except String Environment := do
  if patterns.length != signature.parameterReads.length then throw "source parameter pattern count mismatch"
  ((patterns.zip signature.parameterReads).zipIdx).foldlM (fun environment (pair,index) =>
    QuantumMoves.bind pair.1 [.owner ⟨index,pair.2.basis⟩] environment) []

structure Checked {sources owner name offset} (site : QuantumMatch.Site sources owner name offset)
    (selectorBasis targetBasis : Basis) where
  signature : QuantumSignature.Checked sources owner name
  original : signature.original.source = site.original.source ∧ signature.original.declaration = site.original.declaration
  patterns : List (List String)
  parameters : parameterPatterns signature.original = .ok patterns
  initial : Environment
  seeded : seed signature patterns = .ok initial
  frame : Environment
  traversed : QuantumMoves.replay 129 initial (site.leading.map (·.text)) = .ok frame
  conserved : Conserved initial frame
  selector : Owner
  afterSelector : Environment
  selected : QuantumMoves.eval (site.parsed.selector.map (·.text)) frame = .ok ([.owner selector],afterSelector)
  target : Owner
  afterTarget : Environment
  targeted : QuantumMoves.eval (site.parsed.target.map (·.text)) afterSelector = .ok ([.owner target],afterTarget)
  completeFrame : (owners frame).Perm ([selector,target] ++ owners afterTarget)
  different : selector.ordinal ≠ target.ordinal
  selectorType : selector.basis = selectorBasis
  targetType : target.basis = targetBasis

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

/-- This structural component never skips an unknown preceding expression.
Its source, type, owner and complete-frame facts are retained for composition;
it does not by itself authorize native dispatch or general source execution. -/
def read {sources owner name offset} (site : QuantumMatch.Site sources owner name offset)
    (selectorBasis targetBasis : Basis) : WorkM (Checked site selectorBasis targetBasis) := do
  let signature ← QuantumSignature.read sources owner name
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  let count := site.original.occurrence.header.length+site.leading.length+
    site.parsed.selector.length+site.parsed.target.length
  exactWork (Exact.charge (64*(count+1)^2+256*(count+1)+8*(bytes+1)*(signature.parameterReads.length+1)^2))
  if original : signature.original.source = site.original.source ∧
      signature.original.declaration = site.original.declaration then
    match parameters : parameterPatterns signature.original with
    | .error _ => throw .request
    | .ok patterns =>
      match seeded : seed signature patterns with
      | .error _ => throw .request
      | .ok initial =>
        match traversed : QuantumMoves.replay 129 initial (site.leading.map (·.text)) with
        | .error _ => throw .request
        | .ok frame =>
          if conserved : (owners initial).Perm (owners frame) then
            match selected : QuantumMoves.eval (site.parsed.selector.map (·.text)) frame with
            | .ok ([.owner selector],afterSelector) =>
              match targeted : QuantumMoves.eval (site.parsed.target.map (·.text)) afterSelector with
              | .ok ([.owner target],afterTarget) =>
                if complete : (owners frame).Perm ([selector,target] ++ owners afterTarget) then
                  if different : selector.ordinal ≠ target.ordinal then
                    if selectorType : selector.basis = selectorBasis then
                      if targetType : target.basis = targetBasis then
                        return ⟨signature,original,patterns,parameters,initial,seeded,frame,traversed,conserved,
                          selector,afterSelector,selected,target,afterTarget,targeted,complete,different,selectorType,targetType⟩
                      else throw .request
                    else throw .request
                  else throw .request
                else throw .request
              | _ => throw .request
            | _ => throw .request
          else throw .request
  else throw .request


theorem Checked.ownerPartition {sources owner name offset selectorBasis targetBasis}
    {site : QuantumMatch.Site sources owner name offset}
    (checked : Checked site selectorBasis targetBasis) :
    (owners checked.initial).Perm ([checked.selector,checked.target] ++ owners checked.afterTarget) :=
  checked.conserved.trans checked.completeFrame

end QleisliKernel.SourceTypes.QuantumOperands
