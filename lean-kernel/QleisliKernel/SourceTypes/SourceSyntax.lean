import QleisliKernel.SourceTypes.CallSyntax
import QleisliKernel.SourceTypes.StatementSyntax
import QleisliKernel.SourceTypes.QuantumSequence

/-! A checked decomposition of complete original source tokens. Every child is
bound to an exact checked argument/statement slice. Qmatch retains its existing
complete arm table; its operands still require the existing structural rule,
so calls inside qmatch operands refuse during evaluation. Typed operation rules and all
body/IR preservation obligations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceSyntax
open QleisliKernel.SourceTypes

mutual
inductive Tree : List LocatedToken → Type where
  | move (tokens : List LocatedToken) (term : QuantumMoves.Term)
      (parsed : QuantumMoves.parse 65 (tokens.map (·.text)) = .ok term) : Tree tokens
  | selection (tokens : List LocatedToken) (parsed : QuantumMatch.Parsed)
      (original : QuantumMatch.parse tokens = .ok (parsed,[])) : Tree tokens
  | group {tokens : List LocatedToken} (parsed : CallSyntax.CheckedGroup tokens)
      (children : Children (parsed.group.arguments.map (·.tokens))) : Tree tokens
  | call {tokens : List LocatedToken} (parsed : CallSyntax.Checked tokens)
      (children : Children (parsed.call.arguments.map (·.tokens))) : Tree tokens
  | binding {tokens : List LocatedToken} (parsed : StatementSyntax.Checked tokens)
      (expression : Tree parsed.statement.expression)
      (rest : Tree parsed.statement.rest) : Tree tokens

inductive Children : List (List LocatedToken) → Type where
  | nil : Children []
  | cons {first rest} (tree : Tree first) (children : Children rest) : Children (first :: rest)
end

private def readChildren (readOne : (tokens : List LocatedToken) → Except String (Tree tokens)) :
    (parts : List (List LocatedToken)) → Except String (Children parts) := fun parts => do
  let trees ← parts.mapM fun tokens => do
    let tree ← readOne tokens
    return (⟨tokens,tree⟩ : Sigma Tree)
  let packed : Sigma Children := trees.foldr (fun tree rest =>
    ⟨tree.1 :: rest.1,.cons tree.2 rest.2⟩) ⟨[],.nil⟩
  if original : packed.1 = parts then return original ▸ packed.2
  else throw "child syntax does not retain its complete original token slices"

private def childTrees : Nat → {parts : List (List LocatedToken)} →
    Children parts → List (Sigma Tree) :=
  Nat.rec (fun {_} _ => []) (fun _ next {_} children => match children with
    | .nil => []
    | @Children.cons first _ tree rest => ⟨first,tree⟩ :: next rest)

/-- The index contains exactly one part per child, so it supplies a structural
traversal bound without another source-language capacity. -/
def Children.trees {parts} (children : Children parts) : List (Sigma Tree) :=
  childTrees (parts.length+1) children

private def callsWithFuel : Nat → {tokens : List LocatedToken} → Tree tokens → Except String (List Nat) :=
  Nat.rec (fun {_} _ => throw "original call traversal exhausted") (fun _ next {_} tree => do
    match tree with
    | .move .. => return []
    | .selection .. => return []
    | .group _ children =>
      return (← children.trees.mapM (fun child => next child.2)).flatten
    | .call parsed children =>
      return (← children.trees.mapM (fun child => next child.2)).flatten ++ [parsed.calleeOffset]
    | .binding _ expression rest => return (← next expression) ++ (← next rest))

/-- Operation order is argument postorder, not source-byte sorting. Exhaustion
refuses instead of silently truncating the coverage list. The bound comes from
the original token count, not a fixed expression or call limit. -/
def Tree.calls {tokens} (tree : Tree tokens) : Except String (List Nat) :=
  callsWithFuel (tokens.length+1) tree

/-- Token-derived fuel bounds complete traversal; depth bounds nested expressions.
The number of statements or operation nodes has no new 128-element cap. -/
private def readWithStatements {tokenFuel : Nat} (statements : StatementSyntax.Prepared tokenFuel) :
    Nat → Nat → Bool → (tokens : List LocatedToken) → Except String (Tree tokens) :=
  Nat.rec (fun _ _ _ => throw "source syntax traversal fuel") (fun _ next depth body tokens => do
    if depth ≥ 65 then throw "source expression nesting capacity"
    if tokens.head?.map (·.text) == some "let" then
      if !body then throw "let requires the enclosing original function body"
      let statement ← StatementSyntax.readPrepared statements tokens
      let expression ← next (depth+1) false statement.statement.expression
      let rest ← next depth true statement.statement.rest
      return .binding statement expression rest
    if tokens.head?.map (·.text) == some "qmatch" then
      match original : QuantumMatch.parse tokens with
      | .ok (parsed,[]) => return .selection tokens parsed original
      | _ => throw "qmatch does not consume the complete original expression"
    if tokens.head?.map (·.text) == some "(" then
      let group ← CallSyntax.readGroup tokens
      let children ← readChildren (next (depth+1) false) (group.group.arguments.map (·.tokens))
      return .group group children
    if tokens.length == 1 then
      match parsed : QuantumMoves.parse 65 (tokens.map (·.text)) with
      | .ok term => return .move tokens term parsed
      | .error error => throw error
    let call ← CallSyntax.read tokens
    let children ← readChildren (next (depth+1) false) (call.call.arguments.map (·.tokens))
    return .call call children)

/-- Measure the original token list once. AST traversal fuel and expression
depth retain their existing roles; each let shares the original scan bound. -/
def read (fuel depth : Nat) (body : Bool) (tokens : List LocatedToken) : Except String (Tree tokens) :=
  readWithStatements (StatementSyntax.prepare (tokens.length+1)) fuel depth body tokens

end QleisliKernel.SourceTypes.SourceSyntax
