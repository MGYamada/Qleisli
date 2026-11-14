import QleisliKernel.SourceTypes.CallSyntax
import QleisliKernel.SourceTypes.StatementSyntax
import QleisliKernel.SourceTypes.QuantumMatch
import QleisliKernel.SourceTypes.QuantumMoves
import QleisliKernel.SourceTypes.StaticBindings
import QleisliKernel.SourceTypes.SourceBoolean
import QleisliKernel.SourceTypes.SourceControlSyntax
import QleisliKernel.SourceTypes.SourceStaticControlSyntax
import QleisliKernel.SourceTypes.SourceNominalSyntax
import QleisliKernel.SourceTypes.SourceMatchSyntax
import QleisliKernel.SourceTypes.SourceComputedSyntax
import QleisliKernel.SourceTypes.SourceWorkspaceSyntax

/-! A checked decomposition of complete original source tokens. Every child is
bound to an exact checked argument/statement slice. Qmatch retains its existing
complete arm table; computed operands retain their own original child trees and
left-to-right calls. Typed operation rules and all
body/IR preservation obligations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceSyntax
open QleisliKernel.SourceTypes

mutual
inductive Tree : List LocatedToken → Type where
  | empty (tokens : List LocatedToken) (original : tokens = []) : Tree tokens
  | literal (tokens : List LocatedToken) (value : Bool)
      (spelling : tokens.map (·.text) = [if value then "1" else "0"]) : Tree tokens
  | move (tokens : List LocatedToken) (term : QuantumMoves.Term)
      (parsed : QuantumMoves.parse 65 (tokens.map (·.text)) = .ok term) : Tree tokens
  | selection (tokens : List LocatedToken) (parsed : QuantumMatch.Parsed)
      (original : QuantumMatch.parse tokens = .ok (parsed,[])) : Tree tokens
  | selectionExpression (tokens : List LocatedToken) (parsed : QuantumMatch.Parsed)
      (original : QuantumMatch.parse tokens = .ok (parsed,[]))
      (selector : Tree parsed.selector) (target : Tree parsed.target) : Tree tokens
  | group {tokens : List LocatedToken} (parsed : CallSyntax.CheckedGroup tokens)
      (children : Children (parsed.group.arguments.map (·.tokens))) : Tree tokens
  | call {tokens : List LocatedToken} (parsed : CallSyntax.Checked tokens)
      (children : Children (parsed.call.arguments.map (·.tokens))) : Tree tokens
  | binding {tokens : List LocatedToken} (parsed : StatementSyntax.Checked tokens)
      (expression : Tree parsed.statement.expression)
      (rest : Tree parsed.statement.rest) : Tree tokens
  | staticBindings {tokens : List LocatedToken} (leading : StaticBindings.Prefix tokens)
      (nonempty : leading.bindings ≠ []) (rest : Tree leading.suffix) : Tree tokens
  | sequence {tokens : List LocatedToken} (cut : StatementSyntax.Cut ";" tokens)
      (expression : Tree cut.leading) (rest : Tree cut.suffix) : Tree tokens
  | boolean {tokens : List LocatedToken} (written : SourceBoolean.Syntax tokens)
      (children : Children written.parts) : Tree tokens
  | conditional {tokens : List LocatedToken} (written : SourceControlSyntax.CheckedConditional tokens)
      (condition : Tree written.parts.condition) (thenBody : Tree written.parts.thenBody)
      (elseBody : Tree written.parts.elseBody) : Tree tokens
  | staticConditional {tokens : List LocatedToken} (written : SourceStaticControlSyntax.Checked tokens)
      (thenBody : Tree written.parts.thenBody) (elseBody : Tree written.parts.elseBody) : Tree tokens
  | variant {tokens : List LocatedToken} (written : SourceNominalSyntax.Variant tokens) : Tree tokens
  | record {tokens : List LocatedToken} (written : SourceNominalSyntax.Record tokens)
      (children : Children (written.initializers.map (·.expression))) : Tree tokens
  | projection {tokens : List LocatedToken} (written : SourceNominalSyntax.Projection tokens)
      (receiver : Tree written.receiver) : Tree tokens
  | matching {tokens : List LocatedToken} (written : SourceMatchSyntax.Checked tokens)
      (scrutinee : Tree written.parts.scrutinee)
      (children : Children (written.parts.arms.map (·.body.tokens))) : Tree tokens
  | basis {tokens : List LocatedToken} (written : SourceControlSyntax.CheckedBasis tokens)
      (input : Tree written.parts.input) (body : Tree written.parts.body) : Tree tokens
  | computed {tokens : List LocatedToken} (written : SourceComputedSyntax.Checked tokens)
      (input : Tree written.parts.source.tokens) (body : Tree written.parts.body) : Tree tokens
  | workspace {tokens : List LocatedToken} (written : SourceWorkspaceSyntax.Checked tokens)
      (input : Tree written.parts.data.tokens)
      (dirty : Children (written.parts.dirty.toList.map (·.tokens)))
      (body : Tree written.parts.body) : Tree tokens

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
    | .empty .. | .literal .. => return []
    | .move .. => return []
    | .selection .. => return []
    | .selectionExpression _ _ _ selector target =>
      return (← next selector) ++ (← next target)
    | .group _ children =>
      return (← children.trees.mapM (fun child => next child.2)).flatten
    | .call parsed children =>
      return (← children.trees.mapM (fun child => next child.2)).flatten ++ [parsed.calleeOffset]
    | .binding _ expression rest => return (← next expression) ++ (← next rest)
    | .staticBindings _ _ rest => next rest
    | .sequence _ expression rest => return (← next expression) ++ (← next rest)
    | .boolean _ children =>
      return (← children.trees.mapM (fun child => next child.2)).flatten
    | .conditional _ condition thenBody elseBody =>
      return (← next condition) ++ (← next thenBody) ++ (← next elseBody)
    | .staticConditional _ thenBody elseBody => return (← next thenBody) ++ (← next elseBody)
    | .variant _ => return []
    | .record _ children => return (← children.trees.mapM (fun child => next child.2)).flatten
    | .projection _ receiver => next receiver
    | .matching _ scrutinee children =>
      return (← next scrutinee) ++ (← children.trees.mapM (fun child => next child.2)).flatten
    | .basis _ input body => return (← next input) ++ (← next body)
    | .computed _ input body => return (← next input) ++ (← next body)
    | .workspace _ input dirty body =>
      return (← next input) ++ (← dirty.trees.mapM (fun child => next child.2)).flatten ++ (← next body))

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
    if original : tokens = [] then return .empty tokens original
    if spelling : tokens.map (·.text) = ["0"] then return .literal tokens false spelling
    if spelling : tokens.map (·.text) = ["1"] then return .literal tokens true spelling
    if tokens.head?.map (·.text) == some "static" then
      if !body then throw "static let requires the enclosing original function body"
      let leading ← StaticBindings.readPrefix tokens
      if nonempty : leading.bindings ≠ [] then
        let rest ← next depth true leading.suffix
        return .staticBindings leading nonempty rest
      else throw "static leading has no binding"
    if tokens.head?.map (·.text) == some "let" then
      if !body then throw "let requires the enclosing original function body"
      let statement ← StatementSyntax.readPrepared statements tokens
      let expression ← next (depth+1) false statement.statement.expression
      let rest ← next depth true statement.statement.rest
      return .binding statement expression rest
    if body then
      match StatementSyntax.cutPrepared statements ";" tokens with
      | .ok cut =>
        let expression ← next (depth+1) false cut.leading
        let rest ← next depth true cut.suffix
        return .sequence cut expression rest
      | .error _ => pure ()
    if tokens.head?.map (·.text) == some "if" then
      if (tokens[1]?.map (·.text)) == some "static" then
        let written ← SourceStaticControlSyntax.read tokens
        let thenBody ← next (depth+1) true written.parts.thenBody
        let elseBody ← next (depth+1) true written.parts.elseBody
        return .staticConditional written thenBody elseBody
      let written ← SourceControlSyntax.readConditional tokens
      let condition ← next (depth+1) false written.parts.condition
      let thenBody ← next (depth+1) true written.parts.thenBody
      let elseBody ← next (depth+1) true written.parts.elseBody
      return .conditional written condition thenBody elseBody
    if tokens.head?.map (·.text) == some "match" then
      let written ← SourceMatchSyntax.read tokens
      let scrutinee ← next (depth+1) false written.parts.scrutinee
      let children ← readChildren (next (depth+1) true) (written.parts.arms.map (·.body.tokens))
      return .matching written scrutinee children
    if tokens.head?.map (·.text) == some "basis" then
      let written ← SourceControlSyntax.readBasis tokens
      let input ← next (depth+1) false written.parts.input
      let body ← next (depth+1) true written.parts.body
      return .basis written input body
    if tokens.head?.map (·.text) == some "with_computed" then
      let written ← SourceComputedSyntax.read tokens
      let input ← next (depth+1) false written.parts.source.tokens
      let body ← next (depth+1) true written.parts.body
      return .computed written input body
    if (tokens.head?.map (·.text)).any (fun name => name == "clean" || name == "dirty") &&
        tokens.getLast?.map (·.text) == some "}" && tokens[1]?.map (·.text) == some "(" then
      let written ← SourceWorkspaceSyntax.read tokens
      let input ← next (depth+1) false written.parts.data.tokens
      let dirty ← readChildren (next (depth+1) false) (written.parts.dirty.toList.map (·.tokens))
      let body ← next (depth+1) true written.parts.body
      return .workspace written input dirty body
    if let some written := SourceBoolean.read tokens then
      let children ← readChildren (next (depth+1) false) written.parts
      return .boolean written children
    if tokens.head?.map (·.text) == some "qmatch" || tokens.head?.map (·.text) == some "qif" then
      match original : QuantumMatch.parse tokens with
      | .ok (parsed,[]) =>
        if (QuantumMoves.parse 65 (parsed.selector.map (·.text))).isOk &&
            (QuantumMoves.parse 65 (parsed.target.map (·.text))).isOk then
          return .selection tokens parsed original
        let selector ← next (depth+1) false parsed.selector
        let target ← next (depth+1) false parsed.target
        return .selectionExpression tokens parsed original selector target
      | _ => throw "qmatch does not consume the complete original expression"
    if (tokens[tokens.length-2]?.map (·.text)) == some "." then
      let written ← SourceNominalSyntax.readProjection tokens
      return .projection written (← next (depth+1) false written.receiver)
    if tokens.getLast?.map (·.text) == some "}" then
      let written ← SourceNominalSyntax.readRecord tokens
      let children ← readChildren (next (depth+1) false) (written.initializers.map (·.expression))
      return .record written children
    if (tokens[tokens.length-2]?.map (·.text)) == some "::" then
      return .variant (← SourceNominalSyntax.readVariant tokens)
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
