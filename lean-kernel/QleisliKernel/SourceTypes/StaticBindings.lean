import QleisliKernel.SourceTypes.StatementSyntax
import QleisliKernel.SourceTypes.NaturalSyntax

/-! Exact original-token static-let prefixes. Initializers remain original Nat
syntax; lexical resolution, arithmetic and complete body checking are separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticBindings
open QleisliKernel.SourceTypes QleisliKernel.Semantics.SourceNatural

structure Natural (tokens : List LocatedToken) where
  expression : Expr
  parsed : NaturalSyntax.read (tokens.map (·.text)) = .ok expression

def natural (tokens : List LocatedToken) : Except String (Natural tokens) :=
  match parsed : NaturalSyntax.read (tokens.map (·.text)) with
  | .error error => throw error
  | .ok expression => return ⟨expression,parsed⟩

structure Binding where
  keyword : LocatedToken
  statement : StatementSyntax.Let
  name : LocatedToken
  keywordText : keyword.text = "static"
  letText : statement.keyword.text = "let"
  assignment : statement.assignment.text = "="
  terminator : statement.terminator.text = ";"
  pattern : statement.pattern = [name]
  natural : Natural statement.expression

def Binding.render (binding : Binding) : List LocatedToken :=
  [binding.keyword,binding.statement.keyword] ++ binding.statement.pattern ++
    [binding.statement.assignment] ++ binding.statement.expression ++ [binding.statement.terminator]

private def prefixLoop {fuel : Nat} (scanner : StatementSyntax.Prepared fuel) :
    Nat → List LocatedToken → List Binding → Except String (List Binding × List LocatedToken) :=
  Nat.rec (fun _ _ => throw "static prefix traversal capacity")
    (fun _ next tokens previous => do
      match tokens with
      | [] => return (previous.reverse,[])
      | first :: tail =>
        if keyword : first.text = "static" then
          let statement ← StatementSyntax.readPrepared scanner tail
          match pattern : statement.statement.pattern with
          | [name] =>
            if !identifier name.text then throw "invalid static binding name"
            let expression ← natural statement.statement.expression
            let binding : Binding := ⟨first,statement.statement,name,keyword,
              statement.keyword,statement.assignment,statement.terminator,pattern,expression⟩
            next statement.statement.rest (binding :: previous)
          | _ => throw "static let requires one original identifier"
        else return (previous.reverse,tokens))

structure Prefix (tokens : List LocatedToken) where
  bindings : List Binding
  suffix : List LocatedToken
  restored : bindings.flatMap Binding.render ++ suffix = tokens

def readPrefix (tokens : List LocatedToken) : Except String (Prefix tokens) := do
  let (bindings,suffix) ← prefixLoop (StatementSyntax.prepare (tokens.length+1))
    (tokens.length+1) tokens []
  if restored : bindings.flatMap Binding.render ++ suffix = tokens then
    return ⟨bindings,suffix,restored⟩
  else throw "static prefix original-token mismatch"

end QleisliKernel.SourceTypes.StaticBindings
