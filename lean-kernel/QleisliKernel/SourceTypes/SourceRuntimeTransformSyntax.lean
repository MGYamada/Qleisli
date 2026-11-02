import QleisliKernel.SourceTypes.StaticApplication

/-! Original direct-runtime transform syntax. Complete runtime groups stay
distinct from opaque/static unary Op providers; only named/specialized ordinary
functions and transparent power wrappers belong to this source rule.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeTransformSyntax

inductive Access where
  | forward | adjoint | controlled
  deriving BEq, DecidableEq, Repr

inductive Leaf : List LocatedToken → Type where
  | named {tokens} (written : StaticApplication.Syntax tokens) : Leaf tokens
  | power {tokens} (call : CallSyntax.Checked tokens) (child count : CallSyntax.Argument)
      (name : call.call.callee.map (·.text) = ["power"])
      (arguments : call.call.arguments = [child,count]) (inner : Leaf child.tokens) : Leaf tokens

def Leaf.base {tokens} : Leaf tokens → Sigma StaticApplication.Syntax
  | .named written => ⟨_,written⟩
  | .power _ _ _ _ _ inner => inner.base

def Leaf.counts {tokens} : Leaf tokens → List CallSyntax.Argument
  | .named _ => []
  | .power _ _ count _ _ inner => inner.counts ++ [count]

private def readLeaf : Nat → (tokens : List LocatedToken) → Except String (Leaf tokens) :=
  Nat.rec (fun _ => throw "runtime transform source depth") (fun _ recurse tokens => do
    if tokens.getLast?.map (·.text) == some ")" then
      let call ← CallSyntax.read tokens
      if name : call.call.callee.map (·.text) = ["power"] then
        match arguments : call.call.arguments with
        | [child,count] => return .power call child count name arguments (← recurse child.tokens)
        | _ => throw "runtime transparent power arity"
      else throw "runtime transform child is not a named provider or transparent power"
    else return .named (← StaticApplication.readSyntax tokens))

inductive Checked (tokens : List LocatedToken) where
  | power (call : CallSyntax.Checked tokens) (name : call.call.callee.map (·.text) = ["power"])
      (leaf : Leaf tokens)
  | adjoint (call : CallSyntax.Checked tokens) (child : CallSyntax.Argument)
      (name : call.call.callee.map (·.text) = ["adjoint"])
      (arguments : call.call.arguments = [child]) (leaf : Leaf child.tokens)
  | controlled (call : CallSyntax.Checked tokens) (child : CallSyntax.Argument)
      (name : call.call.callee.map (·.text) = ["controlled"])
      (arguments : call.call.arguments = [child]) (leaf : Leaf child.tokens)

def Checked.access {tokens} : Checked tokens → Access
  | .power .. => .forward | .adjoint .. => .adjoint | .controlled .. => .controlled

def Checked.base {tokens} : Checked tokens → Sigma StaticApplication.Syntax
  | .power _ _ leaf => leaf.base
  | .adjoint _ _ _ _ leaf | .controlled _ _ _ _ leaf => leaf.base

def Checked.counts {tokens} : Checked tokens → List CallSyntax.Argument
  | .power _ _ leaf => leaf.counts
  | .adjoint _ _ _ _ leaf | .controlled _ _ _ _ leaf => leaf.counts

/-- This syntax classification precedes any execution/native decision. A
non-runtime constructor remains subject to its separate static Op rule. -/
def read (tokens : List LocatedToken) : Except String (Option (Checked tokens)) := do
  if tokens.getLast?.map (·.text) != some ")" then return none
  let call ← CallSyntax.read tokens
  if name : call.call.callee.map (·.text) = ["power"] then
    match readLeaf 65 tokens with
    | .ok leaf => return some (.power call name leaf)
    | .error _ => return none
  if name : call.call.callee.map (·.text) = ["adjoint"] then
    match arguments : call.call.arguments with
    | [child] => match readLeaf 65 child.tokens with
      | .ok leaf => return some (.adjoint call child name arguments leaf)
      | .error _ => return none
    | _ => return none
  if name : call.call.callee.map (·.text) = ["controlled"] then
    match arguments : call.call.arguments with
    | [child] => match readLeaf 65 child.tokens with
      | .ok leaf => return some (.controlled call child name arguments leaf)
      | .error _ => return none
    | _ => return none
  return none

end QleisliKernel.SourceTypes.SourceRuntimeTransformSyntax
