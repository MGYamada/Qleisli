import QleisliKernel.SourceTypes.Lexer

/-! Complete original-token statement segmentation. Delimiters inside
nested calls, static arguments and branch bodies cannot terminate the enclosing
let. This is segmentation, not expression/pattern validation, source semantics
or permission to skip unknown constructs. The enclosing consumer must charge
work and evaluate every retained expression under its own checked rule.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StatementSyntax
open QleisliKernel.SourceTypes

private def closing (text : String) : Option String :=
  if text == "(" then some ")" else if text == "[" then some "]"
  else if text == "{" then some "}" else none

private def advance (stack : List String) (token : LocatedToken) : Except String (List String) := do
  if let some expected := closing token.text then
    if stack.length ≥ 64 then throw "source statement nesting capacity"
    return expected :: stack
  if [")","]","}"].contains token.text then
    let expected :: stack := stack | throw "unmatched source statement delimiter"
    if token.text != expected then throw "mismatched source statement delimiter"
    return stack
  return stack

private structure Prefix where
  leading : List LocatedToken
  delimiter : LocatedToken
  suffix : List LocatedToken

/-- Prepare the total recursive function once, then share it across statements.
Only the consumed prefix accumulates; a separator returns the untouched suffix.
The recursive call is in tail position, including long flat malformed input. -/
private abbrev Runner := String → List String → List LocatedToken → List LocatedToken →
  Except String Prefix

private def exhausted : Runner := fun _ _ _ _ => throw "source statement traversal fuel"

private def scanStep (next : Runner) : Runner := fun separator stack tokens reversed =>
  match tokens with
  | [] =>
    if !stack.isEmpty then throw "unclosed original statement expression"
    else throw "missing original statement separator"
  | token::rest =>
    if stack.isEmpty && token.text == separator then .ok ⟨reversed.reverse,token,rest⟩
    else do
      let following ← advance stack token
      next separator following rest (token::reversed)

private def scan : Nat → Runner := Nat.rec exhausted (fun _ next => scanStep next)

private theorem scan_original (separator : String) (fuel : Nat) (stack : List String)
    (tokens reversed : List LocatedToken) (result : Prefix)
    (ok : scan fuel separator stack tokens reversed = .ok result) :
    result.leading ++ [result.delimiter] ++ result.suffix = reversed.reverse ++ tokens ∧
      result.delimiter.text = separator := by
  induction fuel generalizing stack tokens reversed result with
  | zero => cases ok
  | succ fuel ih =>
    cases tokens with
    | nil =>
      simp only [scan,scanStep] at ok
      split at ok <;> contradiction
    | cons token rest =>
      simp only [scan,scanStep] at ok
      split at ok
      next ready =>
        cases ok
        simp only [Bool.and_eq_true,beq_iff_eq] at ready
        exact ⟨by simp only [List.append_assoc,List.singleton_append],ready.2⟩
      next notReady =>
        cases stepped : advance stack token with
        | error error => simp [stepped,bind,Except.bind] at ok
        | ok nextStack =>
          simp only [stepped,bind,Except.bind] at ok
          obtain ⟨retained,spelling⟩ := ih nextStack rest (token::reversed) result ok
          exact ⟨by simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using retained,spelling⟩

/-- An actual prepared scanner, bound to its executable definition. The function
chain is constructed once for the original body, not once for every let/cut. -/
structure Prepared (fuel : Nat) where
  tokenBound : Nat
  measured : tokenBound = fuel
  run : Runner
  original : run = scan fuel

/-- Recurse over Prepared values, not a curried function application. This
forces one construction of the runner chain before any statement is read. -/
def prepare : (fuel : Nat) → Prepared fuel :=
  Nat.rec ⟨0,rfl,exhausted,rfl⟩ (fun fuel previous =>
    ⟨fuel+1,rfl,scanStep previous.run,by rw [previous.original]; rfl⟩)

structure Cut (separator : String) (tokens : List LocatedToken) where
  leading : List LocatedToken
  delimiter : LocatedToken
  suffix : List LocatedToken
  spelling : delimiter.text = separator
  original : leading ++ [delimiter] ++ suffix = tokens

/-- The caller supplies its already measured original-token bound. Only the
prefix through the separator is traversed; the complete suffix stays shared. -/
def cutPrepared {fuel : Nat} (prepared : Prepared fuel) (separator : String) (tokens : List LocatedToken) :
    Except String (Cut separator tokens) := do
  if !["=",";"].contains separator then throw "unsupported statement separator"
  match scanned : prepared.run separator [] tokens [] with
  | .error error => throw error
  | .ok result =>
    have original := scan_original separator fuel [] tokens [] result
      (by simpa only [prepared.original] using scanned)
    return ⟨result.leading,result.delimiter,result.suffix,original.2,by simpa using original.1⟩

def cutWithFuel (fuel : Nat) (separator : String) (tokens : List LocatedToken) :
    Except String (Cut separator tokens) :=
  cutPrepared (prepare fuel) separator tokens

/-- Standalone compatibility entry. Repeated-body consumers share cutPrepared
with their one-time original bound, rather than remeasure/reprepare each suffix. -/
def cut (separator : String) (tokens : List LocatedToken) : Except String (Cut separator tokens) :=
  cutWithFuel (tokens.length+1) separator tokens

structure Let where
  keyword : LocatedToken
  pattern : List LocatedToken
  assignment : LocatedToken
  expression : List LocatedToken
  terminator : LocatedToken
  rest : List LocatedToken
  deriving BEq, DecidableEq, Repr

def Let.render (statement : Let) : List LocatedToken :=
  [statement.keyword] ++ statement.pattern ++ [statement.assignment] ++
    statement.expression ++ [statement.terminator] ++ statement.rest

structure Checked (tokens : List LocatedToken) where
  statement : Let
  original : statement.render = tokens
  keyword : statement.keyword.text = "let"
  assignment : statement.assignment.text = "="
  terminator : statement.terminator.text = ";"
  pattern : statement.pattern.isEmpty = false
  expression : statement.expression.isEmpty = false

def readPrepared {fuel : Nat} (prepared : Prepared fuel) (tokens : List LocatedToken) : Except String (Checked tokens) := do
  let first :: rest := tokens | throw "missing source let"
  if keyword : first.text = "let" then
    let binding ← cutPrepared prepared "=" rest
    let body ← cutPrepared prepared ";" binding.suffix
    let statement : Let := ⟨first,binding.leading,binding.delimiter,body.leading,body.delimiter,body.suffix⟩
    have original : statement.render = first :: rest := by
      calc
        statement.render = [first] ++ (binding.leading ++ [binding.delimiter] ++
            (body.leading ++ [body.delimiter] ++ body.suffix)) := by
          simp only [statement,Let.render,List.append_assoc]
        _ = [first] ++ (binding.leading ++ [binding.delimiter] ++ binding.suffix) := by rw [body.original]
        _ = first :: rest := by rw [binding.original]; rfl
    if pattern : statement.pattern.isEmpty = false then
      if expression : statement.expression.isEmpty = false then
        return ⟨statement,original,keyword,binding.spelling,body.spelling,pattern,expression⟩
      else throw "missing original let expression"
    else throw "missing original let pattern"
  else throw "source statement is not a let"

def readWithFuel (fuel : Nat) (tokens : List LocatedToken) : Except String (Checked tokens) :=
  readPrepared (prepare fuel) tokens

def read (tokens : List LocatedToken) : Except String (Checked tokens) :=
  readWithFuel (tokens.length+1) tokens

theorem Checked.originalTokens {tokens : List LocatedToken} (checked : Checked tokens) :
    checked.statement.render = tokens := checked.original

end QleisliKernel.SourceTypes.StatementSyntax
