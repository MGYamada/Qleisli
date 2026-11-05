import QleisliKernel.SourceTypes.SourceNominalSyntax

/-! Exact original ordinary enum match slices. The scrutinee and every arm body
remain independent children, with original optional block delimiters. Label
identity, completeness, typing, effects and owner frames remain checked duties.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceMatchSyntax

structure Body where
  opening : Option LocatedToken
  tokens : List LocatedToken
  closing : Option LocatedToken

def Body.render (body : Body) : List LocatedToken :=
  body.opening.toList ++ body.tokens ++ body.closing.toList

def Body.spelling (body : Body) : Bool :=
  match body.opening,body.closing with
  | none,none => !body.tokens.isEmpty
  | some opening,some closing => opening.text == "{" && closing.text == "}"
  | _,_ => false

private def readBody (tokens : List LocatedToken) : Except String Body := do
  if tokens.head?.map (·.text) == some "{" then
    let some opening := tokens.head? | throw "missing original match block"
    let (body,closing,suffix) ← SourceControlSyntax.delimiter "}" tokens.tail
    if !suffix.isEmpty then throw "trailing original match block tokens"
    return ⟨some opening,body,some closing⟩
  return ⟨none,tokens,none⟩

structure Arm where
  labelTokens : List LocatedToken
  label : SourceNominalSyntax.Variant labelTokens
  arrowStart : LocatedToken
  arrowEnd : LocatedToken
  body : Body
  comma : Option LocatedToken

def Arm.render (arm : Arm) : List LocatedToken :=
  arm.labelTokens ++ [arm.arrowStart,arm.arrowEnd] ++ arm.body.render ++ arm.comma.toList

def Arm.spelling (arm : Arm) : Bool :=
  arm.arrowStart.text == "=" && arm.arrowEnd.text == ">" &&
    arm.arrowStart.span.endByte == arm.arrowEnd.span.startByte && arm.body.spelling &&
    arm.comma.all (fun comma => comma.text == ",")

private def readArm (tokens : List LocatedToken) (comma : Option LocatedToken) : Except String Arm := do
  let (labelTokens,arrowStart,rest) ← SourceControlSyntax.delimiter "=" tokens
  let label ← SourceNominalSyntax.readVariant labelTokens
  let arrowEnd :: body := rest | throw "missing original match arrow end"
  return ⟨labelTokens,label,arrowStart,arrowEnd,← readBody body,comma⟩

private def readArms : Nat → List LocatedToken → Except String (List Arm) :=
  Nat.rec (fun _ => throw "original match arm traversal fuel") (fun _ recurse tokens => do
    if tokens.isEmpty then return []
    match SourceControlSyntax.delimiter "," tokens with
    | .ok (leading,comma,rest) => return (← readArm leading (some comma)) :: (← recurse rest)
    | .error _ => return [← readArm tokens none])

structure Match where
  keyword : LocatedToken
  scrutinee : List LocatedToken
  opening : LocatedToken
  arms : List Arm
  closing : LocatedToken

def Match.render (written : Match) : List LocatedToken :=
  [written.keyword] ++ written.scrutinee ++ [written.opening] ++ written.arms.flatMap Arm.render ++ [written.closing]

def Match.spelling (written : Match) : Bool :=
  written.keyword.text == "match" && !written.scrutinee.isEmpty && written.opening.text == "{" &&
    written.closing.text == "}" && !written.arms.isEmpty && written.arms.length ≤ 64 &&
    written.arms.all Arm.spelling

structure Checked (tokens : List LocatedToken) where
  parts : Match
  original : parts.render = tokens
  spelling : parts.spelling = true

private def parse (tokens : List LocatedToken) : Except String Match := do
  let keyword :: rest := tokens | throw "missing original match keyword"
  let (scrutinee,opening,rest) ← SourceControlSyntax.delimiter "{" rest
  let (body,closing,suffix) ← SourceControlSyntax.delimiter "}" rest
  if !suffix.isEmpty then throw "trailing original match expression"
  let arms ← readArms (body.length+1) body
  return ⟨keyword,scrutinee,opening,arms,closing⟩

def read (tokens : List LocatedToken) : Except String (Checked tokens) := do
  let parts ← parse tokens
  if original : parts.render = tokens then
    if spelling : parts.spelling = true then return ⟨parts,original,spelling⟩
    else throw "original match spelling"
  else throw "original match reconstruction"

end QleisliKernel.SourceTypes.SourceMatchSyntax
