import QleisliKernel.SourceTypes.Lexer

/-! Candidate byte-location properties and a local refinement check. The
properties do not call lex, declarations, member readers or any acceptance
routine. Lexer is imported for its shared data structures only. Its general
lexical/comment correctness and legacy behavior proofs remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.LocatedFacts

/-- Exact original byte range, without normalization or substring searching. -/
def TokenBytes (bytes : ByteArray) (token : LocatedToken) : Prop :=
  token.span.startByte < token.span.endByte ∧
  token.span.endByte ≤ bytes.size ∧
  bytes.extract token.span.startByte token.span.endByte = token.text.toUTF8

instance (bytes : ByteArray) (token : LocatedToken) : Decidable (TokenBytes bytes token) :=
  inferInstanceAs (Decidable (token.span.startByte < token.span.endByte ∧
    token.span.endByte ≤ bytes.size ∧
    bytes.extract token.span.startByte token.span.endByte = token.text.toUTF8))

/-- All recorded tokens read their original bytes in increasing, disjoint order.
Gaps may contain whitespace/comments; this predicate itself does not classify
those gaps or assert a complete lexical token stream. -/
inductive OrderedSlices (bytes : ByteArray) : Nat → List LocatedToken → Prop
  | nil (lower : Nat) : OrderedSlices bytes lower []
  | cons (lower : Nat) (token : LocatedToken) (tokens : List LocatedToken)
      (after : lower ≤ token.span.startByte) (slice : TokenBytes bytes token)
      (tail : OrderedSlices bytes token.span.endByte tokens) :
      OrderedSlices bytes lower (token :: tokens)

/-- Bounded sequential check over the already read metadata. It neither finds
source tokens nor accepts programs; it compares exact recorded byte locations. -/
def checkOrdered (bytes : ByteArray) (lower : Nat) (tokens : List LocatedToken) : Bool :=
  (tokens.foldr (fun token next lower =>
    decide (lower ≤ token.span.startByte ∧ TokenBytes bytes token) &&
      next token.span.endByte) (fun _ => true)) lower

/-- Candidate proof about this actual check; no source-faithfulness claim. -/
theorem checkOrdered_sound (bytes : ByteArray) (lower : Nat) (tokens : List LocatedToken)
    (ok : checkOrdered bytes lower tokens = true) : OrderedSlices bytes lower tokens := by
  induction tokens generalizing lower with
  | nil => exact .nil lower
  | cons token tokens ih =>
    change (decide (lower ≤ token.span.startByte ∧ TokenBytes bytes token) &&
      checkOrdered bytes token.span.endByte tokens) = true at ok
    have both := Bool.and_eq_true_iff.mp ok
    have facts : lower ≤ token.span.startByte ∧ TokenBytes bytes token :=
      of_decide_eq_true both.1
    exact .cons lower token tokens facts.1 facts.2 (ih token.span.endByte both.2)

end QleisliKernel.SourceTypes.LocatedFacts
