import QleisliKernel.SourceTypes.SourceMeaning
import QleisliKernel.SourceTypes.CallSyntax

/-! Original operation-expression markers from the shared source row traversal.
Constructor children and original mixed-formal actuals have distinct path edges.
Every assertion retains the same parsed tokens and original name query. These
are metadata only: native child-edge alignment, actual invocation/substitution
and complete original duty association remain separate mandatory obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceOperation

inductive Edge where
  | child (ordinal : Nat)
  | actual (mixedOrdinal : Nat)
  deriving BEq, DecidableEq, Repr

structure Marker (sources : Sources) (caller : String) (scope : List String) where
  path : List Edge
  tokens : List LocatedToken
  call : CallSyntax.Checked tokens
  child : CallSyntax.Argument
  meaning : CallSyntax.Argument
  checkedOp : call.call.callee.map (·.text) = ["checked_op"]
  arguments : call.call.arguments = [child,meaning]
  childName : CallName.Name child.tokens
  selected : SourceMeaning.SelectedName sources caller scope (meaning.tokens.map (·.text))
  queried : ∃ before after,
    (SourceMeaning.selectName sources caller scope (meaning.tokens.map (·.text))).run before = (.ok selected,after)

/-- The original token index is supplied by the actual shared traversal run.
Rows keep their original order; assertion markers are collected child first. -/
structure Provenance (sources : Sources) (caller : String) (scope : List String)
    (_tokens : List LocatedToken) where
  rows : List (String × String)
  markers : List (Marker sources caller scope)

end QleisliKernel.SourceTypes.SourceOperation
