import Std
import QleisliKernel.Semantics.FiniteCarrier

/-! Shared source syntax data. Lexing, parsing, resolution and acceptance remain
outside this module. Existing declaration names and fields are retained.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes

/-- Half-open UTF-8 byte range in the retained, unnormalized source. -/
structure SourceSpan where
  startByte : Nat
  endByte : Nat
  deriving BEq, DecidableEq, Repr

/-- The same independent token stream, retaining its original byte occurrence. -/
structure LocatedToken where
  text : String
  span : SourceSpan
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for SourceSpan, LocatedToken

structure Declaration where
  name : String
  isPublic : Bool
  kind : String
  body : List String
  deriving BEq, DecidableEq, Repr

deriving instance ReflBEq, LawfulBEq for Declaration

/-- A brace body found by the shared declaration scanner. The complete header
and inner tokens retain original locations. A function envelope is syntax data,
not proof that its header/body is well-typed or that it authorizes a caller. -/
structure BodyOccurrence where
  declaration : Declaration
  nameToken : LocatedToken
  header : List LocatedToken
  openBrace : LocatedToken
  body : List LocatedToken
  closeBrace : LocatedToken
  deriving BEq, DecidableEq, Repr

structure SourceCatalogue where
  declarations : List Declaration
  bodies : List BodyOccurrence
  deriving BEq, DecidableEq, Repr

namespace OrdinaryBody

/-- Logical component inputs, never Raw SSA identifiers or accepted values.
The implementation reader checks them against its original parameter types. -/
inductive Argument where
  | unit
  | bit (value : Bool)
  | enumeration (origin : Semantics.FiniteCarrier.Origin) (ordinal : Nat)

inductive Expr where
  | unit (tokens : List LocatedToken)
  | bit (tokens : List LocatedToken) (value : Bool)
  | name (tokens : List LocatedToken)
  | call (tokens path : List LocatedToken) (arguments : List Expr)
  | record (tokens path : List LocatedToken) (fields : List (LocatedToken × Expr))
  | project (tokens : List LocatedToken) (receiver : Expr) (field : LocatedToken)
  | conditional (tokens : List LocatedToken) (condition yes no : Expr)
  | matching (tokens : List LocatedToken) (scrutinee : Expr)
      (arms : List (List LocatedToken × Expr))

def Expr.tokens : Expr → List LocatedToken
  | .unit tokens | .bit tokens _ | .name tokens | .call tokens _ _ |
    .record tokens _ _ | .project tokens _ _ | .conditional tokens _ _ _ |
    .matching tokens _ _ => tokens

structure LetSyntax where
  tokens : List LocatedToken
  name : LocatedToken
  value : Expr

structure Body where
  bindings : List LetSyntax
  result : Expr

def Body.tokens (body : Body) : List LocatedToken :=
  body.bindings.flatMap (·.tokens) ++ body.result.tokens

end OrdinaryBody
end QleisliKernel.SourceTypes
