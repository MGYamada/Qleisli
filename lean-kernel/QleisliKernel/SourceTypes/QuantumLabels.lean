import QleisliKernel.SourceTypes.OrdinarySignature
import QleisliKernel.SourceTypes.NaturalSyntax

/-! The shared exact original scalar/enum label reader. Completeness, owner
types, controlled implementations and native equations remain separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.QuantumLabels
open Semantics.FiniteCarrier Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

structure Label (sources : Sources) where
  ordinal : Nat
  typeQuery : Option (TypeRead sources)

def Label.sourceRows {sources : Sources} (label : Label sources) : List (String × String) :=
  match label.typeQuery with | none => [] | some query => query.sourceRows

def read (sources : Sources) (caller : String) (selector : Basis) (tokens : List LocatedToken) :
    WorkM (Label sources) := do
  match selector with
  | [.unit] | [.bit] | [.bits _] =>
    let [literal] := tokens | throw .request
    let ordinal ← adapt (NaturalSyntax.decimal literal.text)
    guard (ordinal ≤ 4294967295) .request
    pure ⟨ordinal,none⟩
  | [.enumeration _ variants] =>
    let some variant := tokens.getLast? | throw .request
    guard (tokens.length ≥ 3 && (tokens[tokens.length-2]?.map (·.text)) == some "::") .request
    let ty ← typeExpressionWithSources sources caller ((tokens.dropLast.dropLast).map (·.text))
    guard (ty.basis == selector && variants.contains variant.text) .request
    pure ⟨variants.idxOf variant.text,some ty⟩
  | _ => throw .request

end QleisliKernel.SourceTypes.QuantumLabels
