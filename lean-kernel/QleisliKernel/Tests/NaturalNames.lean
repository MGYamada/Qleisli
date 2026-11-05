import QleisliKernel.SourceTypes.NaturalSyntax

/-! Existing Nat-only name categories. Ordinary names, qualified tails and
retired syntax retain their separate source grammar.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.NaturalNames
open SourceTypes

private def name (tokens : List String) : Option (List String) := do
  match ← (NaturalSyntax.read tokens).toOption with
  | .name path => some path
  | _ => none

#guard name ["Q"] = some ["Q"]
#guard name ["Op"] = some ["Op"]
#guard name ["Unit"] = some ["Unit"]
#guard name ["Bit"] = some ["Bit"]
#guard name ["CBit"] = some ["CBit"]
#guard !identifier "Q" && !identifier "Op" && !identifier "Unit" && !identifier "Bit" && !identifier "CBit"
#guard name ["helper","::","Q"] = none
#guard name ["helper","::","Bit"] = none
#guard name ["_"] = none
#guard name ["iso"] = none

end QleisliKernel.Tests.NaturalNames
