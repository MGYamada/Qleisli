import QleisliKernel.SourceTypes.Declarations

/-! Small original-query controls; no source-body execution or accepted handles.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceMembers.ResolutionRoute
open QleisliKernel.SourceTypes

def terminal (sources : Sources) (caller : String) (tokens : List String) :
    Option (String × String) :=
  match (resolveReference sources caller tokens).run 1000000 with
  | (.ok result,_) => some (result.moduleName,result.declaration.name)
  | _ => none

def chain : Sources := #[
  ("origin","pub enum Choice { A, B, C }"),
  ("middle","pub use origin::Choice;"),
  ("caller","use middle::Choice;")]

example : terminal chain "caller" ["Choice"] = some ("origin","Choice") := by decide +kernel
example : terminal chain "external" ["middle","::","Choice"] = some ("origin","Choice") := by decide +kernel
example : terminal chain "external" ["caller","::","Choice"] = none := by decide +kernel
example : terminal #[ ("origin","enum Choice { A }") ] "origin" ["Choice"] =
    some ("origin","Choice") := by decide +kernel
example : terminal #[ ("origin","enum Choice { A }") ] "external"
    ["origin","::","Choice"] = none := by decide +kernel
example : terminal #[ ("origin","enum Choice { A }"),
    ("middle","pub use origin::Choice;") ] "middle" ["Choice"] = none := by decide +kernel
example : terminal #[ ("first","pub use second::Choice;"),
    ("second","pub use first::Choice;") ] "first" ["Choice"] = none := by decide +kernel
example : terminal chain "caller" [] = none := by decide +kernel
example : terminal chain "caller" ["middle","::"] = none := by decide +kernel
example : terminal chain "caller" ["middle","Choice"] = none := by decide +kernel
example : terminal chain "caller" ["middle","::","::","Choice"] = none := by decide +kernel
example : terminal (chain.push ("origin","pub enum Choice { X }")) "caller" ["Choice"] =
    none := by decide +kernel
example : terminal #[ ("origin","pub enum Choice { A } pub enum Choice { B }") ]
    "origin" ["Choice"] = none := by decide +kernel

/-- The required conclusion retains both the exact query and every visited
original lookup. No assumed endpoint, caller authentication or desired value. -/
theorem exact_query_contract :
    ∀ (sources : Sources) (caller : String) (tokens : List String)
      (result : Resolved) (work left : Nat),
      (resolveReference sources caller tokens).run work = (.ok result,left) →
      ∃ events,
        QleisliKernel.Semantics.SourceResolution.Query sources caller tokens events
          (ResolutionTrace.resolvedView result) ∧
        ResolutionTrace.OriginalLookups sources events :=
  @ResolutionTrace.resolveReference_query

end QleisliKernel.Tests.SourceMembers.ResolutionRoute
