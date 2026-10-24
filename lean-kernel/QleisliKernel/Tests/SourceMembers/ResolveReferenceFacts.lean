import QleisliKernel.SourceTypes.Declarations

/-! Exact type probe for executable reference-lookup facts. No source-site
authorization or accepted-handle premise may be silently added.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceTypes.ResolveReferenceFacts
open QleisliKernel.SourceTypes

theorem exact_contract :
    ∀ (sources : Sources) (caller : String) (tokens : List String)
      (result : Resolved) (work left : Nat),
      (resolveReference sources caller tokens).run work = (.ok result,left) →
      (result.declaration.isPublic = true ∨ result.moduleName = caller) ∧
        originalBinding sources result.moduleName result.declaration.name =
          .ok (result.source,result.declaration) :=
  @resolveReference_facts

end QleisliKernel.Tests.SourceTypes.ResolveReferenceFacts
