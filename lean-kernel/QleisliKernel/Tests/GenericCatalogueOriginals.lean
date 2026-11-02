import QleisliKernel.Qirf.SourcePendingMeaning
import QleisliKernel.Tests.SourceTraceOriginals

/-! Complete original source catalogues within the unchanged work allowance.
These checks traverse source/type/effect metadata only. They do not execute a
quantum case, construct a joined quantum matrix, or grant an accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericCatalogueOriginals
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite

private def read (sources : Sources) : Option Nat :=
  let action : WorkM Nat := do
    let catalogue ← GenericCatalogue.read sources
    let _ ← Qirf.SourcePendingMeaning.read catalogue
    pure catalogue.records.length
  (action.run 10000000).1.toOption

-- The original eight bundled modules are complete, including all private,
-- generic and unused declarations and original imports/reexports.
#guard read SourceTraceOriginals.bundled == some 30

-- The same check also covers an actual small caller with the implicit prelude.
-- A separate budget for each component cannot establish this whole invocation.
#guard read (#[("main",SourceTraceOriginals.structural_control)] ++
  SourceTraceOriginals.bundled) == some 34

end QleisliKernel.Tests.GenericCatalogueOriginals
