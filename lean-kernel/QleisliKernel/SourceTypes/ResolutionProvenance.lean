import QleisliKernel.SourceTypes.Declarations

/-! Retained original import paths from the shared executable resolver. The
caller must bind its supplied query to the actual source type occurrence;
resolution alone grants neither source-row coverage nor execution authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.ResolutionProvenance

/-- The same resolver used by endpoint consumers, with its actual lookup path.
No caller-supplied trace or independent acceptance implementation is involved. -/
abbrev read := resolveReference

/-- Preserve order and original bytes. Deduplication and aggregation belong to
the caller only after it has bound these queries to its actual source reads. -/
def sourceRows (result : Resolved) : List (String × String) :=
  result.visited.map fun entry => (entry.moduleName,entry.source)

/-- The returned trace itself is the complete independent query/import route,
and each of its bindings was read from the exact original source table. -/
theorem read_query (sources : Sources) (caller : String) (tokens : List String)
    (result : Resolved) (work left : Nat)
    (ok : (read sources caller tokens).run work = (.ok result,left)) :
    Semantics.SourceResolution.Query sources caller tokens result.visited
      (ResolutionTrace.resolvedView result) ∧
      ResolutionTrace.OriginalLookups sources result.visited :=
  ResolutionTrace.resolveReference_retained_query sources caller tokens result work left ok

/-- The exact projected source rows retain their originating visited bindings.
This is a consequence of the full route theorem, not a substitute for it. -/
theorem read_original_rows (sources : Sources) (caller : String) (tokens : List String)
    (result : Resolved) (work left : Nat)
    (ok : (read sources caller tokens).run work = (.ok result,left))
    (row : String × String) (member : row ∈ sourceRows result) :
    ∃ entry ∈ result.visited, row = (entry.moduleName,entry.source) ∧
      originalBinding sources entry.moduleName entry.declaration.name =
        .ok (entry.source,entry.declaration) := by
  obtain ⟨entry,present,same⟩ := List.mem_map.mp member
  exact ⟨entry,present,same.symm,(read_query sources caller tokens result work left ok).2 entry present⟩

end QleisliKernel.SourceTypes.ResolutionProvenance
