import QleisliKernel.Qirf.Checked
import QleisliKernel.SourceTypes.SourceRuntimeTrace

/-! Original source coverage for the ordinary and mixed runtime root gates.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.TypedSourceRoot
open Finite SourceTypes

abbrev Rows := List (String × String)

private def sourceBytes (artifact : Artifact) : Nat :=
  (artifact.sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize).sum

/-- Signature and graph evidence may already cover every supplied row. If
body dependencies are needed, derive their paths from the actual original
body and callees. This decision occurs before the shared Raw root check. -/
def provenance (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments)
    (signatureRows : Rows) : WorkM Rows := do
  exactWork (Exact.charge (artifact.entries.size +
    (artifact.entries.toList.map (·.sources.length)).sum +
    (sourceBytes artifact + artifact.sources.size + 1) * (signatureRows.length + 1)))
  if Validity.sourcesUsedWithSources artifact signatureRows then
    return signatureRows
  let body ← SourceRuntimeTrace.read artifact.sources owner name arguments
  SourceTrace.retainStaticRows (signatureRows ++ body.signature.sourceRows ++ body.summary.staticRows)

structure Binding (artifact : Artifact) (order : Array Nat) (owner name : String)
    (arguments : StaticTypes.Arguments) (signatureRows : Rows) (root : Validity.Root) where
  rows : Rows
  originalRows : ∃ before after,
    (provenance artifact owner name arguments signatureRows).run before = (.ok rows,after)
  originalRoot : ∃ before after,
    (Validity.checkRootWithSources artifact order rows).run before = (.ok root,after)

def read (artifact : Artifact) (order : Array Nat) (owner name : String)
    (arguments : StaticTypes.Arguments) (signatureRows : Rows) :
    WorkM (Σ root, Binding artifact order owner name arguments signatureRows root) := do
  let rows ← NaturalAffine.witness (provenance artifact owner name arguments signatureRows)
  exactWork (Exact.charge (2 * (sourceBytes artifact + artifact.sources.size + 1) *
    (rows.val.length + 1)))
  let root ← NaturalAffine.witness (Validity.checkRootWithSources artifact order rows.val)
  return ⟨root.val,⟨rows.val,rows.property,root.property⟩⟩

end QleisliKernel.Qirf.TypedSourceRoot
