import QleisliKernel.Qirf.RuntimeDiscoveryTraversal

/-! Discover every original runtime body before the one fresh graph check.
The traversal follows actual source events and supplied context occurrences;
provider bodies retain their original supplier receipts. A discovery result is
not source/IR acceptance: local action, ordinary history, Meaning and access
continuations must still be checked under the final root.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeBodyDiscovery
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open SourceRuntimeValues

/-- Metadata discovery is a projection of the same source traversal that records
indexed body plans. The fixed mode has no recovery reader. -/
def visitUsing (artifact : Artifact) (operationMode : OperationMode artifact) (fuel : Nat) {owner name : String}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (events : List (SourceRuntimeContext.Event artifact.sources owner)) (staticRows : List (String × String))
    (request : Context) (prefixRequired : Bool) : WorkM (Discovery × List operationMode.Receipt) :=
  traverseUsing artifact operationMode fuel signature events staticRows request prefixRequired

/-- Existing source callers retain the strict continuation and return type. -/
def visit (artifact : Artifact) (fuel : Nat) {owner name : String}
    (signature : SourceRuntimeContext.Signature artifact.sources owner name)
    (events : List (SourceRuntimeContext.Event artifact.sources owner)) (staticRows : List (String × String))
    (request : Context) (prefixRequired : Bool) : WorkM Discovery :=
  traverseStrict artifact fuel signature events staticRows request prefixRequired

/-- One selected original signature and indexed body, under the exact supplied
catalogue. Both source entry points use this executable reader; no alternate
source, signature cache or acceptance result is introduced. -/
structure SelectedSource (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (owner name : String) (arguments : StaticTypes.Arguments) where
  signature : SourceRuntimeContext.Signature artifact.sources owner name
  selected : RuntimeInterval.Computed
    (SourceRuntimeContext.readSignature artifact.sources owner name arguments .external (some catalogue)) signature
  body : SourceRuntimeTrace.Body signature
  traversed : RuntimeInterval.Computed (SourceRuntimeTrace.readBodyWithSignature signature) body

def readSelectedSource (artifact : Artifact) (catalogue : GenericCatalogue.Checked artifact.sources)
    (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (SelectedSource artifact catalogue owner name arguments) := do
  let signature ← NaturalAffine.witness
    (SourceRuntimeContext.readSignature artifact.sources owner name arguments .external (some catalogue))
  let body ← NaturalAffine.witness (SourceRuntimeTrace.readBodyWithSignature signature.val)
  return ⟨signature.val,by with_reducible exact signature.property,body.val,by with_reducible exact body.property⟩

/-- Source preparation retains complete original pending assessments. It is
not a successful strict Source and cannot replace its withheld proof. Actual
operation/Meaning occurrences remain on this same indexed body for discovery.
-/
structure PreparedSource (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) where
  catalogue : GenericCatalogue.Checked artifact.sources
  audited : RuntimeInterval.Computed (GenericCatalogue.read artifact.sources) catalogue
  pending : SourcePendingMeaning.Prepared catalogue
  pendingRead : RuntimeInterval.Computed (SourcePendingMeaning.prepare catalogue) pending
  selection : SelectedSource artifact catalogue owner name arguments

def PreparedSource.signature {artifact owner name arguments}
    (source : PreparedSource artifact owner name arguments) := source.selection.signature

def PreparedSource.body {artifact owner name arguments}
    (source : PreparedSource artifact owner name arguments) : SourceRuntimeTrace.Body source.signature := source.selection.body

/-- All-original assessment precedes the selected signature/body. This is
non-accepting preparation: a closed M remains explicit and unconsumed. -/
def prepareSource (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (PreparedSource artifact owner name arguments) := do
  let catalogue ← NaturalAffine.witness (GenericCatalogue.read artifact.sources)
  let pending ← NaturalAffine.witness (SourcePendingMeaning.prepare catalogue.val)
  let selection ← readSelectedSource artifact catalogue.val owner name arguments
  return ⟨catalogue.val,by with_reducible exact catalogue.property,
    pending.val,by with_reducible exact pending.property,selection⟩

structure Source (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) where
  catalogue : GenericCatalogue.Checked artifact.sources
  audited : RuntimeInterval.Computed (GenericCatalogue.read artifact.sources) catalogue
  pending : SourcePendingMeaning.Checked catalogue
  pendingRead : RuntimeInterval.Computed (SourcePendingMeaning.read catalogue) pending
  signature : SourceRuntimeContext.Signature artifact.sources owner name
  selected : RuntimeInterval.Computed
    (SourceRuntimeContext.readSignature artifact.sources owner name arguments .external (some catalogue)) signature
  body : SourceRuntimeTrace.Body signature
  traversed : RuntimeInterval.Computed (SourceRuntimeTrace.readBodyWithSignature signature) body

def readSource (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments) :
    WorkM (Source artifact owner name arguments) := do
  let catalogue ← NaturalAffine.witness (GenericCatalogue.read artifact.sources)
  let pending ← NaturalAffine.witness (SourcePendingMeaning.read catalogue.val)
  let selection ← readSelectedSource artifact catalogue.val owner name arguments
  return ⟨catalogue.val,by with_reducible exact catalogue.property,
    pending.val,by with_reducible exact pending.property,selection.signature,
    selection.selected,selection.body,selection.traversed⟩

/-- Reuse every actual component of a successful strict read, including the
assessment preparation retained by that read. This claims no new whole-reader
run and never reconstructs a source body or canonical queue. -/
def Source.preparation {artifact owner name arguments} (source : Source artifact owner name arguments) :
    PreparedSource artifact owner name arguments :=
  ⟨source.catalogue,source.audited,source.pending.toPrepared,source.pending.preparedRead,
    ⟨source.signature,source.selected,source.body,source.traversed⟩⟩

structure Headers (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments)
    (request : Context) where
  source : Source artifact owner name arguments
  discovered : Discovery
  original : RuntimeInterval.Computed (visit artifact 128 source.body.checked.signature
    source.body.checked.events source.body.checked.summary.staticRows request true) discovered

def readHeaders (artifact : Artifact) (owner name : String) (arguments : StaticTypes.Arguments)
    (request : Context) : WorkM (Headers artifact owner name arguments request) := do
  let source ← readSource artifact owner name arguments
  let discovered ← NaturalAffine.witness (visit artifact 128 source.body.checked.signature
    source.body.checked.events source.body.checked.summary.staticRows request true)
  return ⟨source,discovered.val,by with_reducible exact discovered.property⟩

def Headers.roots {artifact owner name arguments request}
    (headers : @Headers artifact owner name arguments request) : List Nat :=
  (artifact.root :: headers.discovered.roots).eraseDups

structure Fresh {artifact owner name arguments request} (order : Array Nat)
    (headers : @Headers artifact owner name arguments request) where
  root : Validity.Root
  checked : RuntimeInterval.Computed
    (Validity.checkRootFromRoots artifact order headers.discovered.rows headers.roots) root

/-- This is the sole fresh graph after complete original discovery. No local
body continuation may replace its dependencies or check a different root. -/
def prepare {artifact owner name arguments request} (order : Array Nat)
    (headers : @Headers artifact owner name arguments request) : WorkM (Fresh order headers) := do
  let bytes := (artifact.sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  exactWork (Exact.charge (8+(bytes+artifact.sources.size+1)*(headers.discovered.rows.length+1)+
    16*(headers.discovered.roots.length+1)^2))
  let root ← NaturalAffine.witness
    (Validity.checkRootFromRoots artifact order headers.discovered.rows headers.roots)
  return ⟨root.val,by with_reducible exact root.property⟩

end QleisliKernel.Qirf.RuntimeBodyDiscovery
