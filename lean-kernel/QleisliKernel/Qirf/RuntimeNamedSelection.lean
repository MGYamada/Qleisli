import QleisliKernel.Qirf.RuntimeNamedSelectionBoundary

/-! One original named selection, including its distinct original-actual
prefix, checked against one final graph. Source preparation owns the original
call/callee/supply/slot partitions. The same-root consumers check that prefix,
every arm and Meaning, the literal local selection and the full caller return.
This bounded derivation does not discharge unrelated catalogue obligations,
root-refined meanings refused during preparation, or issue an execution handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeNamedSelection
open QleisliKernel Finite SourceTypes

structure AtRoot {artifact owner name arguments source request references}
    (named : @RuntimeNamedSelectionSource.Prepared artifact owner name arguments source request references)
    (root : Validity.Root) (runtime : RuntimeFamily.Request) where
  supplies : RuntimeNamedSelectionPrefix.Checked named.supplies root
  suppliesRead : RuntimeInterval.Computed (RuntimeNamedSelectionPrefix.read named.supplies root) supplies
  frame : RuntimeNamedSelectionBoundary.Prepared source.body root named.position runtime named.event named.callee
  frameRead : RuntimeInterval.Computed (RuntimeNamedSelectionBoundary.prepareSource named root runtime) frame
  child : RuntimeSelectionMeaning.LocalChecked named.selection root frame.frame.prepared frame.initial
  childRead : RuntimeInterval.Computed
    (RuntimeSelectionMeaning.readAt named.selection root frame.frame.prepared frame.initial) child
  boundary : RuntimeNamedSelectionBoundary.Checked named root runtime frame child
  boundaryRead : RuntimeInterval.Computed
    (RuntimeNamedSelectionBoundary.finish named root runtime frame child childRead) boundary

/-- The genuine prefix is consumed before this original call event. Neither
an arm's duplicate source leaf nor a final identity matrix replaces its header
occurrence. The existing named boundary then closes all original caller roles.
-/
def readAt {artifact owner name arguments source request references}
    (named : @RuntimeNamedSelectionSource.Prepared artifact owner name arguments source request references)
    (root : Validity.Root) (runtime : RuntimeFamily.Request) : WorkM (AtRoot named root runtime) := do
  let supplies ← NaturalAffine.witness (RuntimeNamedSelectionPrefix.read named.supplies root)
  let frame ← NaturalAffine.witness (RuntimeNamedSelectionBoundary.prepareSource named root runtime)
  let child ← NaturalAffine.witness
    (RuntimeSelectionMeaning.readAt named.selection root frame.val.frame.prepared frame.val.initial)
  let childRead : RuntimeInterval.Computed
      (RuntimeSelectionMeaning.readAt named.selection root frame.val.frame.prepared frame.val.initial) child.val :=
    by with_reducible exact child.property
  let boundary ← NaturalAffine.witness
    (RuntimeNamedSelectionBoundary.finish named root runtime frame.val child.val childRead)
  return ⟨supplies.val,by with_reducible exact supplies.property,frame.val,by with_reducible exact frame.property,
    child.val,childRead,boundary.val,by with_reducible exact boundary.property⟩

structure Checked {artifact owner name arguments source request references}
    (named : @RuntimeNamedSelectionSource.Prepared artifact owner name arguments source request references)
    (order : Array Nat) (runtime : RuntimeFamily.Request) where
  root : Validity.Root
  fresh : RuntimeInterval.Computed (Validity.checkRootFromRoots artifact order named.rows named.roots) root
  checked : AtRoot named root runtime
  consumed : RuntimeInterval.Computed (readAt named root runtime) checked

/-- This convenience reader performs the sole graph computation after all
prefix/provider/reference/site roots and source query rows are discovered. A
caller with an already retained final graph uses readAt instead of a new root.
-/
def read {artifact owner name arguments source request references}
    (named : @RuntimeNamedSelectionSource.Prepared artifact owner name arguments source request references)
    (order : Array Nat) (runtime : RuntimeFamily.Request) : WorkM (Checked named order runtime) := do
  let root ← NaturalAffine.witness (Validity.checkRootFromRoots artifact order named.rows named.roots)
  let checked ← NaturalAffine.witness (readAt named root.val runtime)
  return ⟨root.val,by with_reducible exact root.property,checked.val,by with_reducible exact checked.property⟩

def AtRoot.node {artifact owner name arguments source request references named root runtime}
    (checked : @AtRoot artifact owner name arguments source request references named root runtime) :
    RuntimePureBody.Node root.dependencies root.program checked.frame.ports.block.block := checked.boundary.node

end QleisliKernel.Qirf.RuntimeNamedSelection
