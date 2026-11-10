import QleisliKernel.Qirf.RuntimeContextRequest

/-! Complete reference-context obligations shared by named caller readers.
A direct selection call consumes its own ordered prefix and arm groups. The
existing ordinary/provider/reference body readers consume no such groups, so
every context below those boundaries must remain reference-free. These checks
inspect plain request data; they provide no Meaning or source-body equation.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeReferenceContexts
open QleisliKernel Finite
abbrev Context := RuntimeContextRequest.Context

private def withoutMeaningGroups (explicitEmpty : Bool) : Nat → Context → WorkM Unit :=
  Nat.rec (fun _ => throw .limit) (fun _ visit context => do
    exactWork (Exact.charge (16*(context.calls.length+context.branches.length+context.bodies.length+1)))
    if explicitEmpty then
      exactWork (Exact.charge (16*(context.references.length+1)))
      guard (context.references.all List.isEmpty) .request
    else
      guard context.references.isEmpty .request
    context.calls.forM fun (_,child) => visit child
    context.branches.forM fun (_,first,second) => do visit first; visit second
    context.bodies.forM fun (_,child) => visit child)

/-- The original singleton protocol walker keeps its strict empty list rule. -/
def noGroups : Nat → Context → WorkM Unit :=
  withoutMeaningGroups false

/-- The direct selection's own prefix/arm groups stay available to their
actual readers. A provider in the runtime format may explicitly encode an
empty group for a nested operation. Its strict body reader must still consume
each such group at the matching source occurrence. Meaning leaves keep the
original no-groups rule. -/
def selectionLeaves (context : Context) (explicitEmpty : Bool := false) : WorkM Unit := do
  exactWork (Exact.charge (16*(context.bodies.length+context.references.length+1)))
  context.bodies.forM fun (_,body) => withoutMeaningGroups explicitEmpty 129 body
  context.references.forM fun groups => do
    exactWork (Exact.charge (16*(groups.length+1)))
    groups.forM fun leaves => do
      exactWork (Exact.charge (16*(leaves.length+1)))
      leaves.forM fun (_,body) => noGroups 129 body

/-- Ordinary direct calls separately require an empty own group list; only
an authenticated direct selection may consume it. All descendants use the
ordinary body reader and cannot introduce another unconsumed group list. -/
def call (context : Context) : WorkM Unit := do
  selectionLeaves context
  exactWork (Exact.charge (16*(context.calls.length+context.branches.length+1)))
  context.calls.forM fun (_,child) => noGroups 129 child
  context.branches.forM fun (_,first,second) => do noGroups 129 first; noGroups 129 second

/-- The source-ordered preparation independently consumes every direct call
context and rejects unsupported root sites/branches/bodies. This complementary
walk checks all nested reference fields without a singleton-call assumption. -/
def ordered (context : Context) : WorkM Unit := do
  guard context.references.isEmpty .request
  exactWork (Exact.charge (16*(context.calls.length+1)))
  context.calls.forM fun (_,child) => call child

/-- The common runtime loop consumes each genuine body's own prefix and event
groups. Named and branch children have their own cursors. This plain data walk
provides no source, access, Meaning or execution evidence. -/
def runtime : Nat → Context → WorkM Unit :=
  Nat.rec (fun _ => throw .limit) (fun _ visit context => do
    selectionLeaves context true
    exactWork (Exact.charge (16*(context.calls.length+context.branches.length+1)))
    context.calls.forM fun (_,child) => visit child
    context.branches.forM fun (_,first,second) => do visit first; visit second)

end QleisliKernel.Qirf.RuntimeReferenceContexts
