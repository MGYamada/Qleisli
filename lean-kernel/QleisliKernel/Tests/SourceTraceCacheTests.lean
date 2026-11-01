import QleisliKernel.Tests.SourceTraceCost

/-! Original-body regressions for shared query reuse and honest composed work.
All quantum cases use at most two physical bits. These component tests do not
issue native accepted handles.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceTraceCacheTests
open QleisliKernel.Qirf
open QleisliKernel.SourceTypes
open QleisliKernel QleisliKernel.Semantics.SourceOwners

private def read (source : String) :=
  (SourceTrace.read (RawTraceTests.sources source) "main" "route").run 10000000

private def refused (source : String) : Bool :=
  match (read source).1 with | .error .request => true | _ => false

private def calls (source : String) : Option (List Nat × List Nat) :=
  (read source).1.toOption.map fun checked =>
    (checked.callOffsets,(valueOwners checked.result.value).map (·.ordinal))

-- The first H populates the cache. Later bindings, including already consumed
-- zero-owner values, still prevent that entry from authorizing another H.
#guard refused (RawTraceTests.single "let q=h(q);let h=q;h(h)")
#guard refused (RawTraceTests.single "let q=h(q);let h=();h(q)")
#guard refused (RawTraceTests.single "let q=h(q);let h=();let ()=h;h(q)")
#guard refused (RawTraceTests.single "let q=h(q);main::h(q)")
#guard refused (RawTraceTests.single "let q=h(q);measure_z(q)")
#guard refused (RawTraceTests.single "let q=h(q);h(q);q")

-- Reuse across successive statements, nested arguments and tuple siblings
-- retains every occurrence, owner and actual argument evaluation order.
#guard (calls (RawTraceTests.single "let q=h(q);h(q)")).map
  (fun (offsets,owners) => offsets.length == 2 && offsets.Pairwise (· < ·) && owners == [0]) = some true
#guard (calls (RawTraceTests.single "h(h(q))")).map
  (fun (offsets,owners) => offsets.length == 2 && offsets.Pairwise (· > ·) && owners == [0]) = some true
#guard (calls (RawTraceTests.pair "(h(a),h(b))")).map
  (fun (offsets,owners) => offsets.length == 2 && offsets.Pairwise (· < ·) && owners == [0,1]) = some true
#guard (calls (RawTraceTests.zeroPair "(u,h(h(q)))")).map
  (fun (offsets,owners) => offsets.length == 2 && offsets.Pairwise (· > ·) && owners == [0,1]) = some true

-- Source and actual Raw checks now fit one shared 10M budget after the separately
-- checked interval-root and count-reservation refactors. Earlier refusals remain
-- in immutable experiment snapshots; no second allowance is issued.
#guard ((SourceTrace.read SourceTraceCost.sources "main" "route").run 10000000).1.isOk
#guard (SourceTraceCost.composed.run 10000000).1.toOption = some (129,129)
#guard (SourceTraceCost.composed.run 2000000000).1.toOption = some (129,129)

-- Small composed cases retain the literal-instruction/complete-owner checks.
#guard RawTraceTests.checks (RawTraceTests.single "h(h(q))") RawTraceTests.twoH [1,1] id 10000000
#guard !RawTraceTests.checks (RawTraceTests.single "h(h(q))")
  {RawTraceTests.twoH with operations := [],outputs := [10]} [0,0] id 10000000

#print axioms QleisliKernel.SourceTypes.SourceTrace.evalCached
#print axioms QleisliKernel.SourceTypes.SourceTrace.read
end QleisliKernel.Tests.SourceTraceCacheTests
