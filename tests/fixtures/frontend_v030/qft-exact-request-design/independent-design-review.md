# Independent bounded QFT request design review

Status: additive, local, non-normative review of candidate 1. The reviewer is
`/root/review_isometry_adapter`, separate from candidate author
`/root/isometry_cli_tests`. This review does not adopt a contract, interpretation,
guarantee, namespace or acceptance rule and grants no Issue-completion credit.

The reviewed original is `draft-01.md`, SHA-256
`eb5a4631e99902eb1d7c2439ff31adad36781f75783ed49990d6e9715ea5b471`.
Its eight mapped members and original packet map remain unchanged. The additive
input map records inspected source bytes; it does not attest a compiled binary.
No CLI, native checker, harness, Cargo/Lean build, mathematical probe, test,
Git command or GitHub mutation was executed for this review.

## Assessment

The proposed widths 0, 1, 2 and 3, independent positive Fourier request and
separate zero-width identity-rewire request are suitable for a bounded next
experiment. The candidate correctly distinguishes exact checking under the
current named structural contract from an analytic Fourier theorem, original
source preservation, family/resource certification and canonical std exposure.
The concrete shell-position correction is necessary for current Rust output.
The following constraints should be explicit in the future adapter/harness;
they are implementation requirements for the proposed experiment, not new
production-language decisions.

## Independent expectation and current native gate

The retained #317 contract fixes
`F_n[y,x] = exp(+2*pi*i*x*y/2^n)/sqrt(2^n)`, with axis zero of weight one,
explicit output reversal and exact global phase. The ordinary local source's
high-bit H, positive controlled phases and final pair swaps agree with that
convention by inspection. This review performed no coefficient calculation or
execution and does not convert the previous numerical authoring observations
into exact request evidence.

For n = 1, 2 and 3, the independently fixed complete request port is one owner
0, axes `[0,...,n-1]`, basis exactly `[{tag:bits,width:n}]`, with no classical
ports and identical input/output headers. The singleton `qft` meaning records
the requested width. No candidate Meaning, function name or inferred effect is
an oracle for those requirements. Freeze the request bytes before candidate
request checks and before mutations; assert `NativeChecked.payload()` and
`request()` retain exactly the bytes supplied in each successful call.

`Kernel::inspect_native` and `check_against_native` are the appropriate current
methods. The latter constructs QLF1 for the singleton positive-width Fourier
request and uses a fresh native process. `FourierRoot.checkAll` first checks the
complete artifact, then its actual recursive body, phase-free routes and named
Bits boundary. `Protocol.HierarchicalFinite.checkHadamards` supplies the exact
matrix `[r,r;r,-r]`, where `r = 1/sqrt(2)`, to the original finite QIRF bytes.
A producer's self-consistent X description cannot redefine that H obligation.
The returned H indices must be distinct leaf indices, exactly one per width.

The named inspector binds actual constructors, ports, axes, positive controls,
precision-scaled gradients, routing and mandatory exact H leaves. Its current
theorems establish those executable structural conditions. They do not prove
the analytic Fourier denotation for every accepted hierarchy or a translation
theorem from the original `.qli` source. Keep those limitations visible even
if all proposed bounded calls succeed.

The older ignored `tests/sized_corpus.rs::check_source_fourier_contracts` uses
`inspect`/`check_against` and transitional Rust reconstruction. It is historical
context, not a substitute for this current direct-native experiment. Do not
execute that ignored helper or its broader Python driver from this packet.

## Wrapper and compaction requirements

`FourierRoot.project` and Rust `wiring_order` both reserve child position 1 for
the recursive body. Current Rust factoring emits
`[enter, recursive_body, leave, reversal, optional_output_rename]`. The historical
three-child wrapper around the entire old root would put a shell in the body's
position and can reject a correct output. Candidate 1's corrected structure,
`[composed_enter, old_recursive_body, ...old_suffix, post_rewire]`, preserves the
right position without modifying the matcher.

Rewire arrays contain **positions**, not the owner/axis labels written in port
headers. For a single register, a label-only route has `owners:[0]`,
`axes:[0,...,n-1]`, `classical:[]`, even when the actual endpoint labels are
nonzero. Require exact basis constructors and corresponding coordinate order
at both endpoints. Do not sort actual axes, infer weights from axis labels,
reverse the wrapper's coordinate map, or let the adapter supply a missing real
reversal. Keep the original suffix as ordered children and record any original
output rename separately. New prefix/postfix routes must be phase-free.

Whole native preparation does require every emitted row to be reachable:
`Artifact.finish` calls `Graph.checkWithBudget` with the implementation/proof
roots, and `Graph.reachable` requires all flattened table nodes to be reached.
Thus an obsolete original root and its unique auxiliary rows cannot simply be
left as unreachable evidence beside a new root.

If the adapter compacts, use separate maps for definitions, meanings, encodings
and proofs. Remap all body references, proof premises, implementation/meaning
indices, input/output encodings, typed witness references and both entry
indices. Do not assume four tables have equal lengths or that the general
native format makes their indices interchangeable. Current Rust producer
definition/meaning/proof indices happen to coincide; encoding indices do not.
Reject unsupported constructors rather than discard their references. Verify
the complete retained dependency closure, not just the recursive body's direct
definition children. Fresh whole-artifact inspection remains mandatory.

Candidate 1's phrase "retained byte identity" needs a precise scope. The
preserved original artifact bytes and finite `program`/`description` strings
can remain byte-identical. JSON rows containing remapped indices cannot all
remain byte-identical. For those rows, record exact correspondence modulo the
explicit table-reference maps, with every non-reference field unchanged. This
includes ports, constructor data, phase/count/polarity and child order.

An alternative bounded adapter may replace only the original outer-root row
and its own Meaning/proof header/children, append the needed label routes and
prefix sequence, and retain all original recursive-body indices. The current
transport schedules acyclic dependencies rather than requiring lower numeric
indices, so forward-index append references are not inherently prohibited.
This avoids recursive-body reindexing, but requires the same complete
reachability, encoding and proof checks. It is an unexecuted option, not a
preferred implementation or an established validity result.

## Width zero and negative-test coverage

`F_0=[+1]` retains one logical `Q<Bits<0>>` owner with no axes. It is neither an
empty quantum interface nor `Q<Unit>`. The fixed zero request's identity
rewire is `owners:[0], axes:[], classical:[]`; complete endpoint identity and
Bits0 basis must match. A literal `identity` Meaning is a different constructor.
Do not request named `qft0`, widen its positive-width matcher, or replace the
actual root with a wished-for shape after an unexpected first failure.

Canonical owner 0 is the clean independent boundary. If the experiment instead
associates candidate header labels to the fixed zero request, record this as
explicit endpoint association and verify the complete one-owner Bits0 header;
it is not an independently authenticated source identity. A three-rewire zero
wrapper requires its separately specified three-child request. Generic
pairing is compositional and can reject different child arity before a native
process is invoked.

A global phase is meaningful at width zero and under an external reference.
However, the native named `phase` Meaning and `dyadic_phase` definition require
a Bit target; they cannot simply be placed on a Bits0 owner to manufacture a
native-valid negative. The existing `phase_eighth` lowering instead tensors
the retained atom's identity with a closed scalar, whose internal Unit owner
is packed, checked as an exact 1x1 finite leaf, and unpacked. That is a suitable
source candidate for a future fresh-validity observation. Its changed
composition may fail the zero identity request during Rust pair construction;
such a result tests structural refusal, not an observed native scalar-matrix
comparison. Isolating a zero-scalar coefficient comparison would require a
separately fixed composition request and exact internal finite identity oracle.
No such additional experiment was executed or required to pass here.

Wrong phase/reversal/provider tests should retain two distinct tracks:

- Preserve ordinary wrong-phase, omitted-reversal and h-named-X source studies
  with their first actual outcomes. Optional Fourier factoring may stop; a
  resulting representation rejection does not exercise the intended inner
  phase or H obligation.
- Separately retain structurally preserved artifact mutants, with consistent
  own Meanings/proofs and original exact port/type interfaces. Each needs its
  own successful fresh native inspection followed by the unchanged independent
  request. Only those observations can isolate a Fourier phase, suffix reversal
  or original-QIRF H failure. Grafting an X leaf also requires its QIRF owner,
  axis and type boundary to be bound to the actual chosen H slot.

Use n = 2 for reversal negatives: width-one reversal is identity. The wrong
phase can preserve all arities and port shapes while changing the candidate's
own supported dyadic phase consistently. The missing-reversal mutant can keep
the original suffix arity and use an identity route of the same complete
endpoint types. The H/X mutant must update actual QIRF and its own exact finite
description consistently, leaving the independent H request unchanged.

The Q<Bit>/Q<Bits<1>>, Q<Unit>/Q<Bits<0>> and zero-owner/one-owner negatives are
proper complete-interface tests. Equal physical widths must not repair them.
Their successful native inspection, failure stage and native invocation count
are observations to be retained, not assumed by this design review. Distinguish
source checking, strict transport, pair construction, native structure and
exact finite checks in the results. Preserve genuine unexpected diagnostics.

## Authority and remaining scope

Startup originals and the already passed continuity check against trusted base
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2` were reconstructed earlier; this task
reuses that result while protected records remain unchanged. QS-2026-01,
PR-2026-01, quantitative RS-2026-01 and EXACT-2026-01 retain pending duties.
The only admitted guarantees remain the two original decoded ordinary QLV1
ownership/scope guarantees. Neither the candidate nor this review widens them.

The first 0..3 request capture, analytic/general Fourier proof, original-source
preservation, external-reference theorem, exact retained specialization
correspondence, quantitative family bounds and complete common frontend/std
migration remain separate unfinished work. Preserve the previous authoring
sources/licenses/results and all original packet members. This review changes
no production acceptance, native authority, library API or #317 criterion.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
