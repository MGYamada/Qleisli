# Bounded independent QFT request experiment — candidate 1

Status: local, non-normative read-only design candidate for Issue #317.
This packet records source/API inspection and proposed future tests. It creates
no language rule, primitive, acceptance mode, theorem, constitutional
interpretation, guarantee admission, canonical std API or Issue completion.

No qleisli CLI, native checker, Cargo/Lean build, mathematical probe or test of
the proposed cases was executed for this design. Read-only shell inspection,
GitHub Issue retrieval, file hashing, the constitutional identity check and
local packet writing are separate performed operations. Expected outcomes
below are predictions until an authorized bounded experiment retains actual
first diagnostics and fresh native results.

## Source and upper contract

The fresh Issue snapshot is retained in issue-317.connector.json and
issue-317.md. It contains all 24 acceptance criteria and the ordinary before-code
contract. The exact semantic family is

    F_n[y,x] = exp(+2*pi*i*x*y/2^n) / sqrt(2^n).

Axis zero has weight one; output reversal is part of this phase-fixed positive
operator. F_0 = [+1] on the same Q<Bits<0>> logical owner, distinct from Q<Unit>.
All inputs and external references remain in scope. Future tests here are
only n = 0,1,2,3, not a proof for the family or arbitrary unnormalized inputs.

The frozen ordinary local implementation is
tests/fixtures/authoring_sessions/qft-family-v030/attempt-01/transform.qli.
Its positive-width body adapts the licensed pinned Qualtran translation
corpus/sized/qualtran_qft/fourier.qli, retaining Google attribution. Its
ordinary pub fn qft[static n: Nat] has an outer zero-width identity branch.
The current fixed std specializations still live in stdlib/src/transforms.qli.
Neither this study nor this design exposes std::transform::qft as a canonical
production library API.

QS-2026-01, PR-2026-01, RS-2026-01 and EXACT-2026-01 apply with their adopted
scopes. The existing two ordinary QLV1 ownership/scope guarantees are protected;
this hierarchy study does not extend them. Broad QS/PR/quantitative RS and
the exactness supplement remain pending. The recorded identity check with
continuity base faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2 passes; it is not a
fresh Lean replay, binary attestation, human adequacy judgment or release gate.

## Actual API and transport

src/bin/qleisli/source_plan/options.rs describes these existing selected-source
flags. The future fixed emit command shape is:

    qleisli emit-proposal --entry=transform::qft --module=transform=PATH \
      --nat=n=N --ir-profile=hierarchy --output=PATH --format=json

Only N=0,1,2,3 may be used. emit-proposal requires output and rejects
kernel/request/provider options. It is untrusted and does not invoke the kernel.
The future driver must first preserve source/edition manifest bytes, ordered
argv, CLI/native identities and exact output bytes. It must not execute commands
or scripts selected by artifact metadata.

src/bin/qleisli/source_plan.rs PreparedIr::payload and emission write only the
hierarchical payload. The CLI JSON report has entry, source-check scope and
native-check scope, but these are not source identities inside the artifact.
HierarchyProposal privately retains its ElaboratedProgram, precursor and events;
src/frontend/sized/lower.rs exports tables without the source path/hash/entry
spelling. Finite-leaf transport source arrays are empty. Thus source-to-output
association is recorded producer provenance. Fresh output acceptance alone
does not establish original-source preservation or authenticate its author.

src/interchange/hierarchical.rs provides the actual fresh-native operations:

    Kernel::inspect_native(payload) -> NativeChecked
    Kernel::check_against_native(payload, request) -> NativeChecked

The first decodes and freshly checks original QIRF leaves. The second separately
decodes the independently supplied request, dispatches to the Fourier or generic
request mode, and validates returned original-leaf/request obligations.
NativeChecked retains exact immutable payload/request bytes. Assert those bytes
equal the candidate and frozen independent request used in that call.

src/interchange/hierarchical/runtime.rs uses --hierarchy-pending,
--hierarchy-request-pending and --hierarchy-fourier-pending with an explicit
product version. Missing, incompatible or failed native checking must reject;
serialized receipts or an earlier successful inspection are not inputs
authorizing the next request call. Every proposed mutant needs its own fresh
inspection and its own fresh unchanged-request decision.

tests/sized_corpus.rs::check_source_fourier_contracts is useful historical
structure, but its ignored helper uses older transitional Rust reconstruction.
Prefer the direct native methods above for a future narrow gate test, with a
coordinated existing executable. Do not run the full ignored helper or rebuild
a checker from this read-only packet.

## Independently authored positive request

For each positive n=1,2,3, freeze the request before the candidate request check.
The complete external schema is qleisli.hierarchy-request version1,
profile qpe-dyadic8-v1, equation/unitary, entry0 and a singleton qft meaning.

The independently specified port is owner0, axes[0,...,n-1], and exactly the
basis atom [{tag:bits,width:n}]. Both interface sides contain exactly that one
quantum port and no classical ports. In JSON-like notation:

    {
      "format": "qleisli.hierarchy-request", "version": 1,
      "profile": "qpe-dyadic8-v1", "kind": "equation", "effect": "unitary",
      "interface": {
        "inputs": {"quantum": [P_n], "classical": []},
        "outputs": {"quantum": [P_n], "classical": []}
      },
      "entry": 0,
      "meanings": [{
        "interface": THE_SAME_INDEPENDENT_INTERFACE,
        "body": {"tag": "qft", "width": n}
      }]
    }
    P_n = {"owner":0,"axes":[0,...,n-1],"basis":[{"tag":"bits","width":n}]}

THE_SAME_INDEPENDENT_INTERFACE is built from the fixed contract above, never
copied from candidate meanings. The request carries exact structural/phase
requirements; no numerical tolerance is part of it.

scripts/test_sized_qft.py::request uses this existing schema.
src/interchange/hierarchical/bridge/request.rs requires strict fields,
acyclic meaning tables and one matching unitary equation for a qft root,
then frames QLF1. lean-kernel/Protocol/Hierarchical.lean::parseFourier checks
the repeated complete header and singleton request.
QleisliKernel/Hierarchical/FourierRoot.lean checks complete root interface,
positive width, the structural recursive body and phase-free enter/suffix
routing. It returns mandatory phase-fixed H obligations checked against
the original native finite leaves. Protocol/HierarchicalFinite.lean supplies
the exact H request rather than accepting a producer-named provider.

This is exact checking under the existing named Fourier structural contract.
It is not a general arbitrary-matrix equality API and does not by itself prove
the analytic F_n denotation or a source-preservation theorem for every accepted
hierarchy. Keep those separate missing obligations explicit.

## Outer-shell position 1 and explicit boundary relabeling

scripts/test_sized_qft.py::canonical_boundary wraps a noncanonical artifact in
[rewire(canonical,before), entire_old_root, rewire(after,canonical)].
Its historical Python factored producer often already has canonical owner0,
so those successful tests do not establish this wrapper for the current Rust
payload.

src/frontend/sized/fourier.rs::factor_fourier currently produces the root

    [enter, recursive_body, leave, reversal, optional_output_rename].

FourierRoot.project and bridge/request.rs::wiring_order treat child position1
as the recursive Fourier body. Blindly putting an entire Rust outer shell at
position1 instead supplies another shell to FourierBody.inspect and can reject
a mathematically correct candidate. This is a concrete representation obstacle,
not evidence that the positive Fourier equation is false.

A future bounded, untrusted adapter may only compose explicit label rewiring:

1. Inspect/require the complete one-register Bits<n> interface and the original
   outer shell. Preserve the original artifact bytes.
2. Compose the canonical-to-original boundary rewire with the original enter
   as a phase-free sequence.
3. Keep the original recursive body in position1, unchanged.
4. Retain the original suffix, including its real reversal; append only the
   original-output-to-canonical label rewire.
5. Remove/remap obsolete unreachable table rows, since whole native checking
   requires the table to be live. Record each old/new index and retained byte
   identity. Do not replace phase-bearing bodies or reconstruct a wished-for
   body from its function name.

The new root is [composed_enter, old_recursive_body, ...old_suffix, post_rewire].
Prefix and postfix preserve coordinate positions; they change bookkeeping
owner/axis labels only and cannot supply a missing reversal. Freshly inspect
the resulting complete artifact before testing the independent request.
Original output, adapted output, adapter source/hash and explicit index map
remain separate retained inputs. No new matcher exception is proposed.

## Width-zero exact identity, with its logical owner

Native named qft width0 is unsupported:
FourierRoot.inspect rejects width0 and Artifact.MeaningBody.bounded requires
1 <= width <= 8. Do not request qft0 or waive this rule.

The current empty pure body uses Graph.identity, implemented by Graph.rename.
Its expected meaning constructor is an identity rewire, not the distinct
literal identity constructor:

    {"tag":"rewire","permutation":{"owners":[0],"axes":[],"classical":[]}}

The independently required header has one retained owner with exactly the
Bits0 atom and no axes, equal input/output owner identity and no classical side.
Do not replace this with empty quantum sides or a Q<Unit> port. Physical width
zero does not eliminate a logical owner or identify those basis constructors.

The generic request gate in QleisliKernel/Hierarchical/Root.lean::aligned
compares complete headers and constructor shape. It cannot silently identify
literal identity with rewire, or a leaf with a sequence. Freeze the zero
request as the explicitly required identity-rewire constructor, independently
of candidate proposed meanings. If the bare emitted node retains nonzero
bookkeeping labels, either bind only those verified header labels while keeping
the fixed semantic/type request, or deliberately canonicalize with a separately
specified three-rewire identity sequence and request that exact structure.
Any label binding is recorded as interface association, not independently
authenticated source identity.

Before either approach, assert exactly one Bits0 owner with empty axes,
equal before/after identity and the expected root shape. Preserve any actual
unexpected shape/failure rather than broadening the request until it passes.
A future scalar phase_eighth zero mutant should fail the unchanged exact
identity request; generic child-arity pairing may reject before native dispatch,
so retain that actual stage/invocation count instead of calling it a native
rejection without evidence.

## Bounded adversarial candidates

All candidates are fresh untrusted programs/artifacts and undergo complete
declaration checking and fresh native inspection. Changing their own proposed
meanings consistently keeps them well-formed candidates; those meanings are
never the expected independent request. A candidate is described as
fresh-native-valid only after its own inspection actually succeeds.

| Candidate | Independent unchanged contract | Predicted rejection |
| --- | --- | --- |
| Wrong controlled phase at n2: pi/2 replaced by pi, with the candidate's own meaning updated | Positive F_2 request | Exact phase/stage mismatch |
| Missing real reversal at n2: substitute a valid identity route, preserving own consistent graph | Positive F_2 request with low-axis order | Suffix identity differs from required reversal |
| Changed provider at n2: local ordinary helper named h uses existing X instead of H; control helper uses existing H | Positive F_2 and its phase-fixed H obligation | Actual finite X does not implement H, regardless of spelling |
| Ordinary Q<Bit> H artifact | Positive width1 request on Q<Bits<1>> | Complete basis constructor mismatch despite equal width |
| Ordinary Q<Unit> identity artifact | Zero identity-rewire request on Q<Bits<0>> | Unit/Bits0 constructor mismatch despite equal width |
| Zero-owner empty route, if expressible and freshly native-valid | One-owner Bits0 identity request | Complete logical-owner/interface mismatch |

The changed-provider source uses the existing ordinary source/import path and
sealed X/H primitives, with no new primitive or external-unitary annotation.
If replacing H prevents optional Fourier factoring and changes representation,
record the genuine first diagnostic as such. An artifact-level X-leaf mutation
that retains the shell can isolate the mandatory original finite-H obligation;
it is a separate test and needs its own fresh whole-artifact validity result.

Missing reversal at n1 is NOT a negative: reversal is already identity there.
A changed global phase is a meaningful failure even when measurement
probabilities agree. A type mismatch cannot be repaired by equal bit width,
implicit tuple/Bits casts, labels, lifetimes or function/algorithm names.
Record whether each failure comes from source checking, strict transport,
generic pair construction, native structure or exact finite obligations.
Do not manufacture a single expected error string for several different stages.

## Future fixed capture contract and remaining gates

Later authorized execution must preserve the first desired sources, explicit
schema2 [qrate].edition="2026" manifests, exact source/dependency/CLI/native
identities, commands, stdout/stderr/status, native-call logs, output/request
bytes and checksums. Freeze independent requests before mutation/request checks.
Bound every generated input to n0..3 and cap any loops from driver-owned constants;
artifact metadata is data and never an executable command selector.

Do not run scripts/test_sized_qft.py wholesale: even --small leaves unrelated
width9/out-of-scope negatives and an ignored Cargo helper in its main routine.
A later dedicated driver should call only the intended fixed tiny cases.
No maximum-size case or new quantum build is authorized by this design.

Additional meaningful checks, after the first exact request failures/successes
are retained, include explicit type-shape negatives above, phase/reversal
controls, missing and incompatible native executables without fallback,
unchanged input byte binding and separately authored small coefficient/reference
diagnostics. Numerical diagnostics can help locate errors but cannot replace
the exact request gate or discharge EXACT-2026-01.

General Fourier analytic meaning, source-to-output preservation, tuple QFT2/3
specialization equivalence under explicit E2(a,b)=a+2b and
E3((a,b),c)=a+2b+4c, all-input/reference proof, quantitative family/resource
certification and atomic canonical std namespace exposure remain outstanding.
The current root source work is common pattern checking; this packet grants
no completion credit for any #317 criterion.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
