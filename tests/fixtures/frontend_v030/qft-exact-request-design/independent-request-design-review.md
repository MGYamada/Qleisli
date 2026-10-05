# QFT request design: author follow-up audit

Status: additive, non-normative **self-review**, not independent design approval.
The requested filename is retained for coordination. `context.json` identifies
`/root/isometry_cli_tests` as the observer who authored `draft-01.md`; this audit
is by that same agent. Root or a different author must supply independent review
before authorizing the proposed harness. No acceptance condition is adopted here.

This audit inspected the actual native API, transport, pure root checks,
producer shell and existing tests. It executed no Qleisli command, native check,
Cargo/Lean build, numerical probe or harness. No artifact, request or source
variant was generated or executed. The retained Issue snapshot and eight
first-map members remain unchanged. The accompanying inspected map describes a
bounded source subset, not complete runtime closure or compiled provenance.

## Confirmed contract and limits

The independent family remains
`F_n[y,x] = exp(+2*pi*i*x*y/2^n) / sqrt(2^n)`, with axis zero of weight one,
positive sign, fixed global phase and included output reversal. `F_0 = [+1]`
preserves one `Q<Bits<0>>` owner; it is distinct from `Q<Unit>` and from zero
logical owners. This equation comes from the stated mathematical contract,
not candidate normalization. Future execution is restricted to widths 0–3.

The ordinary licensed source remains the frozen `qft-family-v030` source. Its
current fixed std counterparts retain F001–F002 contracts in
`stdlib/src/transforms.qli`. No canonical generic std API, primitive, analytic
Fourier theorem, source-preservation theorem or Issue completion follows from
this audit. Broad QS/PR/quantitative RS and EXACT duties remain pending; the two
ordinary QLV1 ownership/scope guarantees are not extended by it.

`Kernel::inspect_native(payload)` and
`Kernel::check_against_native(payload, request)` separately decode immutable
inputs and invoke fresh native checking. The second dispatches a singleton
positive-width `qft` request through the QLF1/Fourier mode, otherwise through
generic graph pairing. Both require actual original finite-leaf obligations;
Fourier additionally uses Lean's mathematically fixed phase-sensitive H matrix
in `Protocol/HierarchicalFinite.lean::checkHadamards`. Rust's
`validate_hadamards` verifies transport coverage, not mathematical equality.
Returned payload/request bytes must equal the actual inputs supplied to each
fresh call. Prior inspection or a serialized receipt cannot authorize the next
request check.

The CLI's `emit-proposal` writes untrusted payload bytes without invoking a
kernel. Payload tables contain no original source identity. Association with
`transform::qft`, its manifest and dependencies is producer provenance; output
acceptance alone does not establish source preservation. First commands and
exact bytes must be captured before any successful-result claim.

## Tighten the adapter before implementation

The position-1 obstacle in the first draft is confirmed. The actual Rust shell
is `[enter, recursive_body, leave, reversal, optional_output_rename]`.
`FourierRoot.project` and bridge `wiring_order` treat position 1 as the recursive
body. Wrapping the entire original root at position 1 is a different structure.
The adapter must compose only the explicit phase-free canonical-to-original
rewire with the original enter, retain the original recursive body and suffix,
and append only an original-output-to-canonical label rewire. Renaming labels
preserves coordinate positions; it cannot insert the missing real reversal.
An unexpected emitted shell must preserve its real first failure instead of
being rewritten into a desired Fourier body.

The first draft's “record each old/new index and retained byte identity” needs a
precise delta rule. Keep the original complete bytes unchanged as a separate
input. Reindexed rows are not literally byte-identical: reference integers
change. For retained rows, permit only explicitly typed reference changes;
all interfaces, finite program/description bytes, phase values, structural
operations and non-reference numbers must remain identical. New rows may only
implement the specified phase-free boundary composition and its consistent
meaning/proof/encoding records. Retain per-table index maps and a checked list
of permitted deltas, not a global textual substitution of integers.

`Artifact.lean` defines four tables. Definition edges can reference definitions,
meanings and encodings; meaning edges reference meanings; encoding edges can
reference encodings or a compute definition. Proofs reference implementation,
meaning, both encodings, proof premises and every typed witness reference.
Entry implementation/proof references must also be remapped. Current producer
definition/meaning/proof row alignment is a producer invariant, while encodings
are separately deduplicated. Either handle the complete typed closure or assert
a fixed supported tag/reference subset and reject anything outside it. Do not
assume that one index map is valid for every table or that only definition
children determine liveness. Dropping the obsolete outer root must not strand
its proof/meaning/encoding rows or drop dependencies of the retained body.

## Fix zero-width representation before observing acceptance

Native named `qft(0)` is unsupported and must not be introduced by this harness.
The generic request is shape-sensitive: `Root.aligned` retains the rewire map
and literal constructor, and pairing rejects differing child arities before
native dispatch. `identity`, `rewire` and a sequence of rewires are distinct
requested structures even if they denote the same operator.

Choose and freeze one zero-width policy before request execution: preferably
the canonical single-owner, single-`bits(0)` identity **rewire**, with owner 0,
empty axes and no classical values, and owner permutation `[0]`. If the original
payload needs explicit label adaptation, decide in advance whether the adapter
is required to return that single rewire or a fixed three-rewire sequence with
a separately frozen matching request. Do not select a new request shape or
bind new header labels after a failure to obtain acceptance. Preserving the
first emitted zero payload and an unexpected-shape failure is itself useful.

## Negative cases must demonstrate the gate actually reached

Each mutant must freshly pass complete native inspection before it is called a
native-valid wrong implementation. Its consistent proposed meanings remain
untrusted and are never the independent expected request. The original positive
request bytes remain unchanged for every negative of that width.

- **Wrong phase, width 2:** a shell-preserving change from `j=1,k=2` to
  `j=2,k=2` changes pi/2 to pi and is within the current bounded angle range.
  Update only the candidate's own corresponding phase meaning and preserve
  consistent graph records. Fresh validity and actual unchanged-request rejection
  remain predictions until execution. A source variant can disable optional
  factoring; retain that earlier representation failure separately.
- **Missing reversal, width 2:** replace the actual reversal route with a
  well-typed identity route, updating its own meaning/proof and retaining the
  shell and all dependencies. Fresh validity must succeed before the suffix
  request rejection is claimed. At width 1 reversal already equals identity,
  so it is not a meaningful negative.
- **Changed provider:** an ordinary local helper named `h` implemented with
  existing X supplies a source-level spelling counterexample. It may stop
  factoring, so its rejection need not isolate H equality. A separate actual
  original-QIRF H-to-X leaf mutation, with its own consistent finite X
  description and unchanged shell, can target the mandatory independent H
  obligation only after fresh inspection succeeds. A name or copied provider
  summary is not evidence; no new primitive or external-unitary annotation is
  needed.
- **`Bit` versus `Bits<1>`:** a bare H leaf fails `FourierRoot.inspect`'s
  minimum outer arity before complete basis comparison. The first draft's row
  therefore does not isolate a type error. Use a fixed native-valid three-child
  phase-free-enter/H/phase-free-exit shell with complete `Bit` interfaces for an
  isolated header negative, or honestly retain the earlier shell rejection.
  Do not introduce an implicit cast to make the candidate pass.
- **`Unit` versus `Bits<0>`, or zero owners versus one:** use separately
  native-valid rewire artifacts with those exact headers against the same fixed
  `Bits<0>` rewire request. Equal physical width does not discharge complete
  type/owner equality. If a proposed zero-owner case is not expressible or
  valid, preserve that fact and do not count it as a native-valid negative.
- **Zero global phase:** a future phase-bearing sequence may have different
  child arity from the rewire request and reject in Rust pairing without a
  native request call. Capture that stage and call count; do not claim native
  exact-phase rejection or add a primitive merely to force a preferred result.

Missing/incompatible checker cases must fail without fallback and record the
actual error stage and native-call attempts. Fixed driver-owned paths, widths,
case names and argv must control execution; existing fixture metadata is data,
not a selector for executable commands.

## Remaining work and evidence boundary

The inspected ignored `native_fourier_request_faults` helper uses fixture-selected
paths plus transitional reconstruction, and the shared-powers helper includes
4096. `scripts/test_sized_qft.py` includes widths beyond 0–3 even in related
paths. None was run. A new narrow experiment must avoid invoking those broad
helpers and must freeze the source/manifests, adapter, independent requests,
mutants and command bounds before its first check.

Successful future request results would establish the existing exact structural
request and mandatory original finite obligations for those actual packets.
They would not establish the general analytic Fourier family, arbitrary-input
or source preservation, fixed-specialization equivalence, a new adopted rule,
standard-library exposure or a constitutional guarantee. Numerical reference
probes and their independent formulas remain separate approximate evidence.

Read-only discovery probes for non-existent guessed paths (including
`source_plan.rs` at the frontend root and `native_hierarchy.rs`) were not tests;
actual paths were discovered and inspected. No success is inferred from them.
The additive inspected-map check only validates metadata serialization and
frozen member/source hashes. It is not experiment execution or independent
approval of this self-review.
