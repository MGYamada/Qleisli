# Verification migration through 0.2.2–0.2.9

Status: **VM-22 implemented, 2026-09-30; VM-23–VM-29 pending**.
The user assigns the Rust-to-Lean verification migration to 0.2.2–0.2.9.
This replaces the earlier K1/0.3.0 and K2/0.4.0 implementation schedule in the
[migration policy](lean-kernel-migration.md#staged-migration). The current
version and latest published release are [0.2.2](releases/v0.2.2.md#successful-publication-2026-09-30).
The [frozen VM-22 baseline](../tests/fixtures/verification_v022/README.md)
records the implemented inventory, boundary contracts and small comparisons;
it enables no schema or production Lean authority.

The target by 0.2.9 is a Lean implementation of the complete existing public
verification surface, actual-definition component proofs, and an explicitly
selected production dual-checking path. The Rust verifier remains available
for compatibility and independent comparison. **Formal transfer to Lean-only
production acceptance still requires [S05-C1–C5](release-milestones.md#qleisli-soundness-theorem-v050),
with the Qleisli Soundness Theorem as the v0.5.0 milestone.** Implementation
migration, composed soundness, authority transfer and publication are separate.

## Scope and starting point

Move acceptance logic from the checking boundary outward toward its producers:
exact arithmetic and finite equations, raw-IR resource/effect verification,
hierarchical derivations, then transport and production integration. This is
the checking portion of the adopted backend-to-frontend migration direction.
Rust parsing, diagnostics, CLI/host APIs, evidence generation, simulation and
external synthesis search remain outside the pure acceptance core. Source
lowering, optimization and backend preservation remain K4 proof work.

Preserve the guarantees of each existing API. An ordinary raw-program check
establishes IR validity and effects; it need not gain an algorithm-specific
meaning contract. Where an API promises semantic equality, its logical request
must remain independent of the proposed artifact. Boundary reconstruction must
not invent a request from the producer's claimed meaning or force new caller
arguments onto a compatible public API.

| Existing surface | Actual starting point | Required replacement |
| --- | --- | --- |
| Exact arithmetic | [Rust exact kernel](../src/contract/exact.rs): canonical `Z[ζ8,1/2]`, bounded coefficients/matrices and shared work accounting | Mathlib-free executable arithmetic with proofs of canonical equality and complex interpretation; preserve published success/failure and capacity behavior. |
| Finite semantic evidence | [Contracts](../src/contract/mod.rs), [meaning adapter](../src/contract/meaning.rs), [function extractor](../src/contract/function.rs) and [finite reconstruction](../src/interchange/finite_leaf.rs) | Independently reconstruct actual operations and requested meanings; check encodings, full-space validity, phase, dependencies and cleanup. Rust success flags or private handles cannot become evidence. |
| Raw-IR verification | [`RawProgram`/`RawOp`](../src/ir.rs) and [`verify`](../src/verify.rs), including public raw-only compatibility forms | Total Lean checks for every published constructor, full ownership/effect interfaces, classical SSA, branches and final outputs, with actual-acceptance proofs. |
| Hierarchical verification | [Existing Lean conditional checker](../lean-kernel/QleisliKernel/Hierarchical/Conditional.lean) already checks structure and supported derivations; [host](../src/interchange/hierarchical.rs) still discharges explicit Rust finite-reader/equality obligations | Reuse audited definitions and constructed denotations; eliminate required Rust-checker premises, complete selected rules and bind an independent root request. Conditional reports are not production evidence. |
| Transport and execution binding | QIRF and experimental hierarchy/native protocols have bounded adapters; production `check`/`run` still use Rust | Independently decoded immutable artifacts and requests, reviewed result protocol, fail-closed integration and execution of the exact accepted artifact. |

The [36-case finite corpus](../corpus/README.md), four ownership/effect
rejections and twelve semantic faults are the current positive/negative
regression baseline, not a formal equivalence proof. Preserve the frozen three
upstreams and historical reports. Use the adopted [small-system validation
scope](v0.2.2-plan.md#remaining-validation-scope-small-qubit-systems-2026-09-30):
do not newly generate or check maximum-size corpus cases. Capacity compatibility
still needs explicit review and boundary checks using small data, arithmetic
tokens and malformed requests; it cannot be inferred from small semantic tests.

## Release packets and dependencies

The versions below are selected implementation targets, not automatic release
dates. Each packet starts from preserved `.qli` or raw-IR positive cases and
semantic counterexamples. Complete its prerequisite proofs/checks before
depending on its conclusions. If a gate remains open, carry the packet forward
and record that state; do not manufacture completion to keep the numbering.
Breaking public changes require a MINOR under [versioning](versioning.md).

### Target IR and reference semantics fixed before migration

**Review follow-up, 2026-09-30:** the v0.5 theorem must cover the complete
production profile family, including published `RawProgram`/QIRF compatibility
and each hierarchical profile actually enabled by that release. It is not a
theorem solely about the `PhaseWord` seed or solely about an expanded flat QFT.
Build one finite-leaf checker/interpretation layer (VM-23–26) and compose it
with actual shared hierarchy/call/repetition derivations (VM-27), so the finite
proofs are reused rather than discarded when production hierarchy is enabled.
No new union enum, wire tag or source API is adopted by this planning direction.

VM-22 must freeze each supported serialization, coefficient/phase interpretation,
input and output encoding, capacities, request binding and reference module.
VM-27 must close the bridge from actual hierarchical finite leaves to that same
checker, including the complete observing instrument. VM-29/S05 must list every
production dispatch path; neither silently omitting legacy raw variants nor
leaving a Rust finite-checker premise closes the theorem.

The [domain inventory](coefficient-domains.md#review-inventory-and-v03-decision)
separates R8 finite matrices, hierarchical dyadic phases and modulus-256
component proofs. Specify exact embeddings and reject unsupported crossings;
do not silently round, reduce a phase modulo the wrong domain or infer a domain
from the proposed artifact. The v0.3 specification review decides public domain
and IR changes, while VM-23 preserves current R8 behavior. General-width QFT
needs a size-dependent phase interpretation, not merely a larger width constant.

Reference denotations need independent review and staged separation under the
[specification policy](../TRUST_BOUNDARY.md#reference-specification-review-2026-09-30).
The phase-word definitions are separated now; existing `runFrom`/`realize`,
complex interpretation and future raw instrument definitions need the same
one-way import discipline before their acceptance proofs can become authority.

| Target | Main deliverable | Gate before the next dependent packet |
| --- | --- | --- |
| **0.2.2 / VM-22** | Freeze the existing acceptance inventory and boundary/request contracts; establish reproducible comparison fixtures. Retain the completed simple corpus augmentation. | Every public constructor, evidence form, API/CLI/import entry and capacity has a producer/consumer, semantic obligation, replacement packet and positive/negative test. Review the native packaging options without imposing a new user dependency. |
| **0.2.3 / VM-23** | Implement canonical exact scalars, matrices and shared bounded work in Lean. | Actual arithmetic/equality agrees with the complex interpretation; phase, conjugation, normalization, overflow and work failures are covered. No float or modulo-global-phase equality. |
| **0.2.4 / VM-24** | Migrate circuit/encoding equations and serialized finite evidence reconstruction. | Actual decoded circuits satisfy independently fixed `U E_in = E_out u`, full-space isometry/unitarity and cleanup equations. Changed bytes, type trees, axes, dependencies and requests reject. Raw-program extraction is completed by VM-25/26. |
| **0.2.5 / VM-25** | Migrate pure raw-IR ownership, typing, effects, actual finite extraction and structured cleanup. | Every pure constructor has an executable acceptance theorem, complete live-owner/output coverage, exact phase and reference/zero-return laws. No Rust verifier or extractor premise substitutes for the migrated checks. |
| **0.2.6 / VM-26** | Complete observation, classical SSA/branches and phi/frame verification. | All raw constructors are implemented; accepted pure/observing programs have the required operator/instrument semantics. All measurement outcomes and residual/reference states are retained; complete branch coverage and global freshness are proved. |
| **0.2.7 / VM-27** | Close hierarchical finite/root obligations and supported derivation/schema binding over the same Lean finite checker. | Independently requested roots bind to actual bodies/providers/encodings; no required Rust finite-reader/equality premise. A feature/schema remains disabled until its own R14/H1–H5 and instrument gates pass. |
| **0.2.8 / VM-28** | Integrate audited native packaging, bounded transport and opt-in dual verification into real producer/consumer paths. | Both checkers receive the same immutable artifact/request; either rejection, disagreement or transport failure blocks that path. Execution/emission binds to the checked artifact. Clean distribution and supported-platform checks pass. |
| **0.2.9 / VM-29** | Finish the coverage audit and reproducible migration candidate; exercise the complete Lean replacement through the selected production dual path. | Every published acceptance path and variant has Lean coverage or an explicitly recorded unfinished blocker. Publish composed-proof obligations and S05 readiness/review records. An incomplete replacement is reported as pending, never declared complete. |

### VM-22: inventory and one bounded comparison harness

**Implemented:** [inventory and fixtures](../tests/fixtures/verification_v022/README.md),
[coverage gate](../scripts/check_verification_inventory.py) and
[bounded comparison harness](../scripts/test_verification_baseline.py), enforced
in CI. Native packaging alternatives are reviewed but remain unselected.
Actual comparisons and their limits are in the
[execution record](../tests/fixtures/verification_v022/validation.json).

Inventory the full finite API, including `QuantumIf`, broad raw
`ComputeUseUncompute`, zero-width owners and both sides of function evidence;
absence of a source producer does not permit dropping published raw support.
Use the [producer/debt inventory](interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary)
to separate migration from future core reduction. Specify each boundary's
independent request, exact type tree, ordered ports, effects, phase/domain,
evidence/source dependency binding and byte/work limits before coding it.

Begin with SWAP/Fredkin, XOR/complement and RX/kickback, then existing contract,
Bell/feedback and hierarchy counterexamples. Save the source, actual diagnostics,
artifact/request and both decisions. The first implementation slice after this
inventory is VM-23 scalar normalization/equality and a fixed one-qubit H/T
circuit, rather than an entire new verifier at once. Planned packet identifiers
are work labels, not new public profiles, commands or wire tags.

### VM-23: exact meanings without a domain change

Define normalization, addition, multiplication, conjugation, equality and
matrix composition over the existing finite coefficient domain. Prove these
actual definitions agree with the separate complex interpretation, including
zero and scalar phase on `Unit`. Lean arbitrary-precision arithmetic does not
authorize unlimited inputs or alter Rust's published capacity behavior: specify
bounded intermediate operations, checked failure and aggregate work accounting.
Use Rust arithmetic plus independent mathematical identities as distinct
comparison paths, including signed extrema and denominator normalization.

The hierarchical dyadic-angle profile retains its separately specified
semantics. This packet does not make every M2 phase representable in the ζ8
finite domain, add an arbitrary coefficient domain or adopt approximation.

### VM-24: reconstruct evidence, not producer conclusions

Implement the finite matrix/circuit readers and encoding/contract checks in
Lean. Recheck controls, permutations, canonical coefficients, whole-space
isometry/unitarity, entry encodings and the independent logical operator.
Prove accepted equations imply the promised reference-preserving maps and
exact cleanup. Check complete payloads and dependency identities afresh;
an `Arc`, theorem ID, cached success or source name has no authority.

This packet establishes the finite circuit/equation layer. Evidence that refers
to a `RawProgram` also needs VM-25/26's independently checked extraction from
the actual raw body. Until then, retain that missing premise explicitly and
issue no production replacement seal for such evidence. Keep scalar/axis faults
and changed actual/logical payloads as regressions; coordinated mutations of
artifact and claim must still fail against the separate request.

### VM-25: pure raw IR and clean auxiliary release

Port token/wire/global freshness, ordered register interfaces, structural
type/effect checks, injective basis lifts, split/join and final live-output
coverage. Cover gates, coherent control, `ApplyUnitary`, retained contracts,
restricted `ComputeUseUncompute` and `CertifiedCompute` with actual-body
extraction. Preserve legacy raw forms through checking or a separately proved
adapter; valid output IR alone does not prove legacy translation preservation.

Connect resource transitions to pure operator semantics, including arbitrary
references, controls and scalar phases. Prove the exact factorization required
by clean release; ownership, scope exit and unitary names cannot discharge it.
Classical branches that contain pure operations still depend on VM-26's branch
checker; label VM-25's profile explicitly instead of silently skipping them.

### VM-26: observing instruments and complete branches

Implement initialization, destructive measurement, reset, discard, classical
constants/Boolean operations, branch scopes, classical/quantum phis and complete
caller/frame/output coverage. Preserve seen IDs across both exclusive arms,
fresh logical wires after reset, dead-owner nonrevival and `Q<Unit>` ownership.
Reuse the existing Resource/Phi mathematics as specifications, while proving
the actual executable checker rather than only those projections.

Interpret local observation on the entire correlated system. Prove branch
complete positivity and trace-nonincreasing behavior, summed trace preservation
and correct residual/reference state, with probabilistic addition of hidden
histories. Add partial Bell measurement/discard, reset, feedback and missing-phi
faults. Numerical distribution agreement alone is insufficient. This packet
finishes finite raw coverage and both actual/specification raw evidence readers.

### VM-27: remove transitional hierarchy premises

Connect VM-23–26 to the existing `Conditional`/`Root`/Fourier definitions and
constructed mathematical evaluator. Close full-byte finite H and meaning-pair
obligations with the Lean checker, then complete the selected non-diagonal,
transform, encoding and observing rules with actual-definition theorems. Preserve
shared DAGs, zero-repeat body checking, provider/control capability, phase,
outer reversal and independent root/entry binding; do not replace this with
global dense evaluation or an internal projection-only theorem.

For any enabled QPE schema, prove the actual preparation/controlled powers/
inverse-QFT/measurement instrument, retained target and arbitrary reference
behavior, and completeness under independently checked provider premises.
Existing external entries remain disabled until their full binding gates pass.
The [four shared-QPE source/integration packets](v0.2.2-plan.md#ordered-implementation-packets)
are dependent feature work across this continuation, not all a 0.2.2 release
prerequisite. Validate small instances; the prior maximum-size history remains
history. A pending feature is not completion of the original corpus goal.

### VM-28: bind decisions to real production artifacts

Specify and review the request/result decoder correspondence, bounded native
process behavior, executable provenance and immutable checked artifact lifetime.
Exercise source compilation, raw Rust embedding, finite QIRF and supported
hierarchy/import paths, including Python/foreign adapters that call the CLI.
The proposed dual path must bind both actual/specification functions and all
evidence, not just a normalized summary produced by Rust. Check truncation,
wrong version/profile, extra fields, stale responses, process absence/crash/
timeout and failure/result disagreement. No kernel failure can fall back to
Rust success inside this path. Cache keys require complete bound inputs;
untrusted cached success cannot bypass reconstruction.

Choose an additive explicit configuration and supported-platform distribution
design before public integration; this plan selects no flag or API name.
Keep the existing Rust-only installation/API behavior compatible during 0.2.x.
Making Lean mandatory, removing public Rust APIs, reducing capacity or raising
toolchain requirements needs a MINOR compatibility decision. Proof transport
and native/runtime assumptions remain visible, even after decoder proofs.

### VM-29: declare the actual completed and open scope

Audit all public variants, equation checks, import/host routes and artifact
lifetimes against VM-22's inventory. Re-run the small positive corpus, exact
phase/reference/cleanup faults, independent native comparisons and platform/
distribution failures on the same release candidate. Measure checking work,
representation size and failure behavior without claiming untested capacity.
Document Rust acceptance logic now duplicated only for compatibility/oracles;
do not delete public declarations or audited temporary proofs in a PATCH.

Publish the component-proof composition, remaining transport/native assumptions,
reproduction commands and S05-C1–C5 readiness ledger. Missing proof composition
or independent review keeps the relevant S05 gate open. Lean-only authority is
not inferred from parity or the migration version. The v0.3.0 type-system work
must extend/reprove the relevant migrated rules; v0.4.x prepares broader review
and contributions, and v0.5.0 establishes the theorem for its complete declared
production profile before formal transfer.

## Common acceptance and recording rules

Each packet record must identify the immutable inputs and independent request,
boundary IR, moved functions, enabled rule scope, actual-definition theorem,
explicit remaining premises and dependent packets. Record source/compiled
hashes, performed tests, diagnostics and skipped checks. Update
[project-status.json](project-status.json) and the corresponding release and
conformance records; regenerate the status with
`python3 scripts/check_docs.py --write-status`. Planned entries must never be
counted as executed results or schema enablement.

For kernel changes, run the applicable Rust regression suite and independent
native differential/mutation checks, both pinned Lean builds and audits, runtime
source policy, compiled declaration/import audit and fresh proof replay. Keep
Lean/Mathlib at 4.30.0, the runtime free of Mathlib/external Lake packages, and
the four executable escape hatches prohibited, including generated helpers.
Reuse current focused test scripts before adding another comparison framework.
Release validation follows the [release procedure](crates-io-release.md#release-sequence).

Parity tests detect migration defects; they do not prove equivalence or
soundness. Every migrated acceptance rule needs a semantic/evidence obligation
and proof about the actual executed definition. Unsupported, inconclusive,
limit and transport failures issue no evidence. Do not relax published type,
ownership, phase, clean-return or capacity contracts to get agreement.

The [fixed trust partition](../TRUST_BOUNDARY.md), M0–M5, R14/H1–H5 and the
v1 Physical Realizability/Resource Safety targets persist. This plan adds no
quantitative resource theorem, QLT implementation or backend synthesis promise
to 0.2.x. It authorizes planning; implementation resumption and release actions
remain separately recorded.
