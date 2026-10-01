# Verification migration through 0.2.2–0.2.9

VM-22/23, the VM-24 finite component and [VM-25 straight-line pure raw checking](../tests/fixtures/verification_v025/completion/README.md) are implemented and checked. VM-26–29 retain classical branches/observation, hierarchy closure and production integration. Release [0.2.5](releases/v0.2.5.md) is published; the declared VM-25 profile is checked separately from later integration gates. The user assigned verification migration to 0.2.2–0.2.9, superseding the old K1/K2 dates. 0.2.9 targets complete implementation plus explicitly selected dual checking; Lean-only authority still requires v0.5 S05-C1–C5.

## Scope and starting point

Migrate acceptance outward: exact arithmetic, finite equations, pure/observing raw IR, hierarchy, transport and production integration. Rust parsing, diagnostics, producers, simulation and search remain outside the pure kernel. Preserve every public path/capacity; ordinary validity APIs need not gain a caller-supplied algorithm contract. Semantic requests stay independent of artifact claims. Preserve the frozen [VM-22 inventory](../tests/fixtures/verification_v022/README.md) and original comparison bytes. Validate small systems without generating maximum-size corpus cases.

| Existing surface | Actual starting point | Required replacement |
| --- | --- | --- |
| Exact arithmetic | [Rust exact kernel](../src/contract/exact.rs): canonical `Z[ζ8,1/2]`, bounded coefficients/matrices and shared work accounting | Mathlib-free executable arithmetic with proofs of canonical equality and complex interpretation; preserve published success/failure and capacity behavior. |
| Finite semantic evidence | [Contracts](../src/contract/mod.rs), [meaning adapter](../src/contract/meaning.rs), [function extractor](../src/contract/function.rs) and [finite reconstruction](../src/interchange/finite_leaf.rs) | Independently reconstruct actual operations and requested meanings; check encodings, full-space validity, phase, dependencies and cleanup. Rust success flags or private handles cannot become evidence. |
| Raw-IR verification | [`RawProgram`/`RawOp`](../src/ir.rs) and [`verify`](../src/verify.rs), including public raw-only compatibility forms | Total Lean checks for every published constructor, full ownership/effect interfaces, classical SSA, branches and final outputs, with actual-acceptance proofs. |
| Hierarchical verification | [Existing Lean conditional checker](../lean-kernel/QleisliKernel/Hierarchical/Conditional.lean) already checks structure and supported derivations; [host](../src/interchange/hierarchical.rs) still discharges explicit Rust finite-reader/equality obligations | Reuse audited definitions and constructed denotations; eliminate required Rust-checker premises, complete selected rules and bind an independent root request. Conditional reports are not production evidence. |
| Transport and execution binding | QIRF and experimental hierarchy/native protocols have bounded adapters; production `check`/`run` still use Rust | Independently decoded immutable artifacts and requests, reviewed result protocol, fail-closed integration and execution of the exact accepted artifact. |

## Release packets and dependencies

Targets are dependent work packets, not automatic completion dates. Public breaks require a MINOR. Full production coverage includes RawProgram/QIRF compatibility and every enabled hierarchy profile.

### Target IR and reference semantics fixed before migration

Freeze serialization, domains/phase interpretation, reference definitions, encodings, bounds and request binding before migration. R8, bounded dyadic phases and modulus-256 component models need explicit checked embeddings; no rounding or artifact-selected domain. Reuse the same finite checker in hierarchy. Reference semantics must follow the one-way [review policy](../TRUST_BOUNDARY.md#reference-specification-review-2026-09-30).

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

[VM-22 fixtures and inventory](../tests/fixtures/verification_v022/README.md) cover constructor/API/CLI/import/capacity producers, consumers, obligations and replacements, including raw-only variants, QuantumIf, broad ComputeUseUncompute and zero-width owners. CI detects drift; packaging remains separately selected.

### VM-23: exact meanings without a domain change

[VM-23](../tests/fixtures/verification_v023/README.md) proves actual bounded R8 scalar/matrix operations, canonical equality, complex interpretation, reference behavior, costs and failures. Signed-i128 and machine-index bounds stay compatible. It neither proves old Rust arithmetic nor adds a coefficient domain or production transport.

### VM-24: reconstruct evidence, not producer conclusions

[VM-24](../tests/fixtures/verification_v024/README.md) reconstructs original finite data and independently required equations, with full-space inverse/reference/clean-return laws. Actual RawProgram extraction remains VM-25/26; native graph accounting is experimental. A handle, hash, cached success or Rust acceptance flag is not evidence.

### VM-25: pure raw IR and clean auxiliary release

Cover every pure raw constructor: complete token/wire freshness and output coverage, exact interfaces/effects, injective lifts, structural changes, gates/control/ApplyUnitary, retained evidence and both computed forms with actual-body extraction. Prove phase/reference laws and exact cleanup factorization. Preserve raw legacy forms or independently validate a versioned adapter. Pure classical branches still need VM-26.

The [completed packet](../tests/fixtures/verification_v025/completion/README.md) covers all eleven straight-line pure constructors, complete owners/interfaces, actual extraction and independent complex raw action. General checking uses local finite equations for broad certified scopes and non-dense original protected uses; twelve-bit structural capacities remain. Actual acceptance proves exact zero return on arbitrary correlated amplitudes, complete fresh function-graph semantics and exact signature/body/name/source attachment, with literal and dependency-expanded capacity checks. Native comparisons cover the original trace, phase-exact matrices, actual Rust corpus prefixes and identity/capacity faults. Pure classical branches remain VM-26. The private component envelope is not production QIRF, source preservation or a transferred authority.

### VM-26: observing instruments and complete branches

Cover initialization, measurement/reset/discard, classical SSA and Boolean operations, branch scopes and complete classical/quantum phi/caller/frame interfaces. Keep seen IDs across exclusive arms, dead-owner nonrevival and Q<Unit>. Prove complete instruments on correlated systems: each outcome CP/TNI, summed TP, residual/reference states and hidden-history addition. Prove actual executable definitions, not only existing Resource/Phi projections.

### VM-27: remove transitional hierarchy premises

Connect exact/finite/raw results to actual shared hierarchy and constructed denotations. Discharge Rust finite-reader/equality premises, independently bind roots/providers/encodings and complete selected observing/transformation rules. QPE needs the full preparation/powers/inverse-QFT/readout instrument with completeness and retained target/reference. Keep zero-repeat body checking, phase, reversal, sharing and R14/H1–H5. External schemas remain disabled until their own gates pass.

### VM-28: bind decisions to real production artifacts

Bind both checkers to the same immutable complete artifact/request and bind execution/emission to accepted bytes. Audit packaging and provenance; reject either failure, disagreement, malformed/truncated/extra/stale result, absent/crashed/timed-out kernel. No fallback to Rust success in the dual path. Cover supported platforms and source/raw/QIRF/hierarchy/host producers and consumers.

### VM-29: declare the actual completed and open scope

Inventory every production dispatch/variant and complete Lean coverage, or record an unfinished blocker. Publish composed-proof and S05 readiness/review evidence; parity or an implementation-language change alone proves no theorem or authority transfer.

## Common acceptance and recording rules

Keep PATCH compatibility, Mathlib-free runtime, actual-definition proofs, strict source/compiled audits and independent small semantic/fault checks. Update project-status.json and regenerate both views; bind result records to actual source/binaries. Shared-QPE continuation, publication and general Soundness/Realizability/Resource Safety remain independent gates.
