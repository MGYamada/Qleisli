# Verification migration through 0.2.2–0.2.9

VM-22–25 are checked components. [VM-26](../tests/fixtures/verification_v026/README.md)
completes observation/SSA/branch checking, original complex refinement,
matrix-free CP/TNI/TP and retained branch-functions.
The adopted 0.2.2–0.2.9 staging supersedes K1/K2 dates. VM-29 targets complete
implementation and selected dual checking; Lean-only authority requires S05-C1–C5.

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

### Completed components and remaining gates

[VM-22](../tests/fixtures/verification_v022/README.md) freezes the full constructor/
producer/API/CLI/capacity inventory and comparison bytes. [VM-23](../tests/fixtures/verification_v023/README.md)
proves actual bounded canonical arithmetic/complex interpretation. [VM-24](../tests/fixtures/verification_v024/README.md)
reconstructs actual finite equations; original RawProgram extraction is separate.
[VM-25](../tests/fixtures/verification_v025/completion/README.md) proves all eleven
straight-line pure constructors against independent original-operation traces,
complete owners/interfaces, phase/reference action, actual cleanup for correlated
inputs, and fresh function graphs with full body/name/source attachment. Broad
certified scopes use local finite equations, protected uses non-dense coefficient
semantics; twelve-bit structural capacities remain. Native reports are experimental,
not production QIRF authority. Pure classical branches remain VM-26.

VM-26 now checks all raw constructors, global IDs across both arms, lexical SSA,
zero owners and complete phis. The actual finite Kraus sum proves CP/TNI per
selected outcome and TP overall, retaining hidden and residual/reference states.
Matrix-free coefficient evaluation proves original complex refinement and
general finite-reference CP/TNI/TP; fresh retained functions include closed
classical branches. VM-26 is checked. VM-27–29 retain hierarchy/root closure,
native/decoder correspondence, immutable-artifact dual integration and full
coverage audit. General source preservation and S05 remain separate.

<a id="vm-22-inventory-and-one-bounded-comparison-harness"></a>
<a id="vm-23-exact-meanings-without-a-domain-change"></a>
<a id="vm-24-reconstruct-evidence-not-producer-conclusions"></a>
<a id="vm-25-pure-raw-ir-and-clean-auxiliary-release"></a>
<a id="vm-26-observing-instruments-and-complete-branches"></a>
<a id="vm-27-remove-transitional-hierarchy-premises"></a>
<a id="vm-28-bind-decisions-to-real-production-artifacts"></a>
<a id="vm-29-declare-the-actual-completed-and-open-scope"></a>

## Common acceptance and recording rules

Keep PATCH compatibility, Mathlib-free runtime, actual-definition proofs, strict source/compiled audits and independent small semantic/fault checks. Update project-status.json and regenerate both views; bind result records to actual source/binaries. Shared-QPE continuation, publication and general Soundness/Realizability/Resource Safety remain independent gates.
