# Verification migration through 0.2.2–0.2.9

Adopted staging supersedes old K1/K2 dates. VM22–26 are checked bounded components; VM27–29 open. Complete implementation/dual checking does not transfer authority: S05-C1–C5 required.

## Scope and starting point

Migrate arithmetic→finite equations→raw IR→hierarchy→transport/production. Rust parsing/diagnostics/generation/simulation/search remain outside the Mathlib-free kernel. Preserve every public path/raw-only form/capacity; validity APIs need no new caller algorithm contract. Requests are independent of artifact claims. Keep [VM22 inventory/comparison bytes](../tests/fixtures/verification_v022/README.md), small systems only/no new maxima.

### Target IR and reference semantics fixed before migration

Freeze serialization/domains/phase/meaning/encodings/limits/request binding first. R8/dyadic/mod256 need checked embeddings, no rounding/artifact-selected domain. Reuse one finite checker. Follow one-way [reference review](../TRUST_BOUNDARY.md#reference-specification-review-2026-09-30); Rust success flags/extracted conclusions/private handles are no evidence.

## Release packets and dependencies

| Packet / target | Deliverable and advancement gate |
| --- | --- |
| VM22 / 0.2.2 | Inventory every constructor/evidence/API/CLI/import/capacity with producer/consumer/meaning/replacement/positive-negative tests; packaging review adds no user dependency. |
| VM23 / 0.2.3 | Actual canonical bounded scalars/matrices/shared work with complex arithmetic/equality proof; phase/conjugation/normalization/overflow/work failures, never float or scalar-quotient equality. |
| VM24 / 0.2.4 | Decode/reconstruct U Ein=Eout u, full-space isometry/unitarity/cleanup; reject changed bytes/trees/axes/dependencies/requests. Raw extraction awaits VM25/26. |
| VM25 / 0.2.5 | Actual acceptance for every pure raw constructor: owners/types/effects/extraction/outputs/exact phase/reference cleanup; no Rust verifier/extractor premise. |
| VM26 / 0.2.6 | All raw constructors, observation/lexical SSA/branches/phis/frames/global freshness; actual pure operators/full instruments retain every outcome/residual/reference. |
| VM27 / 0.2.7 | Hierarchy finite/root/derivation/schema binding over same checker, independent roots/actual bodies/providers/encodings, no required Rust reader/equality premise. Enablement still needs R14/H1–H5/instrument gates. |
| VM28 / 0.2.8 | Audited native package/bounded transport/opt-in dual producer-consumer paths. Same immutable artifact/request; either rejection/disagreement/transport failure blocks. Bind execution/emission; clean distribution/platform checks. |
| VM29 / 0.2.9 | Coverage audit/reproducible selected production dual candidate; every public variant has Lean coverage or explicit blocker. Publish composed-proof/S05 readiness/review, never label incomplete replacement complete. |

Targets are dependent packets, not completion dates. Full scope includes RawProgram/QIRF/enabled hierarchy; breaks require MINOR.

### Completed components and remaining gates

[VM23](../tests/fixtures/verification_v023/README.md) actual arithmetic; [VM24](../tests/fixtures/verification_v024/README.md) finite equations; [VM25](../tests/fixtures/verification_v025/completion/README.md) eleven pure constructors/original complex/reference/cleanup/fresh attachments; [VM26](../tests/fixtures/verification_v026/README.md) all raw SSA/phi/branches, matrix-free original-complex CP/TNI/TP for arbitrary finite references. Twelve-bit structural capacity persists, reports experimental.

[VM27](../tests/fixtures/verification_v027/README.md) proves graph/root/reference and finite-leaf/pair/H discharge. Native-only reports need no Rust finite acceptance; compatibility reports rebuild handles with separate work. Decoder/small hierarchy/named-QPE comparisons are tests. Analytic reader→Operator, universal decoder/compiler, schema/source/runtime and production binding remain open.

[VM28](../tests/fixtures/verification_v028/README.md) connects original QIRF/request checking to opt-in ordinary CLI check/run/sample/emit-ir/verify-ir and a sealed dual report. Execution/emission uses the accepted bytes' reconstruction; no fallback. Fresh native bundle builds/audits/replays and relocated tests are implemented. Universal source/runtime correspondence, hierarchy closure, remaining public-path coverage and S05 remain open; this is a selected finite dual slice.

<a id="vm-22-inventory-and-one-bounded-comparison-harness"></a>
<a id="vm-23-exact-meanings-without-a-domain-change"></a>
<a id="vm-24-reconstruct-evidence-not-producer-conclusions"></a>
<a id="vm-25-pure-raw-ir-and-clean-auxiliary-release"></a>
<a id="vm-26-observing-instruments-and-complete-branches"></a>
<a id="vm-27-remove-transitional-hierarchy-premises"></a>
<a id="vm-28-bind-decisions-to-real-production-artifacts"></a>
<a id="vm-29-declare-the-actual-completed-and-open-scope"></a>
## Common acceptance and recording rules

PATCH compatibility/actual-definition proofs/source+compiled audits/independent small semantics and faults. [CI](../.github/ci/README.md) retains full replay for release/manual-full/policy risks. Bind records to sources/binaries; regenerate status. Shared QPE/source preservation/publication/S05/PR/RS are separate gates.
