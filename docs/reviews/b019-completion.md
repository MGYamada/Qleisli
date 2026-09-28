# B019 completion and code-driven handoff

Date: 2026-09-28. Product: **0.1.9**, on
`codex/v0.1.9-review-fixes`, based on published 0.1.8 commit
`f36a57d0661eac4b9790925f59dc124a49cb5ff7`.

**Candidate preparation:** B019-1–5 have completed dispositions and local
validation. B019-6 still requires the clean committed candidate and its hosted
CI/distribution results below. This status will be updated from executed
results; selecting 0.1.9 or publishing an inventory does not close a gate.

The [initial assessment](b019-2026-09-28.md) and its frozen JSON/corpus report
remain historical evidence of the failed F2 case. The later user request was
to finish the finite B019 foundation in 0.1.x, then practice
[code-driven development](../code-driven-development.md) from 0.2.0 onward.
The acceptance conditions themselves have not been weakened.

## Six-condition disposition

| Gate | Disposition and evidence |
| --- | --- |
| B019-1: compatibility | Met. F1 repairs invalid StaticOp syntax under the existing grammar/X1 failure contract; valid source semantics are unchanged. F2 removes redundant private work/storage, with no public identity/IR/evidence/AST/Lean signature change, reduced capacity or raised toolchain. The [release record](../releases/v0.1.9.md) and [F2 note](b019-f2-resolution.md) retain before/after behavior, diagnostics and regressions. Historical 0.1.8 migrations remain historical. |
| B019-2: finite assurance | Met within the declared profile. Both Rust toolchains revalidate V01-C1–C6: unchanged substitutable clients, exact phase/output layout, complete owners including Unit, dependency identity, controlled composition and cleanup with correlated references. The independent [4,608-case exact sweep](../../tests/b019_trusted_boundary.rs) exercises retained operations, control polarity, all ordered axis placements and adjoints. Corpus interference/reference probes are additional approximate checks, not evidence issuance. |
| B019-3: audit dispositions | Met. Completed [frontend audit](b019-frontend-audit.md) and independent [trusted-boundary audit](b019-trusted-audit.md) cover all 20 inventory groups below. F1/F2 are resolved; F3 is consistent with current norms; F4/F5 are addressed; F6 is classified nonsemantic implementation debt. No discovered supported-contract defect is deferred as a future feature. Raw-only acceptance debt remains governed by its published contract and migration rule. |
| B019-4: proof ledger | Met as the specified ledger/audit condition. Paper/Lean/implementation/numerical assumptions remain separate in the [formal ledger](../formal-core.md), [source correspondence](../source-ir-correspondence.md) and [Lean ledger](../lean-resource-proof.md). Fresh Lean 4.30.0 build and 577-declaration audit pass with only the three permitted axioms. The historical [Physlib audit and reintroduction gate](../physlib-environment.md) remain explicit; no current Physlib dependency or new general compiler proof is claimed. |
| B019-5: selected next scope | Met. Six drafts/R01–R14, the complete fixed-width [M1 specification](../next-minor-spec.md), [machine interfaces](../machine-interface-spec.md), [M2 profile](../hierarchical-ir-spec.md), and [dated maintainer-owned bounded-kernel go decision](../decisions/2026-09-27-v1-path.md#scope-decision-and-dated-follow-up) supply the handoff. The 2026-10-04 JST readiness checkpoint is still prospective. CD-1–4 now identify actual source, oracles, failure experiments and dependency boundaries. Sized grammar and production M2 remain unfinished, as required by the plan. |
| B019-6: reproducibility | Local validation passed; exact committed candidate, Linux CI and clean distribution/source-archive results pending. The [distribution checker](../distribution-validation.md) requires a clean HEAD, exact Git bytes/modes and attribution, normal Cargo package verification, extracted locked metadata and fresh production/research tests from the complete archive. Its report identifies commit, tree, artifacts and executed commands. Tagging and publication are separate. |

## Inventory coverage and supported-contract findings

The numbering below follows the current [20-group inventory](../current-status.md#finite-rule-inventory).
That inventory supplies rule/implementation/test/proof links. These dispositions
come from the two completed source reviews, not from counting its rows.

| Inventory group | Completed review/disposition |
| --- | --- |
| 1. Ownership and exact product/Unit types | Frontend types/scopes plus independent verifier consumption, complete outputs and wire freshness. Closed. |
| 2. Declared effects | Frontend derivation/causal metadata plus raw effect verification and observation instruments. Closed. |
| 3. Names, scopes, spent bindings | Project resolution, lexical identity and scope-projection review; finite scope oracle. Closed. |
| 4. Complete branch/result/frame coverage | Source suspended arguments, both-arm lowering, raw phis and numerical relabeling. Closed. |
| 5. Static transformations | Phase, full output order, control/adjoint/repetition and transparent capabilities reviewed; independent exact sweep added. Closed. |
| 6. Basis computations and lifts | Full bounded domains, totality, injection and reference-preserving IR interpretation. Closed. |
| 7. Computed relations/cleanup | Restricted producer and every raw use; certified entry/binding and all exact leakage rows. Closed. |
| 8. Function evidence/dependencies | Both raw functions independently checked, full exact output operator, immutable binding and F2 sharing independently reviewed. Closed after F2 repair. |
| 9. Lexical grammar/errors | Complete constructor/EOF review and source-prefix sweeps. Closed after F1 repair. |
| 10. Modules/visibility/cycles | Sealed resolution, canonical roots, collision/cycle handling and all declarations. Closed under current loading policy. |
| 11. Preparation/wires/exits | Every verifier constructor, fresh allocation history, complete owner exits including zero-width tokens. Closed. |
| 12. Sealed gates/circuits/order | Exact matrices, monomial input-indexed phases, legacy adapter and full register order. Closed. |
| 13. Observation/SSA | Consuming instruments, hidden branch components, fresh reset, both-arm SSA and complete phis. Closed. |
| 14. Limits/numeric execution | Independent work/depth/width/metadata/expansion limits; source-retention regression fixed. Loader policy and floating arithmetic assumptions remain explicit. Closed. |
| 15. Descriptive documentation | Attachment/spans/Markdown reviewed; docs cannot alter IR or authorize ownership. Closed. |
| 16. JSON X1 | Escaping, result envelope, exits, Unicode locations, atomic output and independent decoder. Closed. |
| 17. Foreign-format connections | M1.1-A bounded import/export, ownership reconstruction and independent OpenQASM/LLVM checks. Closed within the terminal profile. |
| 18. Fixed-width operations/meanings | Generic parameter checking, concrete specializations, exact targets, constructor capability/meaning composition and all limits. Closed. |
| 19. Algorithm authoring/contracts | Bundled routines, source/failed-attempt corpus, QPE/reference instruments, finite arithmetic and host order recovery. Closed for the published finite routines. |
| 20. Basis patterns/tuple sugar | Binary AST normalization, full type trees, parameter binding, axis order and location/depth regressions. Closed. |

F2's old 40-provider input now passes both with and without the unrelated
25,003-byte module. Five private unit checks and three source integrations
demonstrate shared storage/work, 100 KB plus 25 KB of comments, 256 providers,
256 contract pairs, mixed consumers, exact dependency binding and unchanged
257-instance rejection. Per-receipt exact validation remains active. Explicit
legacy identity inspection is bounded and shared by receipt clones.

F3's transparent constructor behavior follows the current specification;
opaque-provider tightening belongs to A020-09 and requires its own migration.
Raw-only `QuantumIf`/`ProtectedUse`, duplicate type conversion and the compile
diagnostic sentinel retain published behavior. The reviews found no supported
semantic defect in those paths. Their inventory is not a claim that the trusted
acceptance base has been reduced.

## Local whole-candidate validation

Executed on macOS aarch64 after F2 and the exact sweep were integrated:

| Check | Result |
| --- | --- |
| Rust 1.98.1 and minimum 1.85.0 | **354 production and 43 research tests per toolchain**, all-target Clippy with warnings denied; primary formatting for both packages passed. Separate fresh Cargo targets were used. |
| CLI transport | Independent Python decoder: seven executed tests and one Linux-only skip per binary. Rust CLI/doc/JSON regressions also passed. |
| Lean/Mathlib 4.30.0 | Build passed with 1,457 jobs including cache hits; audit passed for 577 declarations using only `propext`, `Classical.choice`, `Quot.sound`. No proof source changed. |
| Input corpus | 24 mains, **9,412 semantic probes** and four local rejection cases passed; [live report](../../corpus/validation.json) binds source/manifest/oracle/compiler hashes. Old assessment's report is separately frozen. |
| Representative execution | All 14 example projects passed JSON check/run with independent decoding and distribution normalization. Shor15 reports period 4, factors 3/5 and success/retry weights 1/2 each. |
| External formats | Three independent OpenQASM-parser/LLVM syntax and profile tests passed with the newly built interop example. No device execution or complete-format claim. |

Document, helper, whitespace and archive checks are recorded against the final
candidate below rather than credited from a pre-edit tree.

## Candidate and distribution evidence

Pending the first clean commit of the implementation and these records. The
final entry must name an actual commit and successful exact-commit CI run,
record package/archive hashes and include the nested research package, proofs,
all frozen originals and source-specific notices. A dirty-tree package or the
old 0.1.8 HEAD cannot substitute for that candidate.

No tag, merge, hosted release or registry publication is claimed by this record.
Branch push and a reviewable pull request support candidate CI and are reported
separately from publishing the version.

## Handoff boundary

The [code-driven procedure](../code-driven-development.md) and A020-17–20
predeclare the obstacles to future claims. Remaining X2–X6, Python/QIR input,
adaptive connections, hierarchy/scaling, real sampling/retry, arithmetic and
v1 stabilization are not secretly completed by B019. Current source loading
also needs external experiment resource limits before unattended authoring;
future X6 is a separately reviewed MINOR policy change.

The closed three-source corpus/license policy, program-first principle,
retained failures, independent finite oracles and small trusted core are the
foundation for those cycles. General Rust soundness and absence of every
possible bug are not claims B019 can establish. A newly found current-contract
defect reopens maintenance rather than being excused by this handoff.
