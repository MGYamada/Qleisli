# B019 completion and code-driven handoff

Date: 2026-09-28. Product: **0.1.9**, on
`codex/v0.1.9-review-fixes`, based on published 0.1.8 commit
`f36a57d0661eac4b9790925f59dc124a49cb5ff7`.

**Result: all six B019 conditions are met for implementation candidate
`b657e236cc94c5023746df900d42da5bfa23ab96`.** Its clean archive checks and all
six exact-commit Linux CI jobs passed. This later documentation-only closure
records those observed results; its own containing commit must also pass CI
and distribution verification before handoff. No tag or publication is implied.

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
| B019-6: reproducibility | Met for the recorded candidate. Clean local distribution/source-archive checks and all six exact-commit Linux CI jobs passed; immutable run and artifact identities are below. The [distribution checker](../distribution-validation.md) requires a clean HEAD, exact Git bytes/modes and attribution, normal Cargo package verification, extracted locked metadata and fresh production/research tests from the complete archive. Its report identifies commit, tree, artifacts and executed commands. Tagging and publication are separate. |

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

Document/helper tests passed: 19 document, five authoring-record, nine corpus,
20 distribution, 18 imaginary-helper and 11 exact-helper tests. Record checking
validated three sessions/five snapshots/eleven observations. All 58 finite
mathematical checks and 39 exact assertions passed. Imaginary source was not
compiled. Generated status/references and full committed-tree whitespace also
passed in the candidate's Linux CI.

## Candidate and distribution evidence

The immutable [implementation candidate](https://github.com/MGYamada/Qleisli/commit/b657e236cc94c5023746df900d42da5bfa23ab96)
is bound to Git tree `c11f90014536733381f52bd468df4a8c08b084bd`. The
[exact-commit push CI](https://github.com/MGYamada/Qleisli/actions/runs/36416267580)
completed successfully: `rust`, `rust-msrv`, `lean`, `docs`, `interop`, and
`distribution`. The latter preserves its full report, command logs and archives
in the [distribution artifact](https://github.com/MGYamada/Qleisli/actions/runs/36416267580/artifacts/10968120963).
[Machine-readable evidence](b019-completion-evidence.json) records these
observed identities, local checks and explicitly unperformed publication actions.

The local clean distribution run passed against that same candidate:

| Artifact | Exact verified contents | SHA-256 for this local run |
| --- | --- | --- |
| Complete Git source tar | 675 files; every tracked byte/mode, including the eight nested research files, Lean roots/toolchain and all corpus attribution | `cbf887257e8af207a30a683972459b05e862ccc218a03f23a9e678d9b8ec8a05` |
| Production `.crate` | 670 files; normal Cargo build verification, original manifest, clean VCS identity, normalized metadata/locked inspection and exact non-generated payload | `b27034ca259098cb9209679c2968a90f6cf1171773931a0ea43f0dfb5a447f59` |

Both archives retain all 39 frozen upstream records, 48 final QLI source files
and required notices. Cargo excludes only the eight nested research files;
the complete archive excludes no tracked file. Its extracted sources freshly
passed 354 production and 43 research all-target tests. SHA-256 identifies these
particular local artifacts; cross-platform reproducible compiler output is not
claimed. The Linux distribution job independently repeated this procedure.

The [draft PR](https://github.com/MGYamada/Qleisli/pull/12) makes the candidate
reviewable. This completion record and wording corrections are a subsequent
**documentation-only** commit; implementation/tests/scripts/corpus/proofs stay
identical to the verified candidate. The containing commit's push CI and its
own distribution artifact are the final handoff evidence, rather than claiming
that the older candidate's archive hashes identify a later documentation tree.
This avoids a self-referential commit-hash claim inside its own source.

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
