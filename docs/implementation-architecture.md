# Implementation boundaries and maintenance

Map, not acceptance/correctness theorem. [Trust partition](../TRUST_BOUNDARY.md),
[language](language-spec.md) and [pipeline policy](lean-kernel-migration.md) are authoritative.
Raw mutations need renewed verification; numerical results are never equality oracles.

## Responsibilities and dependency direction

| Component | Responsibility/boundary |
| --- | --- |
| [IR](../src/ir.rs) | Untrusted data/IDs/effects/evidence; independent of source/execution. |
| [Verifier](../src/verify.rs) | Independently check raw IR, issue private immutable VerifiedProgram; no frontend/simulation acceptance. |
| [Contracts](../src/contract/mod.rs) | Exact circuit/encoding equations with bounded arithmetic, never numerical/source success. |
| [Function extractor](../src/contract/function.rs) | Independent raw-body comparison/full binding, separate from frontend flattening; shared immutable meanings survive transforms. |
| [Frontend](../src/frontend/mod.rs) | Parse/resolve/check declarations and emit untrusted IR; exact trees/declared effects stay source obligations. |
| [Documentation](../src/frontend/documentation.rs) | Syntax/span metadata only, unchanged AST, no evidence issuance. |
| [Simulator](../src/sim.rs) | Verified closed execution under separate limits; approximate numerical diagnostics. |
| [Host](../src/host.rs)/[CLI](../src/bin/qleisli.rs) | I/O, classical orchestration and algorithm success conditions outside acceptance. |
| [Lean](../lean/README.md)/[kernel](../lean-kernel/README.md) | Separate specified models/actual-definition component proofs; no automatic Rust correspondence. |

## Checked lowering

Preserve once-only source order, values/owners, locations, declared effects, fresh IDs
and work charges. Callee lexical scope excludes caller bindings, register store retains
caller/pending frames. [Values](../src/frontend/compile/lower/value.rs) retain empty-owner
slots and spent-name tombstones hiding globals; ownership is not separability.
[Scope](../src/frontend/compile/lower/scope.rs) restores binder identity/domain/footprint,
not value equality alone. [Branches](../src/frontend/compile/lower/branch.rs) preserve
freshness across both arms and merge complete result positions/frame slots including
Q<Unit>. [Primitives](../src/frontend/compile/lower/primitives.rs) explicitly consume/
replace owners; all emitted operations reverify. Certified bodies mask outer resources,
retain actual/logical circuits; snapshots establish attachment, not source adequacy.

## Traceability

Use actual modules/tests/independent analytic expectations and scoped inventory.
Existence links are not proofs; distinguish paper models, Lean components, native
comparisons and complete implementation claims. Split real responsibilities/interfaces,
not files for length. Convenience/runtime sharing changes no acceptance boundary.
