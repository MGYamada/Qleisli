# Final source review of the CI repairs

Recorded 2026-10-06T00:48:23Z after reading the corrected working-tree diff.
The supplied constitutional continuity base is
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`; the constitutional startup check
passed in this review context. QS-2026-01, PR-2026-01, RS-2026-01 and
EXACT-2026-01 retain their pending duties. The two admitted ordinary QLV1
ownership/classical-scope guarantees retain their exact scopes and premises.

This is a read-only technical review of the product and test sources listed
below, followed only by creation of this new review record. No tests, builds,
native acceptance, workflow operations or semantic oracle were executed by
this reviewer. Results from the integrating agents are separate evidence.
This review adopts no interpretation, guarantee, source-preservation claim
or release approval. The earlier `review.md` and its hashes remain unchanged.

The reviewer previously authored the small `normalize.rs`/`sized/linear.rs`
formatting changes. Those two received a further consistency read here; that
is not an independent-author review of those changes. The rest of the listed
repair diff was reviewed independently of its authors. An integrator must
preserve that distinction when describing the review coverage.

No remaining actionable product/test defect was found in the reviewed diff.

## Resolution of the earlier findings

Capture explanation now runs only after the existing body checker returns an
ownership error. It adds no successful-path scope copy, hidden-binding map,
type traversal or work-budget charge. `local_use_at_span` requires exactly one
occurrence with the original error span and returns its recorded `BinderId`;
duplicate spans are ambiguous even when their targets agree. It neither
resolves by spelling nor changes the original lexical table. Decoration also
requires that exact binding to remain in the surrounding scope after source
evaluation. Spent source owners and shadowed body-local identities therefore
do not become outer captures. The original body evaluation, scope filtering,
effects, obligations, type comparisons and successful-path budget calls remain
in place. The post-rejection lookup and type traversal are charged and can
return a capacity error only after the program was already rejected.

Both Python all-body checkers now pass `hidden | {index}` into a fold body.
This prevents a static index from falling through to the same-named ordinary
definition, including zero-iteration bodies. Runtime parameters, let bindings,
static Naturals and actual Op formals retain their separate existing checks.
The new 16-method script test includes pure/instrument zero- and one-iteration
shadowing negatives and unshadowed structural positives; this review inspected
their source and does not assert their execution results.

Pattern diagnostics suggest `split` only when a quantum owner's immediate
basis is a binary tuple. They do not suggest it for Bit, Bits, Unit or a
nonbinary product. Empty patterns continue to accept only ordinary Unit.
These conditions do not introduce implicit splitting or coercion.

## Other reviewed contracts

Type mismatch rendering reuses canonical `Type::display`, retaining complete
tuple nesting, Q ownership and named Basis spelling. Symbolic Linear sizes are
rendered as affine source expressions, with overflow-safe signed magnitudes;
binder identity, exact size equality, the solver and Debug representation are
unchanged. Static Op and predicate diagnostics add the required Op/arrow
notation without replacing a limit or other non-type error. Explicit local
callee guards preserve the existing rejection of lexical values rather than
falling back to a global spelling.

Python local ordinary references use the declared module identity. Entry
compilation binds the exact registered source; ambiguous inferred identities
and stale explicit registrations reject. The producer's existing type,
ownership, effect, recursion and capacity checks still apply. This expands
untrusted source proposal construction, not the native acceptance authority.
The pure parser's quantum-only subset remains separate from the instrument
parser's additional ordinary values/effects.

The tests now distinguish complete common source checking from requested
concrete projection. Packaged `phase_eighth` retains its common exact Q<A>
contract, while the existing atom-only concrete scalar guard in
`sized/elaborate.rs` rejects a packaged tuple with a located unsupported error.
No scalar action or concrete capability was added. Selected coherent forms
that pass common checks still fail at their unsupported requested projection.
The changed specification negatives remain rejections: the common inferred
effect/annotation mismatch precedes the later injectivity check when the
coherent output width differs. The equal-width constant-table injectivity
negative and positive retained-input examples remain present.

The import-only cycle test retains the same 3,000 modules and small loader
stack and checks canonical back-edge identity/span; it follows the source
Reference's distinction from checked recursive declaration cycles. Diagnostic
regressions reuse existing sources or small bounded cases. Historical sources
and validation outputs were not rewritten by this review. Generic qft<N>
completion and the #317 namespace migration remain outside this repair review.

## Exact reviewed file identities

SHA-256 of the bytes read in this review:

| File | SHA-256 |
| --- | --- |
| `src/frontend/check/body.rs` | `d4ce8b4b67497fdaa1f172cba7a6174319fcb3834f380baff4c4c3d758adf9ef` |
| `src/frontend/check/body/operations.rs` | `cc10b70d978675f968fe30b340d55c9612dd18d10225643239e85a791a51d90a` |
| `src/frontend/check/body/special.rs` | `116245387985c10b013c46cf8dbadbd255c4ea59bab726461006ebd2208b3079` |
| `src/frontend/check/normalize.rs` | `bd8dfc2f928bee5415a232d4b220b03e2200cc88ebf27886aaaa850291a8c68f` |
| `src/frontend/resolve/locals.rs` | `01c50d14dc89756d4d4131a0bbb0a01d3bfe1c83fe54ea451d3f980195ad7ed4` |
| `src/frontend/sized/linear.rs` | `98a0d14d0052e2281cc4c4b07e41f92c933ff836eb43cb0eda285cc07a66874e` |
| `src/frontend/sized/elaborate.rs` | `b65fe34f7bffabc03e07534f7665905378cb30ecf067cf43057c232acbba4490` |
| `scripts/compile_sized_corpus.py` | `eb572c699dfdbcb1951e49ed583067667b4ff50cbfa890fba52826c9e88abd2d` |
| `scripts/compile_sized_instrument.py` | `7b7114990e0a9a34a7526d5904c0682971ac491bbdf6e1b10076294f303591ad` |
| `scripts/test_sized_local_resolution.py` | `76508e158b5a3462b138dcbefb99ba12c8d13c998fb63f8b7c633edf03d93576` |
| `tests/authoring_ergonomics.rs` | `1e6fb6ee38025d88d0cd0aee21a89ffb45cc06138b14c4d6ce7ec33d2fabf9ad` |
| `tests/project.rs` | `5c02c887115d0f437e993130eb101417dd8d1610703e2cb686165014c391e4a6` |
| `tests/quantum_tuple_unitors.rs` | `f9d090547e3bf063af9ad98dc0b472bdc731f527b80e71da1bccfbc1b8c9e570` |
| `tests/quantum_unit_maps.rs` | `0e6323ada15254786785eebb3afda498aa36db5af78b2c3801723c1d9f2953dd` |
| `tests/review_v024.rs` | `4457ef35e7709ec5a569af19b9680b6e67420d2abf5c2ca894135ede00a977af` |
| `tests/specification_boundaries.rs` | `aea7d3b6655e5895d163613c8431d5f7c9d8a834b23123b9cce27d6105414e5f` |
| `tests/unit_patterns.rs` | `c48703cea7f971dcc35f95239a7ad3f875914a68bd5dd683b2e9b820446fedfd` |
| `tests/repair_diagnostics.rs` | `b96cbeeed4df5d59508b3debc8be2e18e0bd65c0581ede9b32ebfe9528855c44` |

These hashes bind this source review, not a built binary, complete release
closure or passing gate. Current inventory/coverage regeneration and actual
Rust/Python/native validation remain the integrating agents' responsibility.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
