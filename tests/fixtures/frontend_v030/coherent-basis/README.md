# Explicit coherent-basis syntax migration

[Issue #81](https://github.com/MGYamada/Qleisli/issues/81) adopts the
[Reference contract](../../../../docs/src/reference/coherent-basis.md):
`basis input as pattern { basis_expression }` replaces coherent `do/pure`.
The parser retains the same CoherentLift AST, checks and finite LiftBasis
lowering. No native definition, schema, public Rust signature, constitutional
text, guarantee or dependency version changes.

`source-map.json` records 48 separate current file derivatives with both
predecessor and current SHA-256 identities. The initial 42 links cover already
selected ordinary-type, predicate and namespace sources; six more cover
direct authoring-source consumers. Original sources, earlier translations,
diagnostics and proof fixtures stay unchanged. Two malformed reserved-function
first sources keep their earlier parse failure and are not rewritten.
`generation-before-validation.json` and `generation-direct-consumers-01.json`
retain the generation state before validation.

Rust and Python fixture helpers use the same strict, explicit selection chain.
The helper neither repairs arbitrary source nor establishes acceptance.
Direct static includes select their recorded derivatives. Whole-project
selection remains separate; this file map has no implicit project migration.
The two complete corpus snapshots have their own manifest selection and
validation in `corpus/migrations/coherent-basis-v030/`.

`implementation-01/parser-ast-comparison-01.json` records equality of all 48
full old/current parsed ASTs after erasing only source spans. The authored
driver builds the actual frozen/current parser, scanner, lexer and AST modules,
with their original documentation attachment function. This bounded comparison
is not a source-preservation theorem. The first source-identity inventory is
preserved before refreshing the parser identity; the frozen Bell example keeps
its original bytes under `before/examples/bell/bell.qli`.

The informed first-source controls and actual text/JSON observations are in
`tests/fixtures/authoring_sessions/coherent-basis-v030/`. Initial failures remain
beside follow-up repairs. Parser tests, existing semantic tests and actual
native-boundary executions have distinct records in `implementation-01/`.
The selected concrete CoherentLift projection and existing Unit-profile limits
remain unsupported; no compatibility alias or stronger emitter is claimed.

The maintainer explicitly excluded external qlippy diagnostic updates and
validation from this unit. Qleisli frontend/CLI diagnostics, Reference,
examples and Cargo Clippy remain in scope. The exclusion is not an integration
claim. Full QS, PR, quantitative RS, source/runtime correspondence and release
gates retain their separate obligations. GitHub remains the work tracker.

The final [integration record](implementation-01/integration-validation-01.json)
binds the changed sources to completed bounded checks. It preserves the first
Rust assertion failure, authored-oracle omission and their separate repairs,
and states skipped checks and retained concrete-profile limits. The two
independent finite corpus oracles use the unchanged mathematical runner and
its stated floating-point tolerance; their reports are not exact proofs.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
