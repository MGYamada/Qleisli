# Classical-function reuse observations

This informed study follows the human-selected `classical fn`
[ordinary decision](https://github.com/MGYamada/Qleisli/issues/22#issuecomment-6010679334)
for edition 2026. Four complete first projects and their predictions were
preserved before implementation. Their bodies differ from the separate
[withdrawn Basis proposal](../basis-runtime-v030/README.md) only in the
declaration keyword; neither collection rewrites the other.

Twenty-one actual public CLI observations are retained: eight BEFORE checks,
eight AFTER checks and five AFTER runs. All calls use `--format=json` with
their actual finite-directory or selected-entry arguments. The sources are
unchanged between phases; there are zero source repairs.

| First project | Actual BEFORE | Actual AFTER |
| --- | --- | --- |
| `shared-flip` | Both checks reject the unavailable declaration keyword. | Finite check/run pass and return `(1,0)` with probability 1. Selected check rejects the coherent `basis` expression with `unsupported`, bytes 224–254; no selected run was attempted. |
| `ordinary-and` | Both checks reject the declaration keyword. | Both checks/runs pass; ordinary noninjective AND returns Bit 0 with probability 1. |
| `nested-label` | Both checks reject the declaration keyword. | Both checks/runs pass; a measured Bit in the exact nested Unit/product argument returns Bit 0 with probability 1. |
| `quantum-argument` | Both checks reject the declaration keyword before reaching the argument. | Finite `type_mismatch` and selected `type` reject bytes 176–177: expected `Bit`, found `Q<Bit>`. |

The BEFORE parser errors cannot establish downstream type, owner, effect or
coherent-lift conditions. The AFTER ordinary-call successes do not eliminate
the selected coherent-lift profile restriction. Independent exact phase,
reference, effect, arity, shape, lexical and visibility controls belong to the
separate [Rust tests](../../../classical_functions.rs); the five run outputs
here are bounded observations against the prior predictions, not a general
semantic oracle or a report that those tests passed.

The fixed BEFORE executable is `/private/tmp/qleisli-default-boundary-after`,
SHA-256 `0340621153f39c92a9493c19c389039ccbae4f7ab43b5e742cd643428c428db7`.
The separate AFTER executable is `/private/tmp/qleisli-classical-functions-after`,
SHA-256 `8291ddad7119af45ec24fe6c1a9266384470b4d0556ebedd6c0c87b710844e5a`.
Both phases select the same native bytes, SHA-256
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
Every observation retains identities before and after the call, raw stream
paths/hashes, arguments, timestamp and exit status. Local hashes do not
authenticate build provenance, child-start identity or compiler correctness.

See the unchanged [prior context and predictions](context.md),
[first-source inventory](first-files.json), [BEFORE capture](observations-before/capture.json),
[AFTER capture](observations-after/capture.json), [assessment](assessment.json)
and [registered session](session.json). Raw stdout/stderr remain beside each
observation. Registration checks these records; it does not replay their commands.

Selected successful observations disclose `native-validity`,
`source_steps_checked: true` and `source_meaning_verified: false`. This study
is not a blind or few-example model benchmark, full CI result, general source
preservation/resource theorem, Issue completion or new guarantee. Broader
QS/PR/quantitative RS/EXACT duties remain pending; the two ordinary decoded-QLV1
ownership/scope guarantees retain their recorded scope. No generic QFT or
maximum-size experiment is included.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
