# Quantum Unit first-source observations

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

Fourteen informed projects were frozen before the first check: six desired
Q<Unit> flows, six deliberate type/ownership counterexamples, and two controls.
`first-files.json` fixes all 32 initial files, including each schema-2,
edition-2026 manifest, context and independent intended laws. Its SHA-256 is
`620ff262140a6604c12356233e0759c59b8ee0fbe00312c7799e16dba9de5e67`.
No source repair occurred.

The existing CLI was reused without a build or binary copy. `identity-before.json`
binds baseline c89871fa490807c12150d70fdbac5c28763ae88b, CLI
`e8dc6a969d9a58ebb9b3f32b2307a36d0fb24679492f0ce086a397434159303e`
and native checker
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
All 234 files in the prior actual MSRV build's selected manifest matched before
observation. A separate 103-file tracked src/stdlib/Cargo inventory and both
binary hashes remained unchanged across these observations. This is identity
evidence, not a complete compiler/dependency attestation or fresh build.

The 28 actual checks have separate immutable observation files:

| Route | Success | Rejection | What was observed |
| --- | ---: | ---: | --- |
| Selected `main::f` | 2 | 12 | Ordinary Unit copy and Q<Bits<0>> identity reach native hierarchy checking. Every Q<Unit> case rejects at the existing sized basis projection. |
| Finite project | 6 | 8 | Q<Unit> identity, helper, ordered Unit/Bit result, phase_eighth wrapper, Apply provider and ordinary Unit control pass. Quantum duplication, loss and wildcard reject for ownership; Bits, controlled-call form and static fold encounter finite-profile limits. |

The selected errors do not establish the intended downstream ownership/type
rejections: the profile limitation masks them. Likewise, the finite Bits and
zero-fold errors do not check the desired exact-type or zero-iteration-body
judgment. `baseline-summary.json` retains the actual codes and messages.

Each finite project has an empty nullary `main` to satisfy that route's entry
convention. Its check verifies the complete source declarations and the produced
main artifact; it does not execute the open function f or independently observe
its scalar coefficient. The selected checks target f and report their native
scope explicitly. This packet runs no state, matrix, sampling or reference
experiment. Existing finite scalar/control semantic regressions remain separate
evidence in `tests/unit_patterns.rs`; `expectations.json` states intended laws,
not newly observed coefficients.

Provider and control syntax is the existing Op/Apply/Controlled syntax applied
to the desired Unit basis. This study adopts no new primitive semantics,
unit/finish names, implicit conversions, native rules or guarantees. It uses at
most one physical qubit, adds no corpus translation and performs no Rust/Lean
build or maximum-size case. Issue completion and release readiness remain
separate.
