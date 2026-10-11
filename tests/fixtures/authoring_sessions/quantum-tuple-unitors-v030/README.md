# Packaged quantum products and explicit unitors: first-source study

Twenty-two informed complete projects precede implementation of the recorded
[#43 contract](contract.md). They use existing source spelling and preserve
desired left/right maps, round trips, nested bases, an exact tuple operation
provider, a separated Unit scalar, coherent control, ordered axes and explicit
counterexamples. They are not a blind authoring benchmark or new corpus work.
No source was repaired. Every project uses at most two physical system qubits.

The 48 original files are bound by `first-files.json`, SHA-256
`8ac863aee3b2c4b8dcd4491b128c95136684550461ee8fb20a0488b2fc88ae2f`.
They contain all source/manifests, context, independent expected laws, the exact
Issue section and the pre-observation identity record. All Qargo manifests use
schema 2 and edition 2026. The current branch commit at authoring was
`9a1ecef79f2f1e42f94093b6f4822f282f6e9129`.

## Original observation and observer replacement

The first 44 checks reused the Unit-map CLI identified by
`quantum-unit-maps/cli-first`, SHA-256
`59ccb6a0fa2669fb11090c3daf5d38a6c39a74caa2c632d0a26a84aec05a236d`.
Of that historical record's 144 selected inputs, 143 still matched; the sole
file difference was the subsequently added private `cfg(test)` preservation
counterexample in `sized/lower/preservation.rs`. The old manifest and executable
identity were not rewritten to claim a new build or all-input equality.

While the observer was running, the parent task ran five existing regression
tests with Cargo against the shared target. Cargo also replaced its CLI binary.
The observer's final identity assertion failed. `observations/` retains all 44
original command records, and `identity-after.json` explicitly records failure.
The per-command `binary_sha256` in that first run was captured **after** its
command. The replacement occurred during the `tuple-provider-finite` command;
that record does not conclusively identify which executable was mapped at
launch. The first 15 post-command hashes are the old CLI and the remaining 29
are the replacement. No first result or source was overwritten.

## Stable appended baseline

After the parent finished Cargo and agreed to keep the executable fixed, the
same 44 checks were repeated under SHA-256
`f9b3d297bf751e79510b51d949f8129c2f0cab1113d62526a7c579a9d382b34c`.
The parent's actual `type-pattern-classification/{commands,sources,result}.json`
records identify that final MSRV 1.85 run; their hashes are retained in
`stable-repeat/identity-before.json`. This is recorded command/input provenance,
not exhaustive dependency or compiler attestation. This observer performed no
build. `stable-repeat/` preserves each repeated observation and checks the CLI
hash before and after **every** invocation.

The native checker remained
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
All 101 selected current production sources and every first file remained
unchanged through both runs. All 44 repeated stdout strings and exit statuses
match their corresponding first observations; that agreement does not repair
the first run's executable-identity limitation.

| Route | Success | Rejection | Actual result |
| --- | ---: | ---: | --- |
| Selected hierarchy `main::f` | 1 | 21 | The unchanged H-H atom control passes. Every packaged tuple project stops at the current Unit/Bit/Bits quantum-basis restriction. |
| Finite project | 5 | 17 | Tuple provider, ordered-axis example, coherent unitors, split/join round trip and atom control pass. Twelve stop at absent finite unit/finish names; three reach distinct type/ownership/effect errors; two stop at finite static/fold profile restrictions. |

Unsupported/import failures do not demonstrate the intended downstream type,
arity, owner, effect or generic-body rejection. The `lost-revived-owners`,
`wrong-arities` and `unused-zero-fold` projects intentionally contain multiple
invalid declarations; the first error masks siblings. They need isolated
follow-up validation. All selected checks retain all supplied declarations.
Each finite project uses an empty nullary observe main: its check does not
execute the open function, establish its operator, or test a reference state.

`expectations.json` records mathematical targets authored before execution:
canonical unitor coefficient +1, exact tree and ordered axes, omega retained
after Unit elimination, controlled fourth power equal to Z, and identity on
arbitrary external references. No coefficient or reference law is established
by the checks in this packet. The planned exact requests and valid-but-wrong
native counterexamples belong to later independent tests.

`session.json` links all 88 observations to the unchanged first source attempt.
`baseline-summary.json` records only actual outcomes and the original/stable
comparison. The two observer scripts are preserved for provenance; no checker
executes commands from these records. `files.json` binds this completed packet.
Future observations or repairs require separate paths. This study admits no
guarantee, closes no Issue and claims no source theorem, fresh Lean replay,
full profile parity, full CI or release readiness.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
