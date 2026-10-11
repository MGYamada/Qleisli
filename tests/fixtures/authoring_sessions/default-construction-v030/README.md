# Explicit construction and the Default boundary

This is an informed first-source study of the ordinary
[#79 decision](https://github.com/MGYamada/Qleisli/issues/79#issuecomment-6009973288)
for 0.3.0, in edition 2026. Six complete first projects and their predictions
precede the commands. Thirty actual public CLI calls are preserved: JSON and
default-renderer checks for every project in both phases, plus three successful
JSON runs in each phase. There are no source repairs or additional attempts.

| First project | Actual result before and after |
| --- | --- |
| `ordinary-default` | The ordinary helper returns `(Bit, Unit)`. Copy/ignore/wildcard use is permitted; run returns Bit 0 with weight 1. |
| `explicit-isometry-default` | The ordinary helper explicitly calls `init0`; measurement consumes its result. Check/run pass and return Bit 0 with weight 1. |
| `false-unitary-caller` | The caller falsely asserts Unitary around the Iso helper. Both phases reject with `effect`, at the complete `default()` call, bytes 284–293. |
| `unused-generic-default` | The unused Basis-generic body calls an unresolved name. Both phases reject `unknown_name` at the `default` callee, bytes 197–204. |
| `explicit-unit-default` | Selected check and scalar run pass. Explicit `unit(())`, `finish` and a fresh returned owner retain the preceding scalar; the zero-wire coefficient is approximately `(0.7071067811865476, 0.7071067811865476)`. |
| `nested-unit-wildcard` | An ordinary product contains a nested `Q<Unit>` owner. Both phases reject `ownership` at `_`, bytes 275–276, despite zero physical width. |

Only the unresolved-default explanation changes: it now mentions `Q<Unit>`
and quantum-containing products. The thirteen other matching observations
retain both raw streams exactly. All observed exits, diagnostic categories,
original spans, nonmessage results and three run outputs are equal. The existing
false-Unitary message continues to state that “externally unitary” is unsupported.

The selected Unit check without `--format=json` prints the existing legacy JSON
status body. Its original default-renderer transcript is retained; the `text`
filename denotes the command mode, not a claim of prose-only successful output.
The JSON wrapper and default command are both recorded, with their actual flags.

The fixed BEFORE executable is `/private/tmp/qleisli-rust-boundary-after`,
SHA-256 `d140ae375e1319f3cc353fe475178357355f921b5dae515a98a785b06ca8bb5d`.
The filename comes from the preceding #68 study. The separate AFTER executable
is `/private/tmp/qleisli-default-boundary-after`, SHA-256
`0340621153f39c92a9493c19c389039ccbae4f7ab43b5e742cd643428c428db7`.
Both phases select the same native bytes, SHA-256
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
The observer checks these identities around each call and checks the frozen
first-source/context/prediction inventory. It neither builds nor copies binaries.
Local hashes do not authenticate build provenance, child-start identity or
compiler/runtime correctness.

See [context](context.md), [prior predictions](predictions-before.json),
[before assessment](assessment-before.json), [comparison](comparison-after.json),
[session](session.json), [source inventory](first-files.json) and
[stream integrity](integrity.json). Raw stdout/stderr and exact argument lists
remain beside every observation. Commands are constructed in `capture.py`,
never replayed from historical records.

This is an informed code/specification observation, not a blind model benchmark,
independent exact oracle, trait implementation or formal proof. The scalar run
explicitly reports `producer-consistency` and `source_meaning_verified: false`;
it does not gain independent source semantics from its numerical agreement.
Existing exact Unit-map, reference and preparation tests remain separate evidence.
There is no implicit Default trait, hidden preparation/cleanup capability,
standalone release API, generic QFT or maximum-size experiment in this packet.
QS/PR/quantitative RS/EXACT broader obligations remain pending, and the two
ordinary decoded-QLV1 ownership/scope guarantees keep their recorded scope.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
