# Original-source 72 comparison, review 01

**Status: completed read-only metadata/evidence follow-up, after root reported
the one-shot capture terminal exit 0.** No original record was rewritten. The
reviewer, `/root/isometry_cli_tests`, authored the common checker and this
additive driver. Recomputed file/stream identities and observed deltas are
separate from the author's interpretation of source policy; this is not an
independent review of the reviewer's own implementation.

## Verified actual records

The old capture is 72 checks: **18 success, 54 nonzero, 304 pre-execv forwarding
rows**. The new capture is **26 success, 46 nonzero, 260 forwarding rows**.
Every CLI capture spawned, returned 0 or 1, and recorded no operational error,
timeout or output-limit event. All 36 text/JSON counterpart pairs in each
capture agree in status and forwarding count. Each failed text diagnostic
matches the JSON code/message and original span; finite line/column values were
recomputed from the immutable original source bytes. All new refusals occur
with an empty forwarding journal.

The exact old `before/files.json` has 365 mapped members; the new
`observations/files.json` has 364. Every mapped byte count, SHA-256 and mode,
and exact directory membership excluding each map itself, matched. The new
map is SHA-256
`a03aed8c6cb8337286230479cbc25cf7ee35ce3a84a61bb25f6660fb5d2258cd`.
FIRST41, all 418 captured original-tree files, and the exact 18 directories
containing only `main.qli` and `Qargo.toml` are intact; all manifests remain
schema 2, edition 2026. Five capture-design files, 32 retained MSRV record files,
both binaries, 113 current source/std/Cargo context rows and 631 current MSRV
source/std/tests/corpus rows matched their captured identities.

The prospective input map and `identity.before.json` are byte-identical at
SHA-256 `db5e885f9a0803e17bdaed63194178df7d68c9fb2b6331f3dad0973d21af55d8`.
The final record retains the identical declared identity and reports unchanged
inputs. The fixed MSRV `attempt-09` has all nine terminal stage records at exit
0 and a completed CLI rebuild; its result record binds the observed CLI
`5f9512a1a14febbc5d88802287b61850682aa8088653631a68bc444704846abf`.
Native remains
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
The historical checkout marker `4d86a0975c6cd97fe5bb1cc71115a2180ad561d6`
is not compiled-HEAD attestation. Root's subsequent unrelated active docs and
metadata repairs were not falsely required to match historical captured docs;
the actual relevant source, stdlib, tests, originals, records and binaries were
checked. This audit executes no validation stage itself.

## Complete transition table

Each cell is **CLI exit / forwarding rows per presentation**, old then new.
The table represents both actual text and JSON calls, rather than an inferred
second presentation. Full 72 event identities, stream/journal equality and
actual JSON diagnostic fields are in `comparison.json`, bound to the two exact
file maps; no bulk raw log is duplicated.

| Original source | Finite old -> new | Selected-auto old -> new |
| --- | --- | --- |
| `mixed-qif-and-generic` | 1/0 -> 1/0 | 1/0 -> 0/1 |
| `private-zero-fold-owner` | 1/0 -> 1/0 | 1/0 -> 1/0 |
| `dead-arm-missing-adjoint` | 1/0 -> 1/0 | 1/0 -> 1/0 |
| `private-basis-valid` | 0/20 -> 0/20 | 1/0 -> 0/1 |
| `private-basis-bad-result` | 1/0 -> 1/0 | 1/0 -> 1/0 |
| `qif-formal-controlled` | 0/20 -> 0/20 | 1/0 -> 0/1 |
| `qif-formal-apply-only` | 1/0 -> 1/0 | 1/0 -> 1/0 |
| `qif-wrong-effect` | 1/3 -> 1/0 | 1/0 -> 1/0 |
| `qif-wrong-shape` | 1/3 -> 1/0 | 1/0 -> 1/0 |
| `computed-unary-predicate` | 0/21 -> 0/21 | 1/0 -> 0/1 |
| `computed-wrong-arity` | 1/1 -> 1/0 | 1/0 -> 1/0 |
| `owner-shadow-move-valid` | 0/21 -> 0/21 | 0/1 -> 0/1 |
| `owner-shadow-live-invalid` | 1/0 -> 1/0 | 1/0 -> 1/0 |
| `static-shadows-global-valid` | 0/21 -> 0/21 | 0/1 -> 0/1 |
| `runtime-shadows-static-policy` | 0/20 -> 1/0 | 1/0 -> 1/0 |
| `runtime-shadows-static-call-invalid` | 1/0 -> 1/0 | 1/0 -> 1/0 |
| `natural-runtime-shadow-invalid` | 1/0 -> 1/0 | 1/0 -> 1/0 |
| `bundled-import-control` | 0/20 -> 0/20 | 1/0 -> 0/1 |

There are ten reject-to-success calls, two success-to-reject calls, sixteen
success-to-success calls and forty-four reject-to-reject calls. Raw stdout
matches in 41 calls, stderr in 47, and journals in 54; all three streams match
in **22 calls**. These are observed equality counts, not a required parity gate.

## Source migration and native boundary

Five selected-auto source controls newly succeed in both presentations: mixed
qif/generic fold, valid private Basis, Controlled qif, unary computed predicate,
and imports of all four real bundles. **Every selected command chooses the
ordinary `main::main` returning Unit.** Complete source judgment now checks the
private/unused bodies and fixed bundles, then only the selected main
specialization is concretely/native checked. These records do not demonstrate
selected concrete lowering of the private qif or computed body, requested
generic specializations, or canonical generic std availability. Their success
JSON retains `source_meaning_verified: false`, `producer-consistency`,
`all-supplied-module-declarations` and `selected-specialization` scopes.

The finite static-Op shadow control deliberately changes from success to a
located type mismatch at the let binder, following the recorded ordinary #32
source policy. Existing selected name rejection remains, with narrower truthful
wording. The runtime-call shadow negative now rejects at that binder before the
later runtime-callee error. Natural shadow, dead-arm missing Adjoint and private
zero-fold duplicate-owner errors now precede former finite eligibility refusals.
The mixed *valid* Nat source still reaches the unchanged finite unsupported
Nat boundary. Legal RHS-before-rebind, static shadow of a global declaration,
and live-owner protection remain distinguishable by the preserved controls.

Private Basis result/arity, qif access, inferred effect and exact provider shape
now yield substantive selected source diagnostics before old projection
refusals. Existing finite categories and byte spans remain in their corresponding
semantic failures, with changed common wording as recorded. Effect diagnostics
still explicitly identify unsupported “externally unitary” claims as semantic
errors, with no GitHub Issue link. No annotation overrides the body effect.

Journal arithmetic is exact: old 300 ordinary QIRF and 4 hierarchy-request rows
become 246 ordinary QIRF and 14 hierarchy-request rows. The finite shadow policy
removes 40 rows, earlier finite effect/shape/arity errors remove 14, and the five
new selected main controls add 10: `304 - 40 - 14 + 10 = 260`. Every retained
journal argv is either `--qirf-native, 0.3.0-alpha` or
`--hierarchy-request-pending, 0.3.0-alpha`, for its actual profile.
**Rows are wrapper records immediately before execv; they are not independently
attested native starts/exits.** The wrapper does not capture native stdin
artifact/request bytes. Equal argv sequences or successful CLI results cannot
therefore prove IR byte parity, analytic meaning, or source preservation.

## Scope and untouched obligations

The guard passed against trusted
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. Applicable QS, PR, RS and EXACT
interpretations, both scoped ordinary QLV1 ownership/classical-scope guarantees,
and all pending proof/enforcement duties remain unchanged. This is an identity
check, not Lean replay or a human adequacy/adoption act.

The audit imported no fixture driver/helper and executed no recorded argv,
CLI/native call, test, Cargo/Lean build, network request, Git or Issue mutation.
An initial metadata inspection mistakenly treated FIRST files as a dict; its
AttributeError was corrected to the actual list schema before full verification.
It was not a captured test or harness failure. No maximum case, simulation,
independent functional oracle, proof, guarantee, Issue completion credit,
full CI or release-readiness claim is added. The finite all-declaration concrete
eligibility barrier and the selected temporary projection remain explicit
outstanding #32/#317 work. Source/IR/native/runtime preservation, exact cleanup,
PR emitted-artifact correspondence and quantitative RS are not established by
these 72 small check captures.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
