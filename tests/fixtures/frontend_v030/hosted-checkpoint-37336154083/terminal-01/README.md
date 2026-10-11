# Terminal hosted checkpoint: run 37336154083

This additive independent GitHub-connector readback records
[run 37336154083](https://github.com/MGYamada/Qleisli/actions/runs/37336154083)
as **completed/success**, attempt 1, updated at 2026-10-05T18:59:12Z.
The richer jobs API returns all 18 rows (`total_count = 18`). All eight
validation producers, all eight required contexts and `changes` succeeded;
`release-readiness` was skipped. The original nonterminal checkpoint and its
19 files remain unchanged; before/after hashes, bytes and modes are retained.

| Producer (success) | Job ID | Required context (success) | Job ID |
| --- | --- | --- | --- |
| check-docs | 111851435760 | docs | 111932054253 |
| check-rust-msrv | 111851435782 | rust-msrv | 111932054098 |
| check-lean-kernel | 111851435887 | lean-kernel | 111932054171 |
| check-distribution | 111851435909 | distribution | 111932054082 |
| check-interop | 111851435941 | interop | 111932054080 |
| check-macos-source | 111851435978 | macos-source | 111932054245 |
| check-rust | 111851435989 | rust | 111932054087 |
| check-lean | 111851436073 | lean | 111932054276 |

The other two terminal IDs are `changes` 111851329117 (success) and
`release-readiness` 111932055584 (skipped). The workflow's single `required`
matrix expands into the eight named contexts above.

The workflow run and job metadata name published PR head
`9256fe9ef4ffa722066b0569ee37341cf65dea0d`. All 17 completed-job checkout
logs and all eight required gates independently bind the **tested merge**
`7549cecca246b9335a3e1b8f9e4a176df8827d0a`. Its ordered parents are base
`ba83c5c97a9c67bf3904423745b3e9c019a083cb`, then that published head.
This run does not validate later local commits or source edits, including
the subsequent common frontend and Formals work. It cannot be reported as
CI for the later locally committed `7e04f20f0c908fd56720a50655bc56c072c80ceb`.

The selected suites and proof lane were both `full`. Kernel proof reduction
and fresh `QleisliKernel`/`Main` replay, the native comparison lane, and
relocated Linux/macOS bundle full replay succeeded. Both bundle logs record
267 process checks and 84 small corpus clients. Full schema type/audit
rebinding and registered guarantee replay also succeeded. The **model-only**
"Compile changed mathematical proofs and audit their declarations" step was
skipped under this full selection; this does not mean the full replay steps
were skipped. Per-command Cargo ignored rows remain separately visible;
some are explicitly rerun by other producers, so they are not reported as
a global list of untested features.

All 16 producer release-receipt/receipt-upload steps were skipped. Seven
required-context evidence uploads were skipped; the docs context retained
the shared required-check report. The release-readiness job did not run.
Successful selected CI establishes no release readiness, new guarantee,
human adoption, source/runtime preservation, broader QS/PR/RS discharge,
Issue completion or publication.

[Observed results and skips](observed-results-and-skips.json) retain every
terminal ID, actual completion time, skipped step and selected relevant log
line. [Checkout and gates](checkout-and-gates.json) preserve the exact source
binding. [Requests](requests.json), API metadata and the tested workflow
record their provenance. JSON objects are serialized returned data, not
original HTTP-response bytes. The merge record is an explicit projection;
its 300 returned changed-file patch rows are omitted.

All 17 connector-decoded logs were independently fetched and checked.
[Log identities](connector-returned-identities.json) and
[retained artifacts](log-artifacts.json) bind 2,071,956 decoded UTF-8 bytes,
including BOM, timestamps, ANSI escapes and whitespace. Six identical logs
reuse the historical gzip files by byte equality; eleven new deterministic
gzip files total 137,519 bytes. No archive artifact or original HTTP ZIP was
downloaded. Only new digest-verified temporary decoded copies were removed.

The first local data-audit assertion incorrectly compared unexpanded YAML
job IDs with matrix display names. Its real failure and corrected initial
diagnostic guess are preserved in [attempt 01](data-audit-attempt-01.json).
The matrix-aware [attempt 02](data-audit-attempt-02.json) passed all identity,
checkout, gate and compression assertions. These were metadata operations;
no local build, test, CLI/native execution, Git or GitHub mutation occurred.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
