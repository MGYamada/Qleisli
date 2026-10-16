# Dormant closed-Op contract first studies

These are informed studies, not blind benchmarks. They preserve all files from
two pre-repair experiment directories, including original source, pre-execution
predictions, full actual stdout/stderr, observations and four Rust snapshots.
This is a partial closed-Op study of exact scalar phase on `Unit`, with zero
authored qubits. Expression obligations remain outside this study, including
owner frames and clean workspace; it contains no Bit/ctrl experiment.

| Packet | Original files | Original bytes | Recorded results |
| --- | ---: | ---: | --- |
| `first-contracts.tar.gz` | 34 | 196,087 | 5 accepted, 1 contract refusal, 1 parser refusal |
| `followup-contracts.tar.gz` | 38 | 36,583 | 9 accepted |

The initial accepted cases include a correct unused checked operation, an
incorrect unused checked operation, its zero-power form and two partially
closed requests. Acceptance of the bad requests is retained as the observed
pre-repair problem. The direct bad control refused the exact contract
`U E_in = E_out u`. The original `deferred_left_bad_right` used `then(...)` and
failed parsing at `8:90`; that diagnostic is not semantic rejection. Its first
source and diagnostic remain unchanged. Separate follow-ups use `then_op`.

All nine follow-ups accepted: five intended refusal cases cover both composition
orders, reversed partial checked/implicit arguments and a bad request hidden in
a closed call. Four intended acceptance controls cover deferred-only,
deferred/closed composition and unused/direct correct phase requests. The
`expected_after_repair` fields are predictions, not the recorded outcomes or
evidence that the repair is complete. The plans retain `execution: not run`;
their separate observation records hold the later actual executions.

Each initial acceptance and the first eight follow-ups reported 22 native
decisions and one independent request, with two concrete local and nine bundled
roots. The direct correct phase control reported 24 decisions and one request,
with three local and nine bundled roots. These are the reported bounded native
checking scopes. Every accepted stream says the checker identity is unpinned,
the entry is absent/not applicable and source preservation is not proved.

Both studies identify CLI SHA-256
`c0bdb167737522fc13f8be5f392fbe40d332d7d152a1adc24bf21a25ed0f02b6`
and kernel SHA-256
`54c9d60b80f67217abd95c8fe6ec1c06aa262e142d5e6db30f46a20cb90faf07`.
The observed source HEAD is `c3b463072dad16b4f082dcc49cf34263b2543dfa`;
it is a separate observation of the working tree, not a binary build identity.
The CLI is a prior build, not a clean commit-to-binary build attestation.
The four Rust snapshots and their complete follow-up before/after hash map are
provenance, not complete build inputs or proof of that binary's origin. No
binary is stored. Recorded wall times do not establish a performance bound.

`packets.json` records every original path, byte count, SHA-256 and mode (`0644`),
plus each compressed and expanded container identity. USTAR records contain
only regular files, ordered by path components, with fixed mode, zero uid/gid
and timestamp, empty owner/link fields and no extensions. Gzip uses an empty
filename and zero timestamp. The two packets retain 72 originals / 232,670
bytes; existing aggregate limits remain 80 files / 5 MiB expanded and 2 MiB
compressed. Original directory names are historical provenance, never inputs
to command replay or filesystem extraction.

`scripts/test_generic_dormant_first.py` reads this history as bounded inert data
and checks identities, inputs, stream associations, outcomes and disclosures.
It never executes recorded commands. No source/native/runtime preservation proof,
general dormant-obligation discharge, QS/PR/quantitative RS/EXACT discharge or
release claim follows from this history; it grants no issue completion.
