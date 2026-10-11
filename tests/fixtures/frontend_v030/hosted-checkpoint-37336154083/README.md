# Hosted checkpoint: run 37336154083

This records one nonterminal pull-request CI snapshot for the previously published
head `9256fe9ef4ffa722066b0569ee37341cf65dea0d`, captured through the GitHub
connector on 2026-10-05. It does not validate the later local SourceCollection
implementation or the later QFT authoring records.

The complete checkout logs show that the runner actually tested merge
`7549cecca246b9335a3e1b8f9e4a176df8827d0a`. The [commit readback](merge.api.json)
records its ordered parents as base
`ba83c5c97a9c67bf3904423745b3e9c019a083cb`, then published head
`9256fe9ef4ffa722066b0569ee37341cf65dea0d`. See the
[complete docs checkout log](logs/check-docs-111851435760.log.txt.gz) and
[checkout audit](checkout-audit.json).

At the recorded snapshot, five of the eight validation producers had completed
successfully: docs, Lean kernel, interop, macOS source and Lean. Both Rust
producers and distribution remained in progress. The separate changes job had
also completed successfully. No required aggregate context was present in this
first-page jobs readback, and this packet establishes no aggregate success.
No further status poll was performed.

The workflow's producer release-receipt steps were skipped for the completed
producers on this pull-request run. The changed mathematical-proof compilation
step in the Lean producer was also skipped. Successful completed jobs do not
establish release readiness, approval, publication, new guarantees or completion
of the broader pending obligations.

[Run readback](run.api.json), [jobs readback](jobs.connector.json),
[status snapshot](snapshot.json) and [tested workflow source](workflow-9256fe9.yml)
retain the evidence and its scope. The jobs connector returns the latest attempt's
first page; this is not a complete final workflow graph. No terminal logs are
claimed for jobs still running at the snapshot.

All six completed job logs are retained in full as deterministic gzip files.
Decompression restores the exact connector-returned UTF-8 bytes, including
timestamps, ANSI escapes and trailing whitespace. These are decoded job logs,
not the original HTTP ZIP bytes. [Decoded identities](decoded-log-identities.json),
[byte readback](byte-readback.json), [request record](requests.json) and
[file map](files.json) document that boundary. The file map excludes itself.

The local artifact audit and documentation/whitespace checks are recorded
separately. No Cargo, Lean or native CLI command was run for this capture.
