# Current CI regression diagnosis

This small packet records actual observed failures from [run 37392202925](https://github.com/MGYamada/Qleisli/actions/runs/37392202925), for branch head `7f6529ef93838d565552c3f501ce016ef1d1d2b4`. The jobs executed synthetic PR merge `a675d87a9e0c550200e179bcd2cc375f7c45458a`, merging that head into `ba83c5c97a9c67bf3904423745b3e9c019a083cb`.

[Observations](observations.json) bind the four job IDs, authoritative GitHub links and selected original line numbers. The four `.log-excerpts.txt` files preserve selected complete decoded log lines, including timestamps; they are excerpts, not full logs. The macOS panic's single enormous successful-Project debug line is omitted to keep this packet bounded. Other selected failure and result lines remain complete.

In that hosted run, both Rust toolchains fail the same specific empty-pattern diagnostic assertion. The macOS job exposes an old rejection expectation for a permitted import-only cycle. Distribution reaches the source archive's all-targets test stage and fails there; its underlying test failure remains unverified because detailed artifact logs were not inspected. Successful earlier stages do not establish completion of the failed distribution gate.

[Read-only repair review](review.md) preserves the initial source inspection separately from the failed commit. Subsequent local records retain both failures and successful focused validation. The original [local MSRV all-targets run](validation/msrv-results.json) reports 792 passed, 24 failed and 52 ignored; its [compiled source record](validation/msrv-compiled-source.json) identifies the earlier inputs. [Stage 03](validation/focused-repair-03-results.json) reports 119 passed and one failed integration test: a nested primitive's diagnostic span was relocated a second time by its enclosing primitive. Neither failure record has been replaced with a later result.

The [validation overview](validation-overview.json) links exact retained records and their hashes. Final local validation is limited to these checks:

| Check | Recorded result and scope |
| --- | --- |
| [Rust stage 04](validation/focused-repair-04-results.json) | Each of MSRV 1.85.0 and installed latest 1.98.1 passes 120 tests in 14 selected integration targets and 62 frontend unit tests, with zero failures and two existing native-kernel ignores. Clippy on all targets and formatting pass. This is not a current all-targets test run. |
| [Earlier Python stage 04](validation/python-repair-04-summary.json) | Eleven bounded comparisons pass before the final Rust diagnostic-provenance fix; they were not all rerun on the final source map. |
| [Final Python stage 05](validation/python-repair-05-host-summary.json) | Two existing host/native comparisons pass with a matching 465-file source map. [Scheduler and parser checks](validation/python-repair-05-ci-coverage-summary.json) each pass 16 tests. |
| [Policy stage 04](validation/policy-repair-04-results.json) | All nine commands pass, including constitutional continuity against `faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. Identity and policy checks do not constitute a fresh Lean replay. |
| [Book stage 04](validation/book-repair-04-results.json) | The retained mdBook 0.5.4 binary reports its version, builds the book, and passes generated-page checks: 23 HTML files, 922 local links and 345 anchors. Actual commands, tool/source hashes and output logs are retained. |

[Review 03](review-final-03.md) remains the preceding read-only observation, including its lack of runtime validation and its author's ownership of the canonical formatter changes. The later failing stage 03 exposed the nested-span defect after that review. [Review 04](review-final-04.md) inspects the provenance repair and retains those authorship limits. A separate [independent display review](review-display-04.md) covers the canonical formatter changes; its metadata observations describe its earlier snapshot. These reviews do not replace the actual execution records.

Full current hosted CI, the entire native comparison manifest, packaging, fresh installation, fresh Lean replay and release validation are not established by this packet. Generic `qft<N>` completion remains excluded from all v0.3.0 and the current goal; existing fixed Fourier comparisons are retained.
