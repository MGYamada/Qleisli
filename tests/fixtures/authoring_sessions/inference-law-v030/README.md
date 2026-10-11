# Explicit inference-law diagnostic study

Nine complete first projects and their desired 24 probes were frozen in
`first-files.json` before observations or production edits. The study was
interrupted before running probes and resumed from those exact bytes.
`baseline/` records CLI SHA-256 `15900c32…`; `after-repair/` records the
new build. Each invocation checks source/CLI/kernel identity, records exact
output and logs native invocations through a transparent unchanged-checker
wrapper. No Rust build ran concurrently with either observer batch.

The 48 observations preserve 18 rejections and 6 successes per batch. Rejections
have zero native calls. Original code/module/spans and exit statuses are
unchanged; all 6 successful JSON outputs remain identical. Diagnostics now name
missing/extra bindings and source-call parameters. `comparison.json` records
this check. These open checks do not execute an operation or prove source
preservation. Independent one-qubit/reference action tests are separate.

`observations/` renders the raw output for the authoring-session integrity
checker. Its recording times come from each actual batch result written after
the observations, not authenticated invocation timestamps. The immutable
original context, sources and desired outcomes are not rewritten.
