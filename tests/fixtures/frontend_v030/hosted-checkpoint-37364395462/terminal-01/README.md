# Terminal metadata, CI run 37364395462

The subsequent fresh API observation reports run attempt 1 completed with
**failure**, on published head `73aca78e13bc65125c4e533da48dd1318cf1cc51`
and PR base `ba83c5c97a9c67bf3904423745b3e9c019a083cb`. The earlier
`current-cancellations-01` packet retains its partial snapshot unchanged;
its checkout/selection evidence binds tested merge
`f7707f2aa4506ca354e93f46c702b63014f2ef44`.

All 18 normalized job records are terminal. Changes succeeded. Six of the
eight producers succeeded: Rust, native kernel, Mathlib Lean, interop, docs
and macOS source. MSRV and distribution were cancelled; the earlier packet
records no runner/steps and unavailable cause. No cause has been established
by this subsequent status fetch. All eight aggregate contexts failed, and
release-readiness was skipped. Passing individual producers does not imply
full CI or release readiness. Producer log contents were not independently
audited for this terminal packet.

`run.json` retains the decoded response from the fixed run API;
`normalized-jobs.json` retains the purpose-built connector's job metadata,
not an invented raw API response. Provenance identifies the observation and
these limits. A local metadata-only check verified the exact head/base and
18 terminal job classifications. It ran no recorded command, build, test,
CLI, native checker, replay, retry or cancellation. This is evidence for the
published checkpoint only, not later uncommitted source changes.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
