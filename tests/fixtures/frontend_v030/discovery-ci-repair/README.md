# Current discovery-help regression repair

PR-head `faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2` was checked by hosted
run 37264563243 using merge checkout
`51f77cd2c3c97f75982e86adf32d197e8385eefd`. Rust 1.98.1, MSRV 1.85.0 and
source-distribution validation stopped on the same non-UTF-8 usage assertion.
Their decoded job logs and original ZIP digest are retained. The downloaded
distribution report/logs are losslessly compressed in `distribution-logs.tar.gz`,
with every original byte hash in `distribution-archive.json`; the failing test's
stdout/stderr also remain directly readable. The distribution artifact confirms the assertion in its
actual source-archive run; it is not an inference from another job. Other
producer jobs passed, and all required aggregates rejected the incomplete run.

`before-cli.rs.txt`, `before-cli-json.rs.txt` and the actual failing local probe
preserve the old expectation. The historical selected-source usage fixture is
unchanged. Non-UTF-8 check/help/--help commands must now match the current
unknown-command route, retain status 2, emit no stdout and provide discovery
without panicking. The current recorded usage snapshot keeps complete JSON
envelope/escaping tests independent of the production serializer.

Validation preserves all first failures:

- `latest/`: the sandbox denied process inspection in the existing descendant
  cleanup test; this is not recorded as a passing test.
- `latest-unsandboxed/`: descendant cleanup and the repaired text usage passed;
  the analogous historical JSON usage expectation then failed.
- `latest-repaired/`: Rust 1.98.1 passes **765 tests**, with **52 existing ignored
  tests** left ignored, on 181 unchanged selected inputs. All-target Clippy and
  formatting pass. Default all-target runtime took 973.91 seconds, including
  the existing 4000 small ownership-comparison cases. No ignored maximum stress
  case was activated.
- `msrv-cli/`: actual Rust 1.85.0 passes **28 focused CLI tests**, all-target
  Clippy and formatting on the same selected inputs. This is not a local MSRV
  all-target runtime claim; hosted MSRV remains a separate required check.
- `policies/`: the first docs/book, rendered-link, inventory/coverage, authoring
  and constitutional checks pass. Its Book warning about an unquoted `Q<T>`
  table cell led to the separate markup repair. Final policy results are
  recorded separately after that change and the next first-source study.

The Book/contributor explanations identify the actual v5 ledger while preserving
the historical v4 transition, both scoped guarantees and all pending obligations.
No constitution, human event, guarantee, semantic predicate, Lean source,
acceptance rule, dependency version or historical validation record changes.
This repair adds no completed Issue and claims no hosted repair success or
release readiness.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
