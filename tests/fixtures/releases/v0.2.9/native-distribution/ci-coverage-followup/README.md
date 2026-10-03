# Native comparison coverage follow-up

CI run [37139409045](https://github.com/MGYamada/Qleisli/actions/runs/37139409045)
on `60d47d2907b8f84c139fad11f718060e9577f975` passed all 67 native comparison
groups, then failed the final command-coverage assertion because it still
expanded only an entire `{record}` argument. The retained report remains marked
failed. Execution and coverage validation now share the same expansion; the
corrected validator accepts all 67 original groups. The nested-path regression
also checks coverage success and rejection of a corrupted recorded command.
The 14 runner tests pass. This is a CI correction, not a change to native
acceptance or a claim that the old full run passed.

The same run exposed a Linux-only timeout in the historical direct expansion
of 1024 TH pairs (`review_v021`). Both Rust 1.98.1 and MSRV 1.85.0 reached the
60-second native limit. The original large case remains as an ignored test for
[the maintainer-selected v0.3.1 stress work](https://github.com/MGYamada/Qleisli/issues/278).
Active coverage preserves the independent recurrence through 1024 static
repetitions and compares direct inline source at 16 repetitions. The active
review target passes 12 tests, with one retained stress case ignored. No timeout
was raised and no failed execution was counted as semantic agreement.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
