# Current frontend regression header migration

This [Issue #33 unit](https://github.com/MGYamada/Qleisli/issues/33#issuecomment-6050049121)
changes twenty-four parameter markers in six current Rust test source builders.
Only test-owned QLI header strings change; runtime definitions, loop/branch
static evaluation, conditions, assertions and public surfaces remain unchanged.
The original complete Rust files are retained at the exact Git commit in
[the record](record.json), with original, initial desired and formatted hashes.
Frozen fixtures and earlier diagnostics are not edited or copied again.

The same frontend suite passed before/after: 87 tests on both Rust latest and
the pinned MSRV, with identical named outcomes and the same two existing ignored
native QPE tests. Both all-target Clippy runs passed. The suite retains actual
fresh native inspection/provider and preservation-refusal tests; no results are
cached. Kernel bytes, commands, environment and observation identities are in
the record. First invocations omitted the required kernel environment and failed;
the actual diagnostic and failure summary are retained rather than counted as
successful validation. Rustfmt also shortened one formatting statement.

VM-22 updates only the six current source hashes after independent public-surface
equality checks; constructors, boundaries, capacity constants and history remain
unchanged. This migration does not complete #33's other current clients or
legacy retirement, algorithm gates or broader QS/PR/RS obligations.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
