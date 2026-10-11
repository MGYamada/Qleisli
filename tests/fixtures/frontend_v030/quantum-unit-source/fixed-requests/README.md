# Fixed transformed scalar requests

This packet preserves the observations used to inspect transport placement
before strengthening `tests/quantum_unit_source.rs`. It does not change the
original sources, recorded outcomes or the native checker.

`before-test.rs.txt` is the exact earlier 11-test file (SHA-256
`d9e62a2ac7fa8871bdb7b877dc0b857ef36f4cb426b40df6a919e55cb323a347`).
`observations.json` and the five entry-named JSON files are byte-for-byte copies
from `/private/tmp/qleisli-unit-transformed-requests`. The JSON artifacts are
emitted **untrusted proposals**, including their producer equations. They are
not independently authored requests.

Each recorded command ran `emit-proposal` on
[`operations.qli`](../current/operations.qli), selecting `main::scalar` for `U`.
All five commands exited 0 and explicitly reported `native_check_scope: none`.
The original record identifies CLI SHA-256
`d6f3c3b31a7e8744e996f4ce48eb081c29177f2e7c563b465c67c8fb5526d29f`.
That is the observed binary identity, not a claim about a later rebuilt binary.
Exact command arguments, stdout, stderr and source hash remain in the original
record. No per-command timestamp, complete environment or source-build manifest
was recorded there; this packet does not invent one.

The expected mathematics was authored independently: for
`U = zeta_8 = exp(i*pi/4)`, application is `zeta_8`, inverse is its conjugate,
eight repetitions are 1, one controlled application is `diag(1,zeta_8)`, and
four controlled applications are `diag(1,-1)`. The strengthened test constructs
an exact 1-by-1 `Exact::phase(1)` matrix and fixed inverse, power and control
request nodes. It does not obtain those coefficients or operations from the
candidate or its `comparison_request`.

Owner labels, ordered interfaces and literal call/rename/sequence placement
were inspected from the saved artifacts because the existing request protocol
compares those structures. This is informed placement, not an independent
source-lowering proof. The new negative changes both the provider scalar and
its producer equation consistently to identity, obtains fresh native acceptance
for that wrong equation, and then requires rejection against the unchanged
fixed controlled request. Separate numerical joint-reference checks retain
the control coordinate and relative phase; their tolerance is runtime test
evidence, not the exact semantic contract.

The later [actual validation record](../latest-fixed-requests/result.json) and
[integration output](../latest-fixed-requests/3.stdout.txt) record **12 tests
passed** for `quantum_unit_source`, including that negative. They also record
the other focused checks with their explicit scope. `provenance.json` binds
those existing files and the strengthened test source by SHA-256. The five
historical probes were not native checks; they must not inherit the later test
result. No build or native execution was performed while assembling this packet.
The later validation reused the existing checker and made no new Lean
build/audit/replay claim.

`files.json` binds every other file in this packet; preserve those bytes rather
than refreshing historical records after future changes. This packet admits
no guarantee and completes no broader QS, PR, quantitative RS or exactness
proof duty, full source theorem, hosted CI validation or release approval.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
