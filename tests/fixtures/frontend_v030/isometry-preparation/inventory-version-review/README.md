# Native hierarchy version diagnostic inventory review

This addendum preserves the earlier `inventory-review/` packet unchanged.
The runtime repair recognizes only the exact common native product-version
failure frame and returns a version diagnostic; generic success, malformed
and trailing frames retain rejection. It grants no new acceptance authority.
The earlier actual CLI failure and the subsequent compile/test results have
separate enclosing validation records.

The first `before/` capture observed runtime hash
`a379ede7cf7f39023cac26f97a7a7ed7374e13cf32feadc9f7b5166386602a01`.
Inventory rejected its stale snapshot while coverage still matched the old
inventory. Metadata was not changed at that point. The root agent then fixed
two test assertions after a real compile failure. This original capture is
preserved; it is not reported as a successful final-source check.

`compile-repaired/` records a separate review of final runtime hash
`0ee4c7afb8363d9e38699c1783345e0e78adbed3f172d891a31c46f1d46ebfda`:

| Phase | Inventory exit | Coverage exit |
| --- | --- | --- |
| `before/` | 1: stale runtime source hash | 0: matched the old inventory |
| `inventory-refreshed/` | 0 | 1: stale coverage digest |
| `after/` | 0 | 0 |

The checking-source map stayed identical through this final sequence, with
SHA-256 `8d1dd0fee0ac5c9580b63bce707af59a1a0a78bd0775ea457d5c40561d1a13fa`.
Its path set matches the prior review and only `runtime.rs` changed.
`compile-repaired/metadata-changes.json` records exactly one inventory hash
replacement and its derived coverage surface digest. `diff-audit.json` checks
the exact JSON difference against the preceding reviewed metadata, whose full
byte identities match the immutable prior packet. The source count remains
251; all signatures, constructors, capacities, routes, statuses, proof gates
and guarantee/publication scope remain unchanged.

The fixed drivers run only the two named inventory guards and never execute
record-provided commands. Their success checks metadata identity and bindings,
not mathematical semantics or the referenced tests. No Cargo or Lean
build/audit/replay, guarantee admission or release validation was performed by
this review. S05-C1–C5 remain open.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
