# Explicit current Rust source clients

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The post-cutover Rust client audit found two active consumers of historical
syntax. Native roundtrip discovery recursively entered `corpus/migrations/`;
the [separate packet](../roundtrip-current-source-selection/README.md) retains
its hosted failure and discovery correction. The bare-CR diagnostic test used
a copied CBit source and repaired only its line ending before expecting a
successful current compilation.

The new [canonical source map](current/review_v019/bare_cr/source-map.json)
preserves both original inputs and selects a separate Bit derivative retaining
the literal CR. The test still checks the exact original byte offset and line,
then explicitly changes CR to CRLF and checks the intended X action. Historical
source bytes, hashes and observations were not rewritten.

[Validation](validation/result.json) ran the complete five-test
`native_roundtrip` target and two-test `review_v019` target, plus their Clippy
checks with warnings denied, on Rust 1.98.1 and the actual 1.85.0 toolchain.
All seven tests passed on each toolchain. The roundtrip test compiled all 101
current projects, retained accepted-artifact roundtrip/cache checks, and the
new discovery regression excludes archived migrations without losing active
corpus projects. This is bounded existing test coverage, not source Soundness.

The commands reused `/private/tmp/qleisli-bounded-validation-target`, with
incremental compilation and debug information disabled. The entire target was
about 402 MiB after both this repair and the preceding Unit-pattern checks.
The same existing audited checker was selected explicitly. There was no new
Lean build, repository snapshot or maximum-size quantum case.

The [distribution failure packet](../hosted-distribution-37218876223/README.md)
confirms the same old roundtrip selector failure from the actual hosted source
archive test. It also records successful crate verification/installation and
owned temporary-work cleanup on failure. The overall hosted run failed; these
component successes do not imply distribution or release readiness.

Fresh all-target/hosted validation remains required. No Issue is closed solely
by this fixture-selection repair, and no tag or publication is performed.
