# Actual private native-client build

Root copied the reviewed candidate source and manifest unchanged from
`../native-client-design-01/`, then built this separate private test client
with actual Rust 1.85.0. The original design packet remains unchanged.

The first formatting check genuinely failed. Its output is retained; the only
repair wraps the existing request method chain. The subsequent formatter check,
offline locked Clippy with warnings denied and build all passed. No native or
QFT request was run by these build commands. The observed executable SHA-256 is
`683b29749f752652b3ddb8dba7fac0ea2d832f848178963f3056d2f5c03d8294`.

The separate lock was seeded from the repository. Initial `cargo metadata
--no-deps` succeeded without resolving the client graph; root's assumption
that it had added the client package failed. A second full offline metadata
operation filtered to the actual macOS host resolved it. All 24 original
package/version/source/checksum/dependency records remain identical; only the
private client package is added, for 25 total. The repository lock is unchanged.
`lock-review.json` records the actual graph comparison, not a compile result.

All 100 declared root source/configuration identities and the existing CLI
bytes remained unchanged through compilation. This is an incomplete build
closure and no compiled-HEAD, compiler correctness or portable executable
attestation. The single existing target directory was reused; no per-case
target, source snapshot or maximum quantum input was generated.

The client only invokes the existing explicit-path inspect/request APIs,
limits each input to 1 MiB, and checks immutable retained-byte equality on
success. Its JSON errors combine decode, pairing, transport and native stages;
external raw process logs must establish whether a checker actually ran.
Later request/candidate observations remain separate from this build.

No public Qleisli source/API, stdlib, dependency version, native/Lean code,
constitutional record or Issue completion changed. QS/PR/RS/EXACT duties and
both scoped guarantees retain their existing meanings and status.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
