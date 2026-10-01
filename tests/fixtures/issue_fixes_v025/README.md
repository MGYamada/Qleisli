# Compatible bug repairs for the next 0.2.5 release

[Issue 146](https://github.com/MGYamada/Qleisli/issues/146) replaces macOS source
loading's unconditional `O_NOFOLLOW_ANY` with a component walk from held directory
descriptors. The macOS-only rustix 1.1.3 dependency provides safe `openat` and
`O_NOFOLLOW` wrappers; project unsafe code remains forbidden. Regular-file and
nonblocking FIFO checks remain. Rust's existing deployment minimum is unchanged.
Tests cover final/intermediate symlink substitution, a held parent renamed and
replaced with a symlink, and a source replaced with a FIFO without a writer.
The macOS/MSRV CI job also compiles Intel macOS with deployment target 10.12.
Compilation does not claim execution on an old macOS installation.

[Issue 147](https://github.com/MGYamada/Qleisli/issues/147) aligns crate-level
quick-reference, trust-boundary and versioning links with the package version.
The docs checker checks package-facing pins in src/lib.rs and README.crates.md;
regressions reject older/future tags while accepting matching or independent
targets. Future version selection must update these links too.

[Validation](validation.json) records actual tests and source hashes. The narrow
PR keeps main's current 0.2.4 metadata and fixes its pins to v0.2.4; the ongoing
0.2.5 workspace has v0.2.5 pins. Neither changes the published 0.2.4 tag/package
or publishes 0.2.5. The larger refactoring/VM-25 work remains separate.

Run cargo test --locked --all-targets, cargo clippy --locked --all-targets --
-D warnings, cargo fmt --check, python3 scripts/test_check_docs.py and
python3 scripts/check_docs.py. Rust 1.85.0 and 1.98.1 are checked separately.
Rust retains production authority; no Lean executable/proof changes occur here.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
