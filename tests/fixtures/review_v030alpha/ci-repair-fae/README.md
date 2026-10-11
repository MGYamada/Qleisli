# Follow-up to the fae0e6a hosted CI run

Run 37206779468 tested `fae0e6a149f5b218bcc7f67f38d9509eb8aeb4f3` through
GitHub's pull-request merge checkout. Both ordinary and MSRV all-target Rust
tests passed. Subsequent jobs exposed two separate failures: MSRV Clippy's
`format_collect` lint in the native round-trip recorder, and the retained
Rust/Python sized comparison using contextual type words as static natural
names. The complete two job logs are retained as deterministic gzip files.
Neither log is a successful full CI record.

`lint-validation.json` records the isolated native recorder repair. The
unchanged fae0e6a tree was exported into a temporary directory; only
`tests/native_roundtrip.rs` was then replaced. Clippy 0.1.85 first reproduced the
failure and then passed **all targets** after writing hexadecimal bytes directly
into one preallocated string. No lint was suppressed. The existing positive
evidence test passed, and all four emitted proposals are byte-identical to the
previously retained native artifacts. That bounded rerun used at most two
qubits; it was not another full four-test round-trip suite.

An environment correction matters for interpreting earlier local records:
`rustup run 1.85.0 cargo clippy` on this machine selected the Homebrew
`cargo-clippy` 0.1.98 from `PATH`. Such invocations alone do **not** establish an
MSRV Clippy result. This record explicitly places the 1.85.0 toolchain's `bin`
directory first and verifies both `rustc` and `cargo clippy` versions. Earlier
command logs remain unchanged; hosted CI uses its explicitly installed
toolchains. The new isolated all-target Clippy result is the verified local
MSRV check for this correction.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
