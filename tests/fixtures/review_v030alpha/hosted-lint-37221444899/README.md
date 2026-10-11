# Hosted all-target Clippy repair

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

[Run 37221444899](https://github.com/MGYamada/Qleisli/actions/runs/37221444899)
checked PR merge `affcee3ca1b4385e22b66bfb269b20db22458326` for branch head
`56eb0725b77670be38d11ce450c1d525b90a5636`. Its MSRV job
`111492483405` passed all-target test execution and failed subsequent Clippy
because `tests/specification_boundaries.rs` retained two unused local
conversions, `av` and `bv`, after the ordinary-type migration. The
[exact failure excerpt](failure-excerpt.txt) is selected from the fetched job
log; the complete job log was not copied into this packet.

Remove those two unused conversions. Keep the complete four-input loop, emitted
program and independently expected swapped output unchanged. This does not
change production code, acceptance or the test's numerical oracle.

The validation driver reuses the fixed bounded target with debug information
and incremental compilation disabled. It type-checks every Cargo target with
Clippy, executes only the ten existing specification-boundary tests, and checks
formatting. No new all-target test executables, source snapshot, Lean build or
maximum-size quantum case is requested. Actual latest/MSRV command output and
selected source identities are retained separately in JSON records.

[Rust 1.98.1](latest.json) and [actual Rust/Cargo/Clippy 1.85.0](msrv.json)
both pass all-target Clippy with warnings denied, all ten selected tests and
formatting. The recorded source hashes remain stable during each run.

This repair does not turn the previous hosted failure into a pass. The current
local commits still require hosted integration after push; release readiness
and publication remain separate.
