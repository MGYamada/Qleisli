# Native distribution candidates

The v0.2.9 distribution pipeline initially prepares macOS and Linux checker
archives, with an explicit matching Rust CLI/library requirement. Cargo does
not download or install a checker. Windows binaries are not an initial target.

The local macOS arm64 candidate was rebuilt from a fresh source copy, audited
and replayed with `leanchecker --fresh` for both `QleisliKernel` and `Main`.
`macos-bundle-manifest.json` binds source hashes, binary/runtime license hashes,
all build/audit/replay commands, dynamic dependencies and relocated positive and
negative protocol checks. `macos-public-paths.json` records 241 process checks
and 84 corpus clients of at most four qubits against that relocated candidate.

`scripts/archive_lean_kernel.py` requires a clean source commit and validates the
bundle's source and file identities before producing a platform archive and
SHA-256 file. Each archive includes the checker, Qleisli and Lean runtime
licenses/notices, audited bundle manifest, source-commit metadata and install
instructions. Full macOS/Linux CI retains these artifacts for release review.
All required checks must pass on the exact source commit before publication;
candidate preparation alone is not a published release or completed Soundness.

Known deferred work remains explicit: #94 capacity typing, #268 Windows process
containment, #274 process batching, #275 diagnostic taxonomy and #278 stress
coverage. No maximum-size stress tests were newly enabled. Rust crates.io
publication and GitHub binary publication are distinct operations.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
