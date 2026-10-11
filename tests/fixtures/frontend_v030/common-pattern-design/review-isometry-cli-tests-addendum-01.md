# Review addendum: concrete sized name type

Reviewer: `/root/isometry_cli_tests`. This is additive to the first read-only
[review](review-isometry-cli-tests.md), which remains a pre-compilation review
of its frozen five-source map. That review did not detect the compiler ambiguity
below and must not be represented as a compilation success.

The parent's actual latest-toolchain attempt01 failed with exit101. The
retained [repair record](compile-repair-01.json) and its referenced stderr show
`ambiguous_associated_items` at `src/frontend/sized/ast.rs:116`: `Self::Name`
could name the enum variant or the PatternView associated type. The parent
changed only the signature parameter to `&BindingName`, already the concrete
associated type selected by this implementation.

This reviewer read that actual failure log and the repaired source. Read-only
comparison of the current sized-AST HEAD diff with the frozen first patch
confirms exactly this one signature-line replacement, apart from Git blob
index metadata. Hashing confirms all five current paths match the repair
record's after map, with the other four source hashes unchanged. The new
sized-AST SHA-256 is
`42ddd4d545865611ba9bc7838ad6600e06879140cd4e689e89c8194891ed78eb`.

The correction disambiguates a Rust type spelling without changing the borrowed
view, lexical identity, pattern representation, actual binders, rule selection,
diagnostic order, capacities or acceptance boundary. No additional semantic
mismatch was found. Original patch/map/failure/review records were not rewritten.

The parent is responsible for attempt02 compilation and later tests/replay.
This reviewer executed no build, tests, CLI/native command or after replay;
observing a repair does not itself establish that those validations pass.
No constitutional adoption, guarantee admission, source-preservation theorem,
complete common checking or #32/#317 completion is claimed.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
