# Dormant control owner-order first study

This informed study is not a blind benchmark. Two unchanged first sources use
one physical qubit and two logical owners, in the ordered forest
`(Q<Unit>, Q<Bit>)`. Both call the same closed `pair` implementation, which
preserves the empty owner and applies X to the bit. The only source difference
is `pair(ctrl a, excl b)` versus `pair(excl a, ctrl b)` in an unused generic
body. No source repair, sampling or maximum-size quantum case was generated.

The first plan predicts acceptance for the empty-owner Ctrl call and requires
refusal for the bit-owner Ctrl call: X changes physical axis zero even though
the bit is the second logical owner. Both first checks actually accepted.
Predictions are requirements, not observed successes. Each success reports one
concrete local root, nine bundled roots and 19 native decisions, with zero
independent requests. An absent entry and unproved source preservation remain
explicit in the full stdout. These ordinary-root decisions did not check the
dormant call's control-sector obligation.

The observed HEAD before and after capture was
`410a50dc0ae2a4179279e75d3c4ea9aad0422ca2`. Capture occurred during a dirty
cherry-pick integration. The retained driver records HEAD and executable
identities; it does not capture a complete source window or Git status. CLI
SHA-256 `5f08a1b8b8e3836954bfb267a94c66757055485cd1c653c881db1c6cae1ca88f`
and kernel SHA-256
`54c9d60b80f67217abd95c8fe6ec1c06aa262e142d5e6db30f46a20cb90faf07`
were unchanged across the two checks. This is not a clean commit-to-binary
build attestation. The driver's presence preserves the actual observer code;
it does not prove that the observed binary implements the checked-out source.

One deterministic USTAR/gzip archive preserves all 11 original files / 6,758
bytes, including both schema-2 projects, first predictions, actual observations,
the capture driver and complete stdout/stderr. Two independent encodings agreed;
both decoded byte inventories and original mode-0644 inventories matched every
original file. The existing 80-member, 5 MiB expanded and 2 MiB compressed bounds
remain unchanged. Archive metadata is fixed and only regular local files occur.

The bounded reader never executes recorded commands or source and never
extracts records to the filesystem. This history does not complete generic
materialization, full dormant checking, source/native/runtime preservation,
QS/PR/quantitative RS/EXACT, an Issue or a release. Fresh checking of the actual
ordered owner forest and its physical Ctrl axes remains separate from retention.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
