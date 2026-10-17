# Derived phase and fixed QFT first history

This is an informed authoring study, not a blind benchmark. It preserves the
first desired ordinary controlled-phase and fixed QFT2/QFT3 sources, all actual
diagnostics, and a separate `translations-01` packet. Only two- and three-bit
cases were executed; no maximum-size quantum case was generated or checked.

The first six invocations include four QFT check/run refusals. The private Bit
identity wrapper used `id[Bit]` instead of `id[type(Bit)]`; the original
`type_mismatch` diagnostics and their exact source positions remain unchanged.
The controlled-phase check and run succeeded. The separate translations change
only that Basis wrapper argument in each QFT source; all four translated QFT
check/run invocations succeeded. The originals were not repaired in place.

Successful check reports record 171 native decisions for controlled phase,
210 for translated QFT2, and 224 for translated QFT3. Each reports zero
independent requests, an entry without a complete independent request, and
`source_preservation_verified: false`. Run streams record approximately uniform
distributions on two or three bits; they contain no native-decision counts.
These outputs are observations, not independent exact Fourier/phase equations,
arbitrary-reference tests, source-preservation proofs or performance benchmarks.
Fresh independent requested equations remain separate validation.

The first driver was Python stdin; no pre-invocation script was saved. No
driver, prediction or invocation transcript is reconstructed. Captures retain
reported argv, exit codes and full stdout/stderr, but those records do not
independently authenticate the invoking observer or the executed argv.
The first capture records dirty HEAD
`460f72e019885bd859686b6f4a8b265b40ab36fd`, CLI SHA-256
`d20fbb4505ed3c11997929b487404ea225395f993ea53bb30183361dcbda6ed9`
and kernel SHA-256
`54c9d60b80f67217abd95c8fe6ec1c06aa262e142d5e6db30f46a20cb90faf07`,
with reported CLI/kernel stability. The translation capture records the same
executable hashes but no separate HEAD or stability window. Neither packet
records a complete compiler-source freeze or pre/post source-byte hashes;
this is not a clean commit-to-binary build attestation. Manifest hashes bind the
bytes observed during later retention, not an invented earlier source window.

Deterministic fixed-metadata USTAR/gzip archives retain 36 unchanged files /
21,235 expanded bytes: first 21 / 11,509 and translations 15 / 9,726. These
include nine `.qli` files, five manifests, two original capture JSON files and
all twenty stream files. The first packet retains its complete original tree
except the `translations-01` subtree, retained completely as the second packet.
`packets.json` binds every original member's bytes, SHA-256 and mode. Existing
80-member, 5 MiB expanded and 2 MiB stored reader limits remain unchanged.
The earlier general-static and runtime-transform retention files are unchanged.

The passive reader never executes recorded commands, sources or observer code
and never extracts archive members. It checks complete inventories, reported
argv/source associations, all streams, refusal locations, separate repair bytes,
native-report scopes and bounded distributions. This history does not establish
current implementation correctness, source/native/runtime preservation,
QS/PR/quantitative RS/EXACT discharge, Issue completion or release readiness.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
