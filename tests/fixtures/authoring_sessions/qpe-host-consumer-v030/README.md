# QPE host consumer expectation repair

The actual PR419 checks on commit
`d1daebe29e78779022afcdc88812a3a4f76090fd` failed in the existing small
two-target/four-phase QPE case. The native API returned `Ok`; the Rust assertion
then compared the old expected string `limit` with `ok`. The legacy host path
had not yet run for that case. The first audit message reversed that distinction;
its subsequent explicit correction is retained alongside the original logs.

[The first index](first-ci-index.json) binds
[all nine original files](first-ci.records.json.gz): exact Git-F Python/Rust
consumers, both full untruncated hosted logs and provider responses/metadata,
and the correction audit. These are inert original records, not a historical
Git-tree archive. No original CI candidate/request packet was captured, and no
source-build attestation or source-preservation claim is reconstructed here.

The repair changes only two Python lines: rename `capacity` to
`target2precision4` and require acceptance. It reuses the same six physical
qubits and independent request. The Rust assertions, all other positive and
phase/route/provider/H/runtime faults, limits and exact-work checks are unchanged.
Existing oversized-nested and shared-word-budget probes retain explicit real
limit refusals. No larger quantum case or raised cap is introduced.

[The separate validation index](validation-index.json) binds
[twelve original local files](validation.records.json.gz), including both saved
observers, full reports and streams. Normal Rust 1.98.1 and explicitly selected
MSRV Rust 1.85.0 both pass all 21 named cases, 11 response faults and 72 binary
transport cases. Both native and legacy host paths now accept the unchanged
six-qubit case: structural work 1,869,612 within 2,000,000; exact work 1,368
within 10,000,000. Both Rust harness tests pass with zero ignored tests.

The normal and MSRV source maps agree and their complete working windows stay
at `82a19287f929bc97afec4ffe66eea998b9ebe46c82978135d16d98fe9d6ffe0b`.
The selected native kernel stays
`bd2bb0c31ac71b646471f1b4f5271bbb9d962e7a2ded5e452c09e9886a8a33cf`.
The MSRV observer explicitly selects and records matching Cargo, Rust, Rustdoc
and Clippy executables before running the Python-owned Cargo child. Normal CLI
observation `0266bd9c…` and MSRV `ba99534f…` remain distinct build observations.

Passive retention comparison decodes base64, checks every original file's
bytes/hash/mode and never executes stored commands or observers. These bounded
local results do not replace latest-head hosted CI, prove general budget
compatibility or source/runtime preservation, admit an external schema, discharge
broader QS/PR/RS/EXACT obligations, or close #369/#167/#142. Future validation and
candidate changes use separate records; first diagnostics remain unchanged.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
