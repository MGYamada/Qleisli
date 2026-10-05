# Unexecuted direct-native client design

This additive local candidate contains a separate unpublished Rust client for
the existing `qleisli::interchange::hierarchical::Kernel` API. It offers exactly
two fixed actions:

```text
qleisli-qft-native-gate-design inspect ABSOLUTE_KERNEL PAYLOAD_FILE
qleisli-qft-native-gate-design request ABSOLUTE_KERNEL PAYLOAD_FILE REQUEST_FILE
```

`inspect` calls only `inspect_native`. `request` calls only
`check_against_native`; it does not reuse a prior inspect receipt. The latter
API selects the current Fourier or generic mode from the strictly decoded
request, without running commands from artifact metadata. The checker must be
an explicitly supplied absolute path. There is no environment/PATH selection,
interpreter, Rust acceptance fallback, source loader, adapter, numerical probe,
simulation, std injection, or receipt deserialization in this client.

Each payload and request is independently capped at 1 MiB. Regular-file
metadata is checked and the actual read is capped at 1 MiB plus one sentinel
byte, so a growing input cannot bypass the size rejection. Inputs are passed
unchanged to the current API. Successful calls assert exact retained payload
and optional request equality, absent candidate bytes, and a pure hierarchy
report. A failed assertion terminates rather than publishing success.

Standard output is one JSON record for ordinary success or failure. Exit 0
means the selected existing API succeeded and byte-retention assertions passed;
exit 1 reports its transport/native error, preserving public code, message and
JSON pointer. Exit 2 reports arguments, file I/O or this client file limit.
Unexpected retention/report assertions panic with a failing process status.
The error stage `hierarchical-kernel-api` intentionally includes strict decode,
pair construction, process transport and native checking: it does not claim
that a checker process necessarily ran. A separately retained wrapper log must
establish actual invocation count and argv.

Source identity, checker hash/build provenance, independent request authorship,
fixed command capture and failure-stage interpretation belong to the external
bounded experiment record. This client neither authenticates them nor turns
output validity into source preservation, an analytic Fourier theorem, a
family/reference/resource guarantee, canonical std exposure or Issue completion.
Its JSON report is local observation data, not serialized acceptance authority.

The manifest has only a path dependency on the repository `qleisli` package,
with its current `0.3.0-alpha` version, edition 2024 and Rust 1.85 minimum. No
dependency versions, repository source or acceptance APIs are changed. The
empty workspace keeps the candidate isolated from any later repository
workspace membership. No Cargo.lock or target directory is created here.
A separate manifest does not inherit the repository lockfile automatically;
review the eventual client lockfile against the repository dependency graph
before a locked build. Any later compilation must use the already coordinated
fixed target directory explicitly, and requires the root's separate review
and authorization. No proposed build command was executed for this record.

Performed: public API/source inspection, additive source writing and file-hash
recording. Not performed: formatting tool execution, compilation, Cargo/Lean,
CLI/native invocation, harness execution, tests, Git or GitHub mutation.
`KernelConfig` does not exist in the current source; configuration here is the
actual public `Kernel::new(PathBuf)` constructor. Native compilation/decoder
correspondence and the matching audited executable remain external assumptions.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
