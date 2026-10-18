# Linked standard-qrate first observations

This is an informed #171 packaging and API study, authored after reading the
repository and public contracts. It is not a blind authoring benchmark. The
exact deployed model identifier and sampling settings were unavailable.

[The index](first-index.json) binds [the lossless inert record](first.records.json.gz):
all **63 original regular files / 69,934 bytes**, including eight untouched
first-source files, the pre-check context, saved observer, sixteen command
observations, all thirty-two stdout/stderr streams, and the actual empty-qrate
build artifact. The JSON/gzip container stores exact file bytes as base64 with
their original paths, modes and SHA-256. It is an observation container, not a
historical Git archive. Empty directory entries are outside its file inventory.
Root and independent passive review compare its bytes with the original files;
no archived command, observer, source or path is executed by that comparison.

Both desired qrates use this identical one-qubit body without selecting std:

```qli
use std::state::init0;
use std::gate::x;

observe fn main() -> Bit {
    measure_z(x(init0()))
}
```

Their explicit schema-2 edition-2026 manifests differ only in the ordinary user
version, `0.1.0` versus `2.4.0`. The complete source/manifests remain inside the
record. The empty root and unsupported std dependency are separate controls,
not repairs to either desired source.

| Actual first command group | Result and limit |
| --- | --- |
| Explicit Rust 1.98.1 with an existing selected Qleisli rlib | The desired public `bundled_std()` call rejects with E0425: the function does not exist. The compiler and rlib are compatible. |
| Existing Qleisli: check and run each user version | All four commands succeed. Each complete numerical distribution returns Bit `1` with probability `1`. This is bounded execution, not a source-preservation theorem. |
| Existing qargo: check and build each user version | All four commands reject `missing module std::state`. Its version response records qargo `0.1.9`, linked Qleisli `0.2.1` and profile `finite-v0`; this is not a native pairing refusal. |
| Existing qargo: empty check and build | Both commands succeed as packaging operations with source count zero and `qleisli_check.status = not_run`, reason `no_sources`. The old build record contains no effective std descriptor. |
| Existing qargo: explicit mismatched std dependency | Generic `invalid_manifest` refusal: dependency tables are unsupported. It does not exercise a specialized pairing resolver. |
| Existing Qleisli `--version` | Invocation exits `2`; that option is unsupported. The actual diagnostic remains preserved. No product-version observation is inferred from it. |

Separate version/help responses are retained alongside the command outcomes.
There are sixteen observations in total; none of the first results is replaced
by a later successful command. No source correction or Cargo/Lean/native rebuild
occurred in this window.

The observer resamples clean HEAD `336d021f29aad05e796bd50ee8e5e6a1b2931289`,
all selected Rust/stdlib/metadata source inputs and all five selected executable
or rlib identities before and after the complete sequence. Those windows agree,
and all eight first-source hashes remain unchanged. Observed CLI
`ba99534f8e8bbbca7ae328dc47972d4326d506f3026ccd36255c49ea2d059c2f`
and kernel `bd2bb0c31ac71b646471f1b4f5271bbb9d962e7a2ded5e452c09e9886a8a33cf`
identify the preexisting selected files. Their digests and current source window
are not a reconstructed commit-to-binary build attestation. The observer sets
the explicit kernel path but does not count or attest native child invocations.

These observations preceded the new read-only descriptor implementation.
They do not implement qargo pairing records, prove stale-content detection,
validate an official mixed distribution, issue an accepted handle, discharge
QS/PR/RS/EXACT, or complete #171. Later implementation and validation use separate
records; these first sources and diagnostics remain immutable.

The separate [first metadata-test index](test-path-first-index.json) binds its
[six-file inert record](test-path-first.records.json.gz). The first edition
suite compiled and ran thirteen tests: twelve passed, while a new test compared
the temporary `/var` spelling with the loader's canonical `/private/var` path.
Its original complete test source and real diagnostics remain unchanged here.
Only the expected canonical path was repaired; the remaining five commands in
that first serial sequence did not execute. Subsequent validation is separate
from this first failure and changes no production loading or acceptance rule.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
