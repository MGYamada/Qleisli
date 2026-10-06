# Original-AST unit policy validation preparation

This is an **unexecuted draft** for root review. It writes no prospective map
until both final Rust runs, the 72 original-source capture, applied documentation
repairs and reviewed metadata are terminal and stable. It is a new fixed driver;
no previous policy main, obsolete 253/254-source expectation or stored argv is
imported. Current active inventory determines the inspected source list; this
does not authorize an inventory change or weaken any checker criterion.

The root supplies actual terminal result and capture-map hashes when freezing:

```text
python3 tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/policy-validation-01/driver.py freeze --latest-attempt attempt-NN --latest-results-sha256 ACTUAL_LATEST_SHA --msrv-attempt attempt-NN --msrv-results-sha256 ACTUAL_MSRV_SHA --capture-files-sha256 ACTUAL_CAPTURE_FILES_SHA
```

The root then reads the concrete map before explicitly delegating execution:

```text
python3 tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/policy-validation-01/driver.py run attempt-01 --inputs-sha256 ROOT_REVIEWED_INPUT_MAP_SHA
```

These placeholders are not observed values or runnable instructions supplied by
result metadata. All attempts and maps use exclusive creation. Retries get new
attempt numbers; failed/partial records are never overwritten. The executable
command lists are literal authored source. Recorded result/argv fields are read
only as identity/evidence data.

The 17 intended commands are: exact pinned mdBook 0.5.4 version, owned temporary
book build, generated HTML/print local-link and anchor check; book regressions;
authoring checker and regressions; source-edition checker and regressions; docs
checker and regressions; constitutional continuity against reviewed
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`; active inventory and its existing
17 mutation regressions; active coverage and its existing 14 mutation
regressions; schema registry `--source-only`; and corpus checker **without a
binary**, for provenance only. No maximum/exhaustive corpus execution or new
source generation is selected. Expected regression counts are 12/7/11/36/17/14
(97 total); they remain assertions until actual raw outputs report them.

The fixed mdBook binary is `/private/tmp/qleisli-mdbook-0.5.4-bin/mdbook`.
The fixed CLI and native binary are hashed before/after but never executed by
this driver. Successful terminal Rust records, their raw logs, input maps and
rebuilt CLI association are checked as separately performed evidence; historical
latest CLI bytes need not equal the current MSRV CLI. Actual 72 check observations
are validated through the terminal capture map/raw records, with no requirement
of output parity across a deliberate source migration. Native forwarder rows
are pre-execv observations, not independent native-start/exit attestations.

The prospective identity map binds all current production Rust, every active
inventory source, current scripts, book, governance, rules, std/corpus provenance,
tests and selected current validation/capture/review packets. It also binds
read-back proposal archives, relocation records and `.md.txt` copies. Historical
proposal maps describe archived paths; no obsolete live-path assumption is used.
Policy outputs and the temporary book are excluded. This is an explicitly
incomplete closure, not a compiled-HEAD, environment or whole-fixture attestation.
SHA-256 binds bytes, not a human act or a mathematical result.

At most two independent Python checks run concurrently. Each authored command
has 180 seconds and a 1 MiB retained stdout/stderr limit; timeout, output limit,
launch failure and incomplete cleanup cause failure. Raw prefixes, argv, status,
timestamps and hashes survive. The generated file hash map is written before
removing only the owned temporary book tree. Version/build failure leaves the
run incomplete and preserves actual records; it does not invent missing commands
or rendered-book counts.

These are ordinary documentation/policy checks. There is no fresh Rust/Lean
build, CLI/native replay, theorem replay, full CI, release-readiness check,
Guardian adoption, new guarantee, source-preservation proof, generic-family/QFT
completion or Issue credit. The two admitted decoded-root guarantees retain
their scope; broader QS/PR/RS/EXACT duties remain pending. Do not run this draft
before root review, final barriers and explicit delegation.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
