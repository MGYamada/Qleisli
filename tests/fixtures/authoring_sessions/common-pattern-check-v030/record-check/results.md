# First-record integrity checks

The successful [constitution guard](constitution.json) checked source identity
and continuity against reviewed base
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`, without Lean replay. The two fixed
commands in [driver-v2.py](driver-v2.py) then passed:

- [Authoring records](authoring.json): 34 records, 49 snapshots and 638 actual
  observations; no stored command was executed.
- [Documentation](docs.json): 1,876 local links, 19 Markdown anchors and
  206 Lean root modules. This is documentation integrity, not Rust/Lean tests.

The original [driver.py](driver.py) failed before running either command.
[The actual traceback transcript](failed-v1.json) preserves that failure:
the new driver compared a hash string with the whole `{sha256, bytes}` record
object, producing a false change alarm. A separate corrected driver reads the
existing `sha256` field; no first source, diagnostic or expected hash was edited.
All 191 completed baseline files and the 23 initial inputs still match their
original hashes. [Entrypoint discovery](discovery-observations.json) also retains
the genuine failed search for an absent regression filename; no nonexistent
test is reported as run.

These three successful guards establish only their stated integrity properties.
The failed helper does not change any CLI/native result. No Cargo/Lean build,
execution oracle, full CI, source-preservation theorem, guarantee admission or
release approval was performed here.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
