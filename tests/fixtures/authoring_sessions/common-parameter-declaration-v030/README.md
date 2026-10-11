# Common parameter-name first-source study

**Status: prepared, no CLI/native/test/build observation performed.** Ten
complete first projects use current source grammar and schema-2 edition 2026.
This is an informed bounded study of existing declaration checks, not an
adopted design, a benchmark or a completed common checker.

The [context](context.md), [prerequisites and predictions](prerequisites.md)
and [unobserved session snapshot](session.before.json) distinguish the intended
contracts from code-derived predictions. Original source and manifests are
bound by `project-inputs.json`; `first-files.json` freezes this preparation
before root executes any source command. The current external input map and
selected executable bytes are recorded in `identity-prepared.json`.

Root reviews the packet and freezes source/CLI before this fixed invocation:

```sh
python3 tests/fixtures/authoring_sessions/common-parameter-declaration-v030/driver.py
```

The driver authors **40 checks**: finite text/JSON and selected explicit-module
auto-profile text/JSON for each project. It never loads executable argv from
planned commands, observations or predictions. There is no emit, run, sample,
Cargo/Lean build or maximum-size experiment. The fixed CLI is the already built
`/private/tmp/qleisli-bounded-validation-target/debug/qleisli`, with SHA-256
`4a5cc9e753268fd7b0b4972cf84dd1fd6338218bc0b104d71b8465fab89151cf`.
Its identity is not a source-to-binary attestation.

The [native launcher](native-log.py) records actual native argv and transparently
delegates to the one pinned existing checker. Exact raw stdout/stderr, genuine
exits and native counts are retained under a new `before/` directory. Launch
failure or timeout retains partial records without inventing a child exit or
publishing an observed session. Successful completion creates `session.json`
only after every observation exists; the unobserved original remains unchanged.
The prepared status of this README remains immutable history.

Before/after byte checks bind all production Rust, kernel source, current
stdlib/manifests, Cargo metadata and constitutional records. This is a declared
incomplete proof/runtime/build closure. No production source, book source,
active metadata, Issue or prior fixture is edited by this packet or driver.
This packet adds no approval, theorem, guarantee or completion credit.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
