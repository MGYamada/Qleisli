# Planned pattern-unit policy validation v2

**Status: prepared, not executed.** This new version preserves the earlier
15-command draft as unchanged historical preparation. Root now runs:

```sh
python3 tests/fixtures/frontend_v030/common-pattern-design/policy-validation/driver-v2.py attempt-01
```

The driver has **13 fixed commands**: pinned mdBook 0.5.4 version/build and
rendered-link checks; book, authoring-session, source-edition and documentation
integrity/regressions; constitutional continuity against
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`; and the active verification-inventory
and production-coverage guards. It performs no Rust or Lean build, test or replay.

The separate [root metadata review](../metadata-review/results.json) actually
passed both guards, 17 inventory mutation tests and 14 coverage mutation tests.
Its raw [inventory](../metadata-review/after.inventory-regression.stderr.txt) and
[coverage](../metadata-review/after.coverage-regression.stderr.txt) results are
retained. These 31 tests are **not rerun or counted as new policy commands**.
The read-only [reference](metadata-reference-v2.json) binds all retained metadata
packet files, its 253 mapped source identities and the exact active metadata
after copies. The driver rejects changed packet/source/metadata bytes before
launching policy commands. It reads identity data only; recorded argv is never
executed. That packet did not freeze historical regression-script bytes, so
this reference does not claim complete historical script/fixture/build closure.

The five changed paths are private `pattern.rs`, the frontend module, finite
lowerer, sized pattern view and sized checker. Input identities also cover
production Rust, kernel sources, docs/governance, selected policy scripts,
stdlib, current session inventories, the actual Reference and changelog, both
policy-driver versions, and the separate metadata packet. Current hashes are
collected after root's final source/metadata/Reference barrier and checked again
after execution. This declared input map is incomplete for fixture/proof/build
closure and supplies no Git or binary attestation.

Each attempt creates a new directory. Genuine stdout/stderr, exit codes,
launch errors and timeouts remain retained. Only the driver's small owned
temporary book output is removed after its file hashes are captured. Independent
Python checks use at most two workers. Source changes and native/mdBook
executable changes cause failure; fixed mdBook identity also requires the
observed version to be exactly 0.5.4.

The [separate bounded Rust driver](../validation/driver.py) and first-source
replay are root-run work. This policy driver neither runs them nor asserts their
success. The context-reset [startup check](preparation-startup-v2/constitution.json)
was separately performed during preparation and returned exit 0; it is not a
run of this policy driver.

Private runtime pattern-binding traversal is shared; sized elaboration and
coherent basis binding remain separate. Passing these checks completes no
common checker, canonical generic QFT API, source-preservation theorem, Issue,
QS/PR/RS/EXACT discharge, full CI or release approval. Both ordinary QLV1
guarantees and all pending obligations retain their current scopes and statuses.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
