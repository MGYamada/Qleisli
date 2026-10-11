# Explicit checked-operation spelling migration

[Issue #82's ordinary decision](https://github.com/MGYamada/Qleisli/issues/82#issuecomment-6009162442)
selects the reserved spelling `checked_op(unitary, meaning)` for the existing
checked operation value. The [Reference](../../../../docs/src/reference/checked-operations.md)
retains `StaticOpKind::Bind`, identifier arguments and the existing evidence
checks. This packet does not introduce a native, schema or capability change.

[First provenance](first-provenance.json) records the eight final selected
predecessor files, three earlier maps and selector inputs before generation.
[The derivative record](derivatives-01.json) preserves that preparation state.
Each new `.qli` file replaces exactly one `bind_op` token with `checked_op`;
all other bytes are identical to its recorded predecessor. Historical sources,
earlier current snapshots, maps and first observations remain unchanged.

[The source map](source-map.json) provides both SHA-256 identities for eight
explicit file links and contains no project links. The shared selector requires
this map after the namespace and coherent-basis maps, including for unmapped
inputs. Selection checks every traversed predecessor and destination, rejects
malformed metadata and escaping paths, and preserves complete project inventory
checks. It does not rewrite arbitrary source or issue an accepted handle.

`python3 -B scripts/test_current_source_fixtures.py` passed 41 tests. Its controls
include missing maps, changed earlier links hidden by a later record, missing
or extra project inputs, invalid hashes, duplicate fields and symlink escapes.
A separate metadata-only check verified the eight actual complete file chains,
exact token replacements, complete current `.qli` inventory and unchanged prior
maps. Compiler, Rust, Lean and semantic validation belong to the integration
records maintained separately under `implementation-01/`; these selector checks
are not a preservation theorem or a new constitutional guarantee.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
