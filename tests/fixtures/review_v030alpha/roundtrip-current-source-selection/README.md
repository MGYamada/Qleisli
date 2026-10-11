# Current corpus selection in native roundtrip tests

The hosted run [37218876223, Rust job 111485304581](https://github.com/MGYamada/Qleisli/actions/runs/37218876223/job/111485304581)
failed while compiling the preserved predicate-domain migration copy of
`pennylane_demos/phase_lock`. The copy still contains the historical `CBit`
spelling. The native roundtrip test recursively searched all of `corpus/`,
which accidentally included the newly added migration archive. This was a
project-discovery error, not a failure to apply the ordered provenance overlays.

`inspection.json` binds the original job log, exact checkout/failure excerpts,
synthetic merge and branch identity. The stored excerpts retain their original
timestamped bytes and one-based line ranges. The full 99,879-byte log was fetched
locally; only its digest and the relevant excerpts are retained here.

The repaired selector visits examples and the three approved provider roots,
matching the existing corpus smoke test and corpus validator. Its independent
Rust discovery regression requires every current provider project, rejects
duplicate roots and excludes the preserved migration projects. It reads only
paths. The actual compile/native-acceptance/re-encoding/cache checks, minimum
project count and evidence-receipt guard remain unchanged.

The filesystem inspection selected 101 current projects (14 examples and all
87 manifest corpus projects), excluding 93 archived migration projects. It
records the exact selected paths and all migration-file hashes. This inspection
uses Python to compare the two selection rules; it is not a Rust or native
execution result. The first inspection source digest precedes a formatting-only
change. `files.json` binds the final test source and packet files.

The related discovery audit found that `tests/input_corpus.rs` already selects
the three provider roots, `scripts/check_input_corpus.py` validates their exact
manifest set, and `scripts/test_lean_raw.py` selects six explicit current
projects. The existing roundtrip recorder hashes all source inputs for
stability but does not compile every file it hashes. No additional active
corpus-wide recursion required a change in this audit.

No historical source, migration record, manifest, native rule or format oracle
was changed. Cargo/Lean builds and the full hosted replay remain pending when
this packet is authored. Subsequent validation must retain its own command and
source identities instead of replacing the hosted failure.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
