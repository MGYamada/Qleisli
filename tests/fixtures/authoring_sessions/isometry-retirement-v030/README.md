# Retirement of the legacy isometry prefix

This informed maintenance study follows Issue #57's adopted `isometry`
vocabulary. It is not a blind authoring benchmark. The context and both source
snapshots preceded the observations; neither source was repaired after checking.
Only `iso` versus `isometry` differs between the two programs. Both retain
schema-2 manifests declaring constitutional edition 2026.

The [session](session.json) binds the complete sources, manifests and eight
actual CLI observations. Before retirement, both sources checked and returned
the classical zero outcome with probability one. After retirement, the original
`iso` source fails `check` and `run` with `parse` at bytes 90–93, line 4,
column 1, recommending `isometry fn`. The canonical source still checks and
returns the same distribution. Each observation records the CLI digest before
and after its invocation; both digests agree in every record.

These observations establish this bounded migration behavior. They do not prove
source preservation, general isometry semantics or completion of Issue #57.
Versioned JSON effect tags remain `iso`; this source change does not change
native acceptance rules or grant inverse/control access. Lean public vocabulary
compatibility remains a separate step. The original observations are retained
alongside the subsequent results.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
