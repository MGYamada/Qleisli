# Canonical ordinary type migration

Issue #27 replaces source `CBit` / `CBits<n>` with ordinary `Bit` / `Bits<n>`,
`false` / `true` with `0` / `1`, and the old empty tuple type spelling with
`Unit`. Quantum ownership remains explicit in `Q<A>`. This is a source
migration, with no upstream, native schema, capacity, or acceptance-authority
change.

`migration.json` follows the prior predicate-domain migration and the exact
latest immutable authoring snapshots. Its 174 source entries are complete
snapshots of all 87 affected projects. `sources/` contains their exact current
bytes. Historical sessions, attempts, observations, licenses and upstream
snapshots are unchanged.

`checks.json` records all 87 actual native source checks, each successful,
including argv, cwd, streams, binary/kernel identities and compiled-source
hashes. No rebuild was performed: the existing independent after CLI was used.
All compiled Rust files and embedded stdlib files matched its saved input
manifest both before and after these commands. A later frontend type-module
comment and root-owned crate documentation may differ; those are not silently
substituted into the recorded build identity. Native source checking alone
does not prove source preservation or replace the independent small-system
semantic comparisons.

`sized-local-identities.json` separately records the two changed local measured
QPE source hashes. These local compositions are not upstream authoring
projects. Their current generic/lowering checks and independent Unit/readout
execution observations are recorded in the ordinary type cutover fixtures.
The migration metadata validator has passed against the complete current
corpus. No maximum-size quantum cases were generated or checked for this
record.
