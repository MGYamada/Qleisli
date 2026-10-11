# Canonical ordinary types and literals: implementation record

This informed implementation follows Issue #27's adopted contract, retained in
`contract.md`. The preceding desired-source study remains unchanged in
`../ordinary-classical-types/`. This record is neither a blind authoring study
nor a general source-preservation proof. No new human guarantee admission,
native schema, quantum capacity, or native acceptance authority is introduced.

## Implementation boundary

Both frontend profiles use the same AST-to-`Type<N>` classifier for ordinary
`Unit`, `Bit`, `Bits<n>`, quantum `Q<A>`, and exact products. `0` and `1` are
ordinary and basis Bit literals. Explicit static natural expressions retain
their separate context. `CBit`, `CBits`, `true`, `false`, and the old `()` type
spelling reject with migration diagnostics; the value/pattern `()` remains.
No legacy source adapter repairs inputs during checking.

Sized Unit has its own constructor and no owner or value port. Unit patterns
match only Unit. Lowering and source-event reconstruction omit only ordinary
Unit ports and retain executed operations. `Bits<0>` and `Q<Bits<0>>` remain
separate from Unit; quantum owners are never removed by a width-zero rule.
The finite and sized lowering limits remain explicit. In particular, this
unit does not add general basis polymorphism, finite register lowering, sized
runtime Boolean evaluation, or general sized `Q<Unit>` support.

The independent 14-test suite and before/after source archives live in
`../ordinary-types-independent/`. It found and captured the intermediate
empty-Unit-pattern regression and its repair. Its 18 byte-identical outputs
and source-bearing comparison cover bounded phase/reference-sensitive actions.
The existing dropped-readout limitation, including its downstream module-less
`0..0` diagnostic, is preserved for later shared diagnostic work.

## Explicit migration inventories

`source-before.json` and `source-before.tar.gz` preserve the compiler input
before implementation. `active-migration-plan.json` binds 190 changed active
`.qli` files to exact `active-before/` and `active-current/` copies. The
`migrate_source.rs` tool was compiled against the pre-cutover Rust AST; its
recorded executable/library identities matter. It is historical migration
tooling, not a supported converter compiled against today's removed AST cases.

`historical-current-map.json` identifies 355 original/current fixture files.
Original authoring sessions, diagnostic observations, archives and manifests
remain byte-identical. Current copies under `current/` are selected explicitly
by the live Rust/Python harnesses. Complete selected fixture families include
unchanged companions and intentionally rejected inputs; their presence is not
a blanket acceptance or semantic validation claim. `migration-check.json`
records all 355 identity checks and the 149 changed source pairs: each original
rejects for removed spelling and each explicit current source parses. The
checker uses the documentation parser only; it does not issue native handles.

`client-before/` and `client-initial-migration.json` retain the initial live
Rust-client migration inputs. Later test expectation repairs are ordinary test
maintenance, not edits to those retained inputs. `changed-files.json` lists
the exact assigned tracked-file identities at handoff and the checks still
pending after the disk-space stop.

The corpus uses the append-only chain in
`../../../../corpus/migrations/ordinary-type-v030/`. Its complete 174-source
snapshot follows the prior predicate-domain overlay. All 87 affected projects
passed actual native source checking using the independently built after CLI,
with matching Rust/embedded-stdlib identities before and after the commands.
The two measured-QPE local composition hashes are recorded separately. No
historical authoring session JSON or upstream source identity was rewritten.

## Performed checks and remaining checks

- The library compiled, and all Rust integration targets compiled with
  `cargo test --offline --no-run --tests` before the disk-space stop.
- `client-tests-first/commands.json` records 26 completed targets: 24 passed
  (224 passed tests, five deliberately ignored cases). `compile` and
  `operation_parameters` each exposed one stale migration expectation. Their
  repairs are saved but have not been rerun. The following `iterative_qpe`
  target was interrupted during compilation and has no completed result.
- The successful targets include common parser/type/docs, sized source,
  source/IR correspondence, classical scope and effects, exact function and
  computed contracts, tuple/owner boundaries, and active algorithm examples.
  These are bounded regressions, not a general preservation theorem.
- `small-client-checks/` records five JSON CLI tests, six independent generated
  source/CLI probability comparisons (maximum four live qubits), 13 Python
  compaction tests, and seven authoring-session validator tests, all passed.
  These reused the existing isolated CLI and did not invoke Cargo.
- The Python instrument check separately produced a two-qubit QPE proposal,
  checked its preparation/readout components natively and compared its action
  to the independent oracle. It also checked existing negative source cases
  and rejection of obsolete classical return-type spelling. Whole hierarchy
  acceptance and the Cargo-based Python/Rust instrument bridge are pending.
- The frozen 799-input native archive remains unchanged, SHA-256
  `296c36efa109762fefe9386c9a5b53ac010f8aa94e7464f595c0bf3173f3fae1`.
  This identity check is not a new replay of all 799 inputs.

The independent fixture records its own successful Rust 1.98.1 Clippy run for
`ordinary_types`. Full all-target latest/MSRV Clippy, the two repaired Rust
expectations, remaining client targets, and full CI are not claimed complete
here. Use the actual Rust 1.85.0 toolchain directory at the front of `PATH`
when resuming MSRV checks. The later `types.rs` introduction change is comment
only; root-owned `src/lib.rs` documentation is tracked separately from the
frozen observed build. No maximum-size quantum cases were newly generated or
checked in this unit.
