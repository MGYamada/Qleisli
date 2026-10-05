# Isometry adapter inventory review

This record refreshes the current source identities after review of the Iso
adapter. It does not change production authority, route classification,
constructor coverage, capacities, proof gates or constitutional guarantee scope.

Both checker sources were read before the metadata edits. The fixed `review.py`
driver invokes only `scripts/check_verification_inventory.py` and
`scripts/check_production_coverage.py`; it never executes commands supplied by
a record. Its source map covers the checking files discovered by the inventory:
Rust, Python and stdlib source plus Mathlib-free Lean source, excluding `.lake`.
That map was identical before and after every run and across all three phases,
with SHA-256 `ced74868cc57153ab711fdd5cd56149ff4c1e15b97def2196e26328d916aa0f0`.

| Captured phase | Inventory | Coverage | Actual result |
| --- | --- | --- | --- |
| `before/` | exit 1 | exit 0 | Inventory rejected the stale `source_plan.rs` hash. Coverage still matched the old inventory, so its success alone did not validate current source identity. |
| `inventory-refreshed/` | exit 0 | exit 1 | The reviewed inventory passed; coverage rejected its stale surface digest. |
| `after/` | exit 0 | exit 0 | Both refreshed metadata checks passed. |

`metadata-changes.json` lists the three changed source hashes, the newly
inventoried private `isometry_tests.rs` file and the derived coverage digest.
All existing public signatures and capacity constants were unchanged. The
private test file has no public declarations, functions or capacity constants
and joins the existing `sized-source` group. Source snapshots increase from
250 to 251. `diff-audit.json` records an exact JSON comparison with the prior
HEAD metadata: every other inventory section and coverage field is unchanged.

The final guards account for 269 constructors, 36 groups, 20 public boundaries,
21 production paths and nine native modes. S05-C1–C5 remain open. These guards
check identities, declarations, bindings and test existence; they do not run
the referenced tests or prove source/native/runtime correspondence. No Cargo
or Lean build/audit/replay, guarantee admission or release validation was
performed in this review. The adapter's actual semantic tests have separate
records in the enclosing fixture.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
