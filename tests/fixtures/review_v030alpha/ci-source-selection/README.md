# Current source selection and historical artifact review

This records a completed local repair unit, not completion of the whole-codebase
review. The original source and failing assertions remain in base commit
`241474ee2bce4e0631632d8ba51dcc1cf39a5d40`.
[Hosted run 37578949691](https://github.com/MGYamada/Qleisli/actions/runs/37578949691)
checked merge commit `41070c0a85cd1d2634e06c7ce3ec88c55426e635`.
The adjacent validation record binds the changed source and observed local runs.

## Findings and repairs

- Native round trips expected 14 migrated projects although 33 were selected.
  Migration history is authoritative for current leaves; independent enumeration
  still requires every logical project, without duplicates, and excludes old
  snapshots. Tests no longer duplicate mutable counts or stage names.
- The observing adapter assumed current roots had no evidence. It now preserves
  all dependency bodies, signatures and source identities, with only dependency
  indices topologically renamed. The independent exact Kraus evaluator checks
  both implementations and specifications. Native acceptance receives the
  original complete QIRF bytes, not a reconstructed evidence-free root.
- The baseline compared new compiler encodings byte-for-byte with historical
  QIRF. Historical bytes remain immutable and independently verified; current
  bytes receive their own native verification and exact operator comparison,
  including phase and ordered outcomes. Fixed expected distributions remain.

The adapter's fault tests cover dependency replacement, invalid/missing/cyclic
references, unsupported evidence and distinct basis trees. Existing migration
tests retain multistage, provenance, tamper, duplicate and missing-source checks.
Neither oracle is a new production acceptance path or a source-preservation proof.

The VM-22/29 inventory refresh covers the changed comparison programs and new
untrusted adapter only. Constructors, public Rust interfaces, acceptance routes,
historical IR and constitutional records are unchanged.

## Validation limits

Rust 1.98.1 and MSRV 1.85.0 each passed 960 tests across 102 targets, with 52
existing ignored tests. Both Clippy all-target runs passed. The observing and
streamed drivers passed 150/154 native cases and 143 Rust comparisons each;
the independent exact operator counts were 145/147. The baseline's 12 source
cases passed separately. Inventory, production coverage, documentation and
adapter tests passed. These local checks do not replace the clean-checkout
native manifest, distribution, proof or final hosted checks.

The ownership differential test alone took about six minutes per toolchain.
This is a measured cost, not evidence of nondeterminism or permission to remove
its independent coverage. No maximum-size fixture was generated.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
