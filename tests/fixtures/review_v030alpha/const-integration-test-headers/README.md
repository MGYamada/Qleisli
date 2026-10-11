# Current integration-test header migration

This [Issue #33 unit](https://github.com/MGYamada/Qleisli/issues/33#issuecomment-6050403486)
migrates 217 parameter-header markers in 27 current integration-test sources.
The initial desired rewrite included one historical lookup needle, which remains
`static` because it matches bytes in an unchanged first-source fixture; its
generated declaration uses `const`. Frozen fixtures and Rust static variables
are unchanged. Original complete sources remain at the exact Git commit in
[the record](record.json), with before/initial-desired/final hashes.

All 27 targets passed before and after on Rust latest and the pinned MSRV:
310 tests per toolchain, with identical named outcomes and twelve existing ignored
tests. Seed 42 and all 512 linear-size cases remain unchanged. Actual native
acceptance and phase/reference/provider mutation checks still execute; no result
cache or case reduction is introduced. The separate 4,000-case ownership suite
is unchanged and was not rerun for this client-only unit; full CI retains it.
Both all-target Clippy checks and Rustfmt passed.

The initial migration failed an existing nested-provider test on both toolchains:
changing the historical lookup needle prevented insertion of a required Nat
parameter. The actual diagnostic and correction are recorded. Matching strings
in retained historical input must not be confused with generated current source.
Rust code outside literals compares unchanged after masking whitespace, except
Rustfmt's optional trailing argument comma in one `rejects` call.

VM-22 refreshes only its two current comparison pins (`sized_cli` and
`sized_linear_seeded`), after checking their original identities. No frozen
comparison file, current public-source row, boundary, constructor or capacity
changes. The reviewed VM-29 surface identity is unchanged for these pins.
Before/after elapsed times include compilation, warm target reuse and competing
processes; they are observations, not a performance claim.

This does not complete #33's corpus/history client migration or legacy retirement,
algorithm obligations, source preservation or broader QS/PR/RS guarantees.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
