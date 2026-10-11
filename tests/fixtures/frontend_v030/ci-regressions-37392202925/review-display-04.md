# Independent canonical-display and metadata review

Recorded 2026-10-06T00:52:59Z. This reviewer did not author the changes to
`src/frontend/check/normalize.rs` or `src/frontend/sized/linear.rs`.
The review read their actual diff and surrounding type, binder and comparison
code. It ran no tests, builds, native checks, Lean replay or semantic oracle.
The only new file produced by this review is this record.

Constitutional startup was completed earlier in this uninterrupted review
context using continuity base
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`.
This review adopts no interpretation or guarantee and makes no proof,
source-preservation, runtime, full-CI or release claim.

No actionable defect was found in the two display changes.

## Source inspection

`normalize::expect` performs the existing bounded `equivalent` judgment first.
Canonical type rendering is reached only after that judgment returns false.
No successful-path type comparison, solver call, owner rule or budget charge
was changed by the reviewed hunk. `Type::display(Stage::Runtime)` retains
explicit Q ownership, complete immediate tuple nesting, Unit, Bit, Bits and
named Basis spelling. It does not insert splitting or coercion.

`Linear::Display` borrows the existing ordered terms and constant. It performs
no coefficient addition, multiplication, signed negation, map normalization
or key replacement. Both coefficients and constants use `unsigned_abs`.
Thus the magnitude of `i128::MIN` is representable as `u128` and can be printed
with the preceding minus sign; `i128::MAX` is printed without negation.
The following are reasoning checks of the code, not executed formatter tests:

- First negative terms receive `-`; subsequent positive terms receive `+`.
  Subsequent negative terms receive their own `-`.
- Coefficients +1 and -1 omit the magnitude; other magnitudes precede `*name`.
- Zero terms are skipped. A zero constant is omitted after a nonzero term,
  while an entirely zero expression prints `0`.
- Nonzero constants receive the appropriate separator even after a term.

BinderKey comparison and Linear equality remain derived from the stored
identity-bearing keys, not the rendered spelling. Two distinct binders named
`n` remain distinct terms; printing `n+n` or `n-n` is not a certificate that
their identities or mathematical values coincide. Conversely, the existing
context may establish equality between differently rendered affine forms.
The formatter is a diagnostic view, not an identity encoding or solver oracle.
The existing Debug representation is unchanged.

## Metadata observations

`metadata-update-03.json` is internally consistent with the recorded source
hashes in the current inventory and its recorded coverage identity. Its three
continued source transitions match `metadata-update-02.json`. Inventory fields
other than source hashes, and coverage fields other than `surface_sha256`,
match HEAD. The coverage identity recomputed by the documented canonical JSON
projection is
`6a0b3f2b9dc39fd963b44fc5c70494a6effe12b79a979d426db164273e4aade4`,
matching both coverage and metadata-update-03. This is an identity observation,
not execution of either inventory/coverage checker.

At this review snapshot, exactly three inventory source hashes lag the latest
diagnostic provenance mark. The integrator has explicitly reserved their
refresh for a new metadata-update-04 record:

| Path | Recorded inventory hash | Current byte hash |
| --- | --- | --- |
| `src/frontend/check.rs` | `cbe9bf52967f7200181079ff9a11a6ec499cfd6f0445f822566553abeb05ae3d` | `f0060cecd778ff199ada98d24776244427c0309f4637004ac46a21dff0f9b6e5` |
| `src/frontend/check/body/operations.rs` | `cc10b70d978675f968fe30b340d55c9612dd18d10225643239e85a791a51d90a` | `6d6faa315e9b7839be68df81b68371918ccd721b8d3053fd3f2f3e12215809c4` |
| `src/frontend/sized/check.rs` | `be72b25e2000eca319d9b4fe554804270d0f297620ace9a29d961cfc2a85d000` | `238ffb9c786351885b13ac78980a70bcaceaaf1c94a1248b9b379ade1433728b` |

Consequently this record does not claim that the inventory currently binds
every current source byte or that metadata-update-03 covers those later edits.
Historical metadata and validation records are not rewritten by this review.

## Exact bytes reviewed

| Path | SHA-256 |
| --- | --- |
| `src/frontend/check/normalize.rs` | `bd8dfc2f928bee5415a232d4b220b03e2200cc88ebf27886aaaa850291a8c68f` |
| `src/frontend/sized/linear.rs` | `98a0d14d0052e2281cc4c4b07e41f92c933ff836eb43cb0eda285cc07a66874e` |
| `src/frontend/types.rs` | `7ecb70d63535c3aed4083979c9ca1140831f150e52f80e155a07403d511229c1` |
| `src/frontend/resolve/locals.rs` | `01c50d14dc89756d4d4131a0bbb0a01d3bfe1c83fe54ea451d3f980195ad7ed4` |
| `tests/fixtures/verification_v022/inventory.json` | `fcf95bede317cbf0a3456f3dfd4b5ef6debfa7455347ff06451fc9ea5447854d` |
| `tests/fixtures/verification_v029/coverage.json` | `30ab4681567c98451f5100d5473a7abd1bb8b7af2bf9a4c9fe6e772c2e98dc15` |
| `tests/fixtures/frontend_v030/ci-regressions-37392202925/metadata-update-03.json` | `779d382f879f28084e663e700eca586220fd0e7226b525975fa29afa6354e329` |

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
