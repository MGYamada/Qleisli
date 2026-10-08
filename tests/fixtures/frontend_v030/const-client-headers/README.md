# Current client parameter headers

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Issue [#33](https://github.com/MGYamada/Qleisli/issues/33), following commit
`9f1c4fbdafe102ef9b68df7e2711023de1d9b560`. This selection stage migrates
21 individual current source files and three current projects: the generic
verification client and both observing QPE source comparisons. All historical
sources and preceding migration records remain unchanged. Only `static`
parameter-header markers become contextual `const`; no loop marker, body,
effect, interface, edition manifest or license is changed.

The independent inventory test derives eligible files from preceding selection
stages and the actual sized/measured client directories. Projects are checked
against the original logical-project registry and their final preceding stage.
It compares exact transformed bytes, complete source inventories and hashes;
missing stages reject. Counts are reported outcomes, not separately maintained
selection criteria. Generic QFT and delayed Fourier headers are excluded.

`validation.json` records exact equality of three small pure and three instrument
proposals. Instrument source hash maps are independently checked before exclusion
from object equality. The independent complex/instrument client tests passed,
including their native checks and negative cases. Both source-only observing QPE
comparisons checked the original frozen source hashes, executed the selected
projects and passed 32 independent probability comparisons on latest and MSRV.

Six related Rust targets passed on both toolchains; existing ignored cases were
retained. Fixture selection passed 55 tests, shared source integrity passed all
five commands, and docs passed. No production Rust or Lean definition changed.
The previous commit `5d4c50ac2a0f6da47bbbc990385fa3027e210153` passed full CI
run 37723343703 on attempt 1; that does not establish full CI for these new edits.
No ownership cases were removed or cached. This unit did not rerun the unchanged
4,000-case suite or claim a fresh Lean replay or constitutional guarantee.
