# Independent producer const header migration

This bounded [Issue #33](https://github.com/MGYamada/Qleisli/issues/33#issuecomment-6049900733)
change aligns the independent Python proposal parser with the adopted contextual
`const` marker. Historical `static` headers remain temporary migration inputs;
ordinary const-named functions, parameters and values remain identifiers.
No corpus source, graph semantics, acceptance rule or capability is changed.

[Before](before.json) retains the desired first source and actual pre-edit
diagnostic against the parser at Git commit
d926101e0bb555de86d1c47295fa6fcd0c54e464 (the parser identity is also recorded by SHA-256).
[After](after.json) retains the same source and successful parsed declaration
against the edited parser. These are informed implementation observations,
not a controlled model benchmark or proof.

`python3 scripts/test_sized_local_resolution.py` passed all nineteen tests:
the sixteen existing regressions plus ordered Nat/Op marker equivalence,
contextual names and small proposal equivalence at widths 0/1/2,
and explicit-marker rejection. Both pure and instrument parser paths are tested.
The observing parser shares this header implementation; a full observing runtime
comparison was not run for this unit. Rust and Lean definitions are unchanged.

[Small validation](small-validation.json) records the existing small-system
Xor/GHZ native comparisons, full basis/reference-column oracles, four semantic
faults, two invalid IR refusals and sixteen source refusals. Run with
`python3 scripts/test_sized_corpus.py --small --record <path>` and the existing
audited kernel selected by `QLEISLI_KERNEL`/`QLEISLI_HIERARCHY_KERNEL`.
Earlier validation records and source snapshots were not regenerated.
This does not complete #33, broader source preservation or QS/PR/RS obligations.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
