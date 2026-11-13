# Indexed access in a finite project

The [first project](project/main.qli) puts a Hadamard on one bit, uses that
bit as `ctrl` and the other as `excl`, then observes the returned register.
The [edition 2026 manifest](project/Qargo.toml) and source are unchanged
across the observations.

- [Initial check](first-check.json) on `7ed1ba4cb47cb4d43d34c453c36a47437d895778`
  refused the selected argument at the finite-profile boundary.
- [Intermediate check](duplicate-plan-check.json) recorded a duplicate
  retained static plan. The compiler now uses the existing selector roots.
- [Current run](current-run.json) observes `00` and `11` with equal
  probabilities up to simulation rounding.

The commands were `qleisli check PROJECT --format=json` and
`qleisli run PROJECT --format=json`, with the repository's native checker
selected. The JSON observations are inert. The separate project regression
in [exclusive_access.rs](../../../exclusive_access.rs) checks the exact action
of reverse-order indexed calls and scalar slice phase against explicit owner
flow, with axis and phase counterexamples.
