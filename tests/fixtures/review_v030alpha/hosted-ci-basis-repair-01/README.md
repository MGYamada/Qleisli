# Canonical coherent unitor control after the syntax migration

The current positive integration control previously read the first authoring
source in `quantum-tuple-unitors-v030/attempt-01/finite-coherent-unitors`.
That source deliberately retains historical `do/pure` spelling. Its bytes,
manifest, observations and original unitor equations remain unchanged.

`finite-coherent-unitors/` is an explicit derived project under the adopted
[Issue #81](https://github.com/MGYamada/Qleisli/issues/81) migration. Only the
three coherent-map bodies change to `basis q as p { e }`. Visibility, signatures,
effects, complete Unit/Bit trees, input owners, output axis order and coefficient
`+1` are preserved. The pre-edit test and exact original source/manifest are
frozen here; `provenance-before-validation.json` records identities, the three
literal substitutions and bounded predictions before validation.

The integration test keeps the finite split/join positive control and its
located raw-profile refusal. The canonical coherent project must still pass
finite checking and refuse selected CoherentLift instantiation. The untouched
first source separately must reject at its exact first `do` bytes through both
finite loading and selected parsing, with the current migration diagnostic.
Other ownership, phase, reference and independent action-oracle cases in the
test file are unchanged.

No Cargo/native/CLI execution was performed by the source preparer. Actual
validation belongs in separate records added by the integration owner. This
source preparation establishes no general preservation theorem, new primitive,
constitutional guarantee, completed release gate or issue-completion credit.

The integration owner subsequently ran all eleven tests in
`quantum_tuple_unitors` on Rust 1.98.1 and MSRV 1.85.0: both passed with no
ignored tests. Targeted Cargo Clippy with `-D warnings` passed on both
toolchains, and formatting passed. Exact commands and streams are in
`validation-01/`; the separate validation record binds their identities.
These local checks do not establish hosted full CI or distribution success.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
