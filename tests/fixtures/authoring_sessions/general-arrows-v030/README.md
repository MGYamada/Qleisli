# General pure arrow boundary study

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

This informed #83 study preserves six desired sources using `Op<A -> B>`:
preparation, a Unit/Bit unitor, an incorrect Unitary assertion, a wrong input
provider, zero repetition of a rectangular operation, and a requested controlled
rectangular operation. The Arrow token separates the codomain from the existing
comma Meaning slot. The first sources were written before that syntax was
implemented; their observations preserve that boundary.

All six first checks fail at the project manifest: the author accidentally used
`schema = 2`. Attempt-02 changes only the manifest to the existing
`schema-version = 2` contract; every source is byte-identical. Its six actual
checks reject `->` while expecting `>`. The first twelve observations, manifest
mistake and unchanged sources remain in [session.json](session.json). Those
parser refusals do not establish any downstream effect, capability or type rule.

The intended independent small preparation result is `(1/sqrt(2), 1/sqrt(2))`.
The unitor should retain the input bit coefficients, phase and external frame.
Twelve subsequent observations retain both pre-repair general-arrow checks and
the checks after forward provider lowering was repaired. Preparation initially
failed at a producer Unit-only restriction; the unitor initially failed because
the adapter changed its owner type. Both unchanged clients now pass actual
native CLI checking. The four negative clients reject at common effect/type
checking. There are 24 observations in total; no earlier record was overwritten.

`tests/general_operation_arrows.rs` compares the two positive clients' small
complex execution with literal expectations, including both unitor basis inputs.
It also tests ordered Basis substitution, phase, external entry bindings and
whole-source rejection. Internal tests in
`src/frontend/specialize/lower/preservation/isometry_tests.rs` use independently
authored exact native requests and an external reference. A separate wrong-gate
experiment confirms initialization-movement checking alone does not establish
the full gate meaning; the independent exact H request rejects a native-valid X
substitution. These are bounded regression checks, not general preservation.
General composite/transform lowering and rectangular Meaning evidence remain
open under #83/#46. The finite profile rejects explicit general-arrow lowering.
No external model, generic QFT or maximum-size case was used.
