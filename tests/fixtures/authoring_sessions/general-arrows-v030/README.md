# General pure arrow boundary study

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

This informed #83 study preserves six desired sources using `Op<A -> B>`:
preparation, a Unit/Bit unitor, an incorrect Unitary assertion, a wrong input
provider, zero repetition of a rectangular operation, and a requested controlled
rectangular operation. The Arrow token separates the codomain from the existing
comma Meaning slot. These are desired programs, not implemented syntax or proof.

All six first checks fail at the project manifest: the author accidentally used
`schema = 2`. Attempt-02 changes only the manifest to the existing
`schema-version = 2` contract; every source is byte-identical. Its six actual
checks reject `->` while expecting `>`. The twelve observations, first manifest
mistake and unchanged sources remain in [session.json](session.json). Those
parser refusals do not establish any downstream effect, capability or type rule.

The intended independent small preparation result is `(1/sqrt(2), 1/sqrt(2))`.
The unitor should retain the input bit coefficients, phase and external frame.
These expectations have not yet been compared with execution of these clients.
The effect-ceiling prerequisite has separate internal tests; it does not enable
general arrows, native arrow composition or their capability laws. General
arrow acceptance, lowering and independent semantics remain open under #83.
No external model, generic QFT or maximum-size case was used.
