# Execution-view binding: original controls and encoding vectors

The `before/` files are exact copies of the external study made against source
`e1816954b64aaf399dc29aeb69299f14be4815a4`, before #362 implementation. The
[manifest](baseline.json) binds all 86 original files by SHA-256. The first
context, sources, commands, failed attempts and raw stdout/stderr are unchanged.
Absolute paths in observations describe the historical commands; integrity
readers never execute them.

Four original `.qli` projects cover Bell preparation/readout, HTH phase
interference, Bell partial discard and a falsely asserted unitary observing
body. The first three check/run/emit successfully; the last rejects. Three
initial direct native calls omitted the mandatory product version and reject;
appended calls using the identical packets and correct argument accept. The
16 observations retain both attempts. An independent numerical oracle agrees
with the three tiny distributions within 1e-12; this is numerical QA, not exact
source/runtime proof.

The seven Unicode artifacts have a valid H circuit-evidence positive control.
All seven original native checks accept. Rust rejects the two lone-surrogate
variants and accepts ASCII, a valid surrogate pair, its literal non-BMP spelling
and escaped/literal U+FFFD. The 14 raw observations demonstrate conservative
host refusal, not execution of a differently decoded program. Original source
text in the evidence is inert identity metadata, not a compiler-preservation
witness.

[Eighteen shared encoding vectors](canonical-vectors.json) specify QDV1 bytes
independently of either implementation. They test the primitive
[encoding contract](../../../../docs/src/reference/execution-view.md), not
complete finite/hierarchy profiles or production acceptance. This fixture
supplies no #362 completion credit, new guarantee or release approval.

## Typed finite vectors

`finite-walker-vectors.json` supplies manually specified decoded descriptions
for the three original observing roots, all 21 Raw constructors, both branch
arms, zero-width owners, distinct type trees and rectangular exact matrices.
The all-constructors row tests transport only; its concatenated operations are
not claimed to form an accepted program. Rust and Lean independently read
typed data and compare their encodings to these descriptions. The production
native protocol and acceptance authority are unchanged at this stage.

`function-cache-vectors.json` gives ten independent full function-view
expectations, including exact H–T–H coefficients, a zero-width Unit owner,
branch routes that compose or cancel, protected/certified ancilla phase,
quantum conditional phase and an adjoint dependency. Lean checks each body
freshly and derives the expected circuit; Rust checks its actual retained
circuit/matrix caches. The last row's dependency zero means the first corpus
entry. Rust maps the actual reconstructed Arc to that explicit corpus index;
this is not a claim about the enclosing native packet's entry ordering.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
