# Fourier binding: first attempts and current scope

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The [work packet](../fourier-binding-packet.md) fixes the complete target before
implementation. This is informed development, not a controlled model benchmark.

- [First coefficient source](HierarchicalFourier-first.lean.txt) and
  [actual initial diagnostics](first-check.log) retain the initial arithmetic
  and dependent-coordinate failures. Repairs use explicit high/low-bit number
  identities and preserve the phase of every coefficient.
- [First generated native source](FourierStage-first.lean.txt) was saved before
  building. [Its first build](../fourier-stage-native-first.json) failed because
  the mutation harness used `.product` instead of the actual `.tuple` type atom.
  Repairing that fixture spelling left the acceptance expectations unchanged.

The current sources are [universal coefficient laws](../../../../lean/Qleisli/HierarchicalFourier.lean),
[pure stage inspection](../../../../lean-kernel/QleisliKernel/Hierarchical/FourierStage.lean),
[actual evaluation binding](../../../../lean/Qleisli/HierarchicalFourierStage.lean),
and [native/independent oracles](../../../../scripts/test_hierarchical_fourier_stage.py).
The [current native record](../fourier-stage-native.json) has 144 outcomes and
168 complex vectors, including correlated-reference columns.

This checkpoint establishes the five-node stage geometry and its conditional
coefficient theorem. The one-bit base, full finite H obligation, controlled
gradient/recursive composition, actual outer reversal and independently requested
root remain to be connected. A pending stage is not Fourier evidence; all
external schemas remain disabled and the full v0.2.1 goal remains open.
