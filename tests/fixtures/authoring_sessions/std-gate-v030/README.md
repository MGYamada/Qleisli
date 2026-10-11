# Provisional ordinary std::gate first clients

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

The maintainer selected `std::gate` and ordinary `.qli` provisional definitions
for `swap` and `permute_axes`. The informed context, first two complete clients
and source hashes were preserved before implementation. No external model was
invoked and no blind authoring benchmark is claimed. The session binds four
actual CLI checks: both first clients reject the missing module before the
change, then pass with unchanged source/manifest bytes. Source checks alone
neither execute the desired distribution nor prove mathematical meaning.

Both interfaces are explicitly two-Bit. Physical `swap` retains output wire
order and performs three CNOTs; `permute_axes` returns reversed axes with the
exact map `[1,0]` and no physical gate instruction. Separate tests exercise the
actual ordinary std imports through both public paths, full exact complex
coefficients, wire order, retained work and independently rejected native-valid
wrong circuits. Explicit-access closed clients return the independently
expected `(1,0)` for the written input `(0,1)`.

No new primitive, generic register SWAP, arbitrary permutation facility,
routing-cost guarantee or constitutional discharge is claimed. The module
consumes an existing slot/byte budget; no operational ceiling is increased.
The observed executable hashes bind bytes, not build provenance or source
preservation. First observations are immutable and are not regenerated.
