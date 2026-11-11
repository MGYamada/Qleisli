# Informed axis-routing and diagnostic study

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

Root and one implementation agent used issue #76, the current Reference,
stdlib sources and existing regressions. This was informed maintenance,
not an independent first-author evaluation. Four original diagnostic sources
were frozen before the message changes; two paired export sources were frozen
before their regression implementation. The baseline is 75282f7c445472717bf59c9b57a21e4e40ea4175.

The first four CLI calls mistakenly used --json; their usage refusals are
preserved separately from the corrected --format=json observations. An early
after-observer tried to parse an empty/non-JSON stdout while Cargo was rebuilding
the shared CLI and raised JSONDecodeError. Its child exit/status and stderr were
not retained; no outcome is inferred from that attempt. The stable executable
observations below were captured later, with raw streams retained.

Zero-width logical owners still forbid binding exchange. Ordinary assignment
gets ordinary advice. The two public library interfaces remain two-Bit only.
For each paired export, independently expected ordered action is
|a,b> -> |b,a>, coefficient +1. Physical SWAP has three CNOT gates and
readout [0,1]; structural reordering has no gate instruction and readout [1,0].
The native encoded-contract regression separately checks all coefficients and
rejects valid target mutations of map, gate work and phase. Successful CLI
export alone is not that exact request, a general source/routing theorem,
physical hardware certification, quantitative resource proof or issue completion.

The CLI was built locally against the source; executable hashes identify bytes
but are not build attestations. Existing broader QS/PR/RS/EXACT duties and
the two admitted QLV1 ownership/scope guarantees retain their recorded scopes.
