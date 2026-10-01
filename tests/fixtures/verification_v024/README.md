# VM-24 finite evidence boundary

Status: **finite component implemented, actual-definition proofs built and native
comparisons passed in the working tree**. [Issue 128](https://github.com/MGYamada/Qleisli/issues/128)
tracks this v0.2.4 boundary move. Production authority remains Rust.

The contract was fixed before implementation on 2026-10-01, starting from the
[negative RX source](../../../corpus/authoring/v024-small/attempt-01/pennylane_demos/rx_negative_quarter/kernel.qli),
[lost-scalar counterexample](../../../corpus/semantic_faults/negative_rx_missing_scalar/kernel.qli)
and [modulo-four decrement](../../../corpus/qualtran/add_minus_one2/kernel.qli).
Their original sources/diagnostics remain intact. This is informed kernel
implementation, not a new authoring benchmark or a source-preservation proof.

## Actual moved boundary

The Mathlib-free [finite checker](../../../lean-kernel/QleisliKernel/Finite.lean)
receives original H/monomial/dependency steps, complete prefix type trees,
controls, ordered axes, encodings and the independently required root contract.
It reconstructs the physical matrix and checks `U E_in = E_out u`, isometric
encodings/logical maps and whole-space physical validity. `checkAll` starts with
an empty cache, requires dependencies to have been checked earlier, rejects
cycles/duplicate visits and checks every entry. Each callable dependency is the
actual reconstructed map with identity encodings; a restricted encoding cannot
become a whole-space call. No external cache or success flag is an input.

The [experimental adapter](../../../lean-kernel/Protocol.lean) freshly reads the
published `qleisli.finite-matrix` version-1 R8 description and a private finite
component envelope. It rejects duplicate/unknown fields, unsupported profiles,
noncanonical dyadics and malformed framing. The prefix type bridge and component
envelope are not public QIRF formats or production CLI modes. Parsing/byte-level
transport refinement and accepted-artifact execution remain VM-28/29.

## Proof and checking scope

The [data reference](../../../lean-kernel/QleisliKernel/Semantics/Finite.lean)
and [literal complex reference](../../../lean/Qleisli/Semantics/Finite.lean)
import no arithmetic/acceptance/transport module. The
[actual-definition bridge](../../../lean/Qleisli/Finite.lean) proves:

- Every successful local contribution and vector accumulation preserves literal
  complex amplitudes, including negative controls, ordered axes, adjoints and
  scalar Unit phases. Every reconstructed column has a complete mathematical
  execution trace of the original steps; no producer-computed matrix is assumed.
- Accepted encoded equations preserve action with arbitrary untouched reference
  systems, including entangled inputs and full scalar phase. Logical isometry
  preserves joint norms. Clean return follows from the actual independently
  required output encoding's zero amplitudes in every dirty row; a scratch name
  or lifetime is not evidence.
- Actual whole-space acceptance implies both inverse equations. Fresh complete
  artifact acceptance implies the independently requested root equation and both
  whole-space inverse laws. The original canonical description reader retains
  four independently reduced dyadics and exact row-major entries.

[Native validation](native-validation.json) records **222 Lean cases, 211 Rust
comparisons and 110 independent rational matrix checks**. The
[harness](../../../scripts/test_lean_finite.py) passes original data only; oracle
results and expected decisions are excluded from its native requests. Rust reads
original matrix bytes, constructs original circuits and checks selected ordinary
`CheckedContract` equations through unchanged public APIs. The separate oracle
composes rational gate matrices using closed polynomial formulas. Its negative
cases include phase, polarity, type/axis/dependency/request changes, coordinated
body/claim changes, dirty scratch, equal-image/different-coordinate encodings,
computed-encoding uncomputation, producer flags/caches, invalid JSON and work
exhaustion. Twenty-two graph faults and three deliberately damaged output/work
records are detected. [Input cases](native-inputs.json) also retain oracle data
for reproduction; those oracle fields are never sent to Lean.

Successful semantic circuits use at most three qubits. Capacity probes use Unit
or malformed inputs: 1,024/1,025 steps, exact H precharge, seven-bit rejection,
type depth 33 and dependency depth 32/33. Published matrix/direct-circuit/Gram
remaining-work comparisons are exact. Selected graph equations compare
acceptance and full matrices; their experimental aggregate budget additionally
reads all maps, checks whole-space Gram and rechecks the root. This is not a
change to production pricing. VM-28 must bind integration costs and transport
limits before production adoption. VM-23's 815 native comparisons also pass.

## Remaining premises

RawProgram extraction, owners/effects, original function bodies and source
identity remain VM-25/26. This finite component establishes no replacement seal
for raw evidence and no general source/lowering preservation theorem. Hierarchy
finite/root discharge remains VM-27. Native transport refinement, supported
platform packaging, fail-closed production dual checking and execution of the
exact accepted artifact remain VM-28/29. Rust-only installation/public APIs stay
intact, external schemas remain disabled, and S05 authority transfer remains
separate from this component proof.

[Boundary validation](boundary-validation.json) records actual commands and
later premises. [Registry validation](registry-validation.json) records both package builds,
compiled-declaration/axiom audits, runtime source policy, fresh proof replay and
actual schema type export. Schema IDs, checker/theorem types, domains and disabled
external entries are unchanged. VM-22 adds two finite source pins and reviews the
root import/Protocol hashes; original Rust surfaces and frozen 36-case/12-fault
comparison bytes remain unchanged. Version selection, tagging and publication
remain separate.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
