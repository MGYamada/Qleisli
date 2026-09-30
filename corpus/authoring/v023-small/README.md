# Six small-system translations for 0.2.3

[session.json](session.json) pins twelve complete first-source files saved before
their first QLI checks. [Actual diagnostics](check-initial.json) record all six
successes without source repair. Known tuple/rotation workarounds, existing
translations and the driver template were available. This is informed authoring,
not a controlled model benchmark. Compiler and source hashes bind the observations.

| Frozen source | Selected translation | Explicit narrowing |
| --- | --- | --- |
| QuantumKatas `AllStatesWithParitySuperposition_Reference` | `odd_parity3` | Three wires, odd parity; common recursive Hadamards and conditional flips retain the full unitary. |
| QuantumKatas `AllBellStates_Reference` | `bell_singlet2` | Two wires, fixed classical index 3; exact Z/X order and scalar sign. |
| Qualtran `LessThanConstant` | `less_than_constant2` | Unsigned width 2, threshold 3, arbitrary target. |
| Qualtran `EqualsAConstant` | `equals_constant2` | Unsigned width 2, constant 1, restored mixed-polarity controls. |
| PennyLane `circuit(params)` | `ry_quarter` | Params=(0,pi/2), no optimizer or continuous angles. |
| PennyLane `U_C(gamma)` | `ising_zz_quarter2` | One edge, gamma=pi/2, no full graph/mixer/optimizer. |

Only existing pinned upstream files are reused. Microsoft MIT notices and
Qualtran Google Apache-2.0 notices remain on translations. PennyLane's frozen
metadata names `josh` for qubit rotation and `alowe`, `Jay` for MaxCut; their
Apache-2.0 notices and modification attribution are retained. No assets, helper
implementations or upstream dependencies are imported. See the
[policy](../../POLICY.md) and [manifest](../../manifest.json).

[semantic-validation.json](semantic-validation.json) checks 490 probes against
independent signed coefficients, integer predicates and Pauli exponentials.
Every complex entry is observed through controlled X/Y interference, so scalar
phase cannot disappear behind output probabilities. All six deliberate faults
first pass source checking and then disagree with the numerical oracle. They
are labelled local mutations, not authoring repairs or new external sources.
Validation uses at most three data qubits (four including the interference meter).
No new maximum-size case, syntax, standard API or acceptance rule is introduced.
Finite numerical agreement is not a proof or upstream-framework execution.
