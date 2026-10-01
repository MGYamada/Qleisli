# Six small-system translations for 0.2.4

[session.json](session.json) pins twelve complete first-source files saved before
checking. [Initial diagnostics](check-initial.json) record six successful checks
with the baseline 0.2.3 compiler and zero source repairs. Existing driver,
tuple and exact-rotation workarounds were available; this is informed authoring,
not controlled model evaluation.

| Frozen source | Kernel | Contract exercised |
| --- | --- | --- |
| QuantumKatas `TwoQubitGate4_Reference` | `zero_control_x2` | Negative coherent control, preserving both owners. |
| QuantumKatas `BellStateChange3_Reference` | `bell_change_zx2` | Full ZX operator and its sign, distinct from XZ or Y. |
| Qualtran `AddK` | `add_minus_one2` | k=-1 modulo four, including zero underflow and borrow order. |
| Qualtran `QROM` | `qrom1` | data=[2,1], arbitrary two-bit target and retained one-bit address. |
| PennyLane `circuit(params)` | `rx_negative_quarter` | params=(-pi/2,0), adjoint access and exact scalar phase. |
| PennyLane `circuit(params)` | `ry_negative_quarter` | params=(0,-pi/2), signed columns and operation order. |

[Semantic validation](semantic-validation.json) records 264 probes covering
every complex matrix entry through controlled X/Y interference, with all six
paired type-correct faults detected. Independent arithmetic, signed permutation
and Pauli-exponential oracles do not read QLI bodies to obtain expected outputs.
New kernels use 1–3 data qubits, at most four including the interference meter.

Only already pinned files are reused; commits, upstream hashes, licenses and
notices remain unchanged. Every new translation returns all owners and adds no
stdlib API, language form or acceptance rule. Scalar erasure and reversed Bell
or RY ordering agree on ordinary basis probabilities, requiring the complex
probes. Existing Issues [#19](https://github.com/MGYamada/Qleisli/issues/19),
[#21](https://github.com/MGYamada/Qleisli/issues/21) and
[#39](https://github.com/MGYamada/Qleisli/issues/39) track the retained explicit
control/scalar/literal authoring obligations. No new maximum-size case,
upstream-framework execution, general translation proof or algorithm proof is
claimed.

The later [review migration](../../../tests/fixtures/review_v023/README.md)
adds a second complete attempt using `s` and `phase_eighth` for negative RX.
The initial workaround and its observations remain immutable.
[Real checks](review-checks.json) and [independent replay](review-semantics.json)
cover all six cases after migration. This is a curated source improvement, not
an additional first-attempt success or an algorithm proof.
