# Six small-system translations for 0.2.5

The [session](session.json) preserves twelve complete first-source files before
checking. [Initial diagnostics](check-initial.json) accept five of six projects;
CZ incorrectly used a nonexistent `controlled_z` name. The second full snapshot
expresses that same operator with existing `qif`, `id` and `z`, and corrects QAOA
attribution against frozen metadata. [Repaired checks](check-repaired.json)
accept all six. One semantic-source repair was made; this is informed authoring
with prior repository/pattern access, not a controlled model evaluation.

| Frozen input | Kernel | Contract |
| --- | --- | --- |
| QuantumKatas `TwoQubitGate2_Reference` | `controlled_z2` | CZ phase on the whole two-wire space, including coherent control. |
| QuantumKatas `ToffoliGate_Reference` | `toffoli3` | Both controls retained; arbitrary target, no unintended one-control block. |
| Qualtran `LessThanEqual` | `less_equal1` | XOR inclusive one-bit comparison into either target value; restore inputs. |
| Qualtran `GreaterThan` | `greater_than1` | Strict one-bit comparison; complemented input restored. |
| PennyLane `circuit(params)` | `rotation_mixed_sign` | RY(-pi/2) RX(pi/2), exact scalar and noncommuting order. |
| PennyLane `U_B(beta)` | `qaoa_mixer2` | Two-wire RX(pi/2) product mixer, beta=pi/4, whole-space phase. |

[Semantic validation](semantic-validation.json) passes **490 probes** covering
every complex matrix entry and detects all six paired type-correct faults.
Independent signed-permutation/arithmetic/complex-coefficient oracles never read
QLI bodies to construct expected results. Tests use at most three data qubits,
four with the interference meter; tolerance 1e-11 issues no exact evidence.

Existing upstream commits, bytes, licenses and notices are unchanged. No new
stdlib API, language form, checker rule, maximum-size corpus case or framework
execution is added. These are narrowed kernels, not full general-algorithm
ports or translation proofs. The actual missing-name diagnostic and existing
explicit-control/scalar obligations accompany [Issue 19](https://github.com/MGYamada/Qleisli/issues/19)
and [Issue 21](https://github.com/MGYamada/Qleisli/issues/21).
