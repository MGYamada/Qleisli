# Six small-system translations for 0.2.6

[First sources](session.json) were saved/hashed before checking, with prior
repository, frozen-input and oracle context. [Initial checks](check-initial.json)
accept four projects; two reflection sources mistakenly put the repeat_static
count second. The complete second snapshot puts the count first, as specified;
[repaired checks](check-repaired.json) accept all six. Two source repairs, one
syntax correction pattern; this is informed authoring, not controlled model evaluation.

| Source | Case | Obligation |
| --- | --- | --- |
| QuantumKatas | phased_uniform2 | Signed/imaginary coefficients of ZH tensor SH |
| QuantumKatas | graph_state2 | CZ after H², negative edge phase on all input columns |
| Qualtran | reflection_minus1 | PREPARE=H, global_phase=-1 and exact private cleanup |
| Qualtran | control_zero_reflection2 | Zero-controlled reflection, including its relative scalar |
| PennyLane | rotation_half_y | RY(pi) RX(pi/2), noncommuting order and scalar |
| PennyLane | ising_zz_negative2 | One negative-angle ZZ edge, exact RZ scalar |

[Semantic replay](semantic-validation.json) covers 164 probes (all complex
entries via control X/Y interference) and detects six paired type-correct
faults. New kernels have at most two data qubits. Interference probes add one meter;
reflection scopes specify one private flag, eliminated where statically extracted. Tolerance 1e-11 issues no exact evidence. Independent analytic
oracles do not inspect the QLI bodies to construct expected values. No new
maximum-size system, upstream framework run, stdlib API or acceptance rule.

Upstream bytes, pins, licenses and notices remain unchanged. These are narrowed
kernels, not general algorithm ports or translation proofs. The real count-order
repair is recorded alongside the existing source-form/control obligations in
[Issue 19](https://github.com/MGYamada/Qleisli/issues/19) and
[Issue 21](https://github.com/MGYamada/Qleisli/issues/21); no new syntax is adopted.
