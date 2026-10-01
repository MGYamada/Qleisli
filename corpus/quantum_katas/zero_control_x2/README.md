# zero_control_x2

Source: [TwoQubitGate4_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/BasicGates/ReferenceImplementation.qs).
License: **MIT**; [intake policy](../../POLICY.md).
The pinned original, license and required notices remain under `corpus/upstream/quantum_katas/`.

## Contract and scope

|a,b> -> |a,b xor (1-a)> with amplitude +1; retain the control and target on the whole input space.

Two input wires; preserves the upstream negative-control CNOT-then-X implementation. No array API or implicit control access.

The owner tree has 2 ordered Bit leaves. Its first leaf has integer weight 1;
`main` starts at all zero and prints those leaves from left to right. Every
input owner is consumed once and every output owner is returned. No scratch
escapes, and no observation occurs inside the unitary kernel.

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/zero_control_x2
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/zero_control_x2 --exhaustive
```

The independent oracle checks all basis columns and every complex entry through
controlled X/Y interference, including phase and bit order. The paired local
semantic fault must pass source checking before the oracle detects its wrong
meaning. See the [first-source session](../../authoring/v024-small/README.md).
Finite numerical checks do not prove translation correctness or execute the
upstream framework.
