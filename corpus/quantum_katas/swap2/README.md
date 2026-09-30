# Swap2

Source: [TwoQubitGate3_Reference](https://github.com/microsoft/QuantumKatas/blob/1a4740ff70ceffebde73d1434b2dedbe27643300/BasicGates/ReferenceImplementation.qs).
The [frozen original](../../upstream/quantum_katas/BasicGates__ReferenceImplementation.qs) retains its notices.
License: **MIT**; [intake policy](../../POLICY.md).

## Contract and finite translation

Map |a,b> to |b,a> with scalar +1 on the entire two-qubit space, preserving arbitrary reference correlations.

Translates the original three-CNOT SWAP on two fixed inputs. Both owners are returned; arrays, device placement and general-size registers are excluded.

Classification: ordinary case-local `.qli` definitions, with public interface
`Q<(Bit, Bit)> -> Q<(Bit, Bit)>` and effect `Unitary`. The kernel consumes each input
owner once and returns every owner; main explicitly prepares and measures.
Separate owners do not assert a product state. Integer bits use first-leaf
weight 1; result strings list leaves from left to right. Tuple shape is exact.
Existing gates, split/join and coherent control lower through the unchanged
independent Rust IR verifier; no language or standard-library API is added.
Duplicate/missing owners, incompatible shapes and observation in pure code
are rejected by existing checks. A type-correct wrong circuit needs semantic
validation rather than source checking alone.

```sh
cargo run --bin qleisli -- run corpus/quantum_katas/swap2
python3 scripts/check_input_corpus.py target/debug/qleisli --case quantum_katas/swap2 --exhaustive
```

The independent oracle checks every complex matrix entry through X/Y coherent
interference, including absolute phase. See the
[first-source record](../../authoring/v022-simple/session.json) and
[validation scope](../../README.md). Upstream frameworks are not executed;
finite numerical checks are not a general algorithm or translation proof.
