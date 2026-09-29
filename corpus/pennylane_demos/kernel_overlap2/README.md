# Kernel Overlap2

Source: [kernel](https://github.com/PennyLaneAI/demos/blob/3a04df83a16af3a2f0fd9398c0b5cc2c060ebedd/demonstrations_v2/tutorial_kernel_based_training/demo.py).
The [frozen original](../../upstream/pennylane_demos/demonstrations_v2__tutorial_kernel_based_training__demo.py) retains its source notices.
License: **Apache-2.0**; [intake policy](../../POLICY.md).

## Contract and translation scope

Apply S(x2)^dagger S(x1), S(x)=RX(x[0]) tensor RX(x[1]), for x1=(pi,pi/2), x2=(pi/2,0). The net operator is RX(pi/2) on each wire with exact scalar phase. On |00>, probability 00 and the kernel overlap equal 1/4.

Specializes default RX AngleEmbedding to two features and exact quarter-turns. The host reads the all-zero probability instead of an imported Hermitian observable. No dataset, SVM, PyTorch, optimization, gradients or continuous-angle API is included.

Classification: ordinary `.qli` definitions, with public signature `Q<(Bit, Bit)> -> Q<(Bit, Bit)>`, `Unitary`.
All inputs are consumed, and every unmeasured owner is returned exactly once.
Integer bits use first-leaf weight 1; output strings list leaves left to right.
No implicit tuple conversion is used. These are case-local APIs, not new
standard-library APIs or language forms. Existing gates, split/join, static
transforms and measurement lower through the unchanged independent IR verifier.
Wrong types, duplicate owners and pure uses of observation are rejected by the
existing checker. Type-correct wrong algorithms need the independent semantic tests.

```sh
cargo run --bin qleisli -- run corpus/pennylane_demos/kernel_overlap2
python3 scripts/check_input_corpus.py target/debug/qleisli --case pennylane_demos/kernel_overlap2 --exhaustive
```

Full complex-entry tests retain absolute phase for the unitary cases; Bell
measurement has branch/reference tomography. See the [validation scope](../../README.md)
and [first-source record](../../authoring/v021-expansion/session.json).
No upstream framework is executed and finite numerical agreement is not a proof.

The upstream [AngleEmbedding contract](https://docs.pennylane.ai/en/stable/code/api/pennylane.AngleEmbedding.html) defaults to RX; its implementation is not copied into this corpus.
