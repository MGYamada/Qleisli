# Deliberate semantic counterexamples

These twelve local mutations are **expected to compile and verify** under the
language's type/resource rules, then disagree with the independently stated
algorithm contract. They are curated semantic tests, not external translations,
failed first attempts or a fourth input source. Upstream-derived source retains
its original license and attribution; the QuantumKatas variants are MIT.

The [manifest](manifest.json) states each mutation and its reference case.
`check_input_corpus.py` requires successful checking, then a numerical semantic
mismatch. A parse, compiler or harness failure does not count as detection.
The phase-erasure case has the same ordinary outcome probabilities; controlled
X/Y interference must distinguish it. The swapped Bell labels leave the default
00 example unchanged, requiring the complete Bell-label/reference probes.

The six simple 0.2.2 mutations omit SWAP's final CNOT, ignore Fredkin's control,
flip the wrong constant-XOR bit, complement only one bit, erase RX's scalar,
and mark the wrong phase-kickback key. Each names its finite reference contract
in the manifest. Missing RX scalar leaves ordinary Z probabilities unchanged,
so its phase-sensitive detection is required separately from the quickstart.
