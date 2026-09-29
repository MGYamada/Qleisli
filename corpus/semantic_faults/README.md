# Deliberate semantic counterexamples

These six local mutations are **expected to compile and verify** under the
language's type/resource rules, then disagree with the independently stated
algorithm contract. They are curated semantic tests, not external translations,
failed first attempts or a fourth input source. Upstream-derived source retains
its original license and attribution; the Bell and majority variants are MIT.

The [manifest](manifest.json) states each mutation and its reference case.
`check_input_corpus.py` requires successful checking, then a numerical semantic
mismatch. A parse, compiler or harness failure does not count as detection.
The phase-erasure case has the same ordinary outcome probabilities; controlled
X/Y interference must distinguish it. The swapped Bell labels leave the default
00 example unchanged, requiring the complete Bell-label/reference probes.
