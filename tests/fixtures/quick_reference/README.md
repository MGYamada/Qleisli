# Quick-reference executable sources

The four complete original programs were extracted byte-for-byte from the
retired 0.2.7 quick reference during the 0.2.8 docs reduction. Their bytes remain
historical inputs. None of these four sources contains the retired coherent
`do ... pure ...` notation, so this migration needs no new coherent derivative
for them.
Current conformance tests in [qli_corpus.rs](../../qli_corpus.rs) select explicit
migration derivatives through [current-source fixture selection](../../../scripts/current_source_fixtures.py),
with independent expected distributions for phase cancellation, teleportation,
phase kickback and static operation substitution. The test manifest retains
edition 2026; a grammar migration does not change the constitutional edition.

The current coherent spelling is `basis q as p { e }`. The
[normative contract](../../../docs/src/reference/coherent-basis.md) retains the
single quantum owner, restricted basis expression, injectivity, exact phase and
ordered axes. These original files are not accepted aliases for the retired
spelling, and updating a current derivative does not rewrite the original.

The explanatory reference remains in the fixed release source.
