# Tuple shape and type-contract correction

This is an informed development regression, not a controlled authoring benchmark.
The user selected arity-preserving tuples for unreleased 0.2.0 on 2026-09-29.
The [type contract](../../../docs/type-system.md) defines formation, equality,
ownership and conversions; the [migration](../../../docs/type-system.md)
supersedes the earlier left-folding rule.

## Preserved first source and independent criterion

[`first_source/main.qli`](first_source/main.qli) was saved before changing the
compiler. The actual [baseline](baseline.json) records successful checking even
though its declared nested result and flat body have different intended shapes.
That was the documented 0.1.8 rule, not a claim of an old quantum-soundness hole.
The same source must now reject with `type_mismatch`, distinguishing
`((Bit,Bit),Bit)` from `(Bit,Bit,Bit)` in its diagnostic.

[`explicit_layout.qli`](explicit_layout.qli) spells the two conversions as
ordinary total basis definitions and quantum lifts. Its round trip is checked
against identity on the full three-bit register, then independently observed
with an entangled reference: the expected ordered output is `0010` with unit
probability (up to reference simulator rounding). This tests axis order and
reference correlations, not merely whether a signature parses.

[`wrong_permutation.qli`](wrong_permutation.qli) has the same valid types and
ownership but reverses the first and last bits. It must fail exact identity
evidence. [After-state observations](after.json) retain real CLI invocations,
diagnostics, output and source/compiler hashes. Temporary project paths are
recorded verbatim; the source files remain here.

## Cost and migration observations

- The correction removes the need to remember an implicit association when
  deciding whether interfaces are equal. It deliberately requires explicit
  conversion when those interfaces have different shapes.
- The positive fixture has two basis conversions and two quantum wrappers;
  the fixed binary standard APIs need no new definitions or changed contracts.
- Three of 24 external-corpus kernels needed explicit former binary trees.
  [Attempt 04](../../../corpus/authoring/session.json) preserves this migration
  without rewriting earlier attempts. All 9,412 independent semantic probes
  passed afterward. No external source or license was added.
- No generation/verification timing comparison was measured for this change.
  Existing finite width/work limits remain; arity (64 fields) and actual nesting
  have separate bounds. No dense-matrix scaling or general proof claim follows.

CI runs [tuple shape tests](../../tuple_shapes.rs), including mixed and
zero-width ownership, pending branch frames, exact meanings, source capacities,
and iterative rejection/drop of deep untrusted type trees. The
[interchange suite](../../interchange.rs) also rejects altered external type
requests and noncanonical tuple arities in separate verifier processes.
