# Realization, specialization and resources

This chapter specifies the 0.3.0 boundary between a program's meaning and a
claimed target implementation. It applies the adopted PR-2026-01 and RS-2026-01
[interpretations](../design/initial-interpretations.md) under the
[authority hierarchy](authority.md). It selects no concrete target schema,
universal gate set, synthesis algorithm or new source syntax. The current
implementation and proof limits are stated below.

The governing decisions are [#120](https://github.com/MGYamada/Qleisli/issues/120),
[#127](https://github.com/MGYamada/Qleisli/issues/127),
[#280](https://github.com/MGYamada/Qleisli/issues/280) and
[#281](https://github.com/MGYamada/Qleisli/issues/281). Their remaining
implementation and evidence obligations are not discharged by this chapter.

## Semantic validity and a target realization

Semantic unitarity states a property of the exact denotation. It does not
promise that the selected target can implement that operator, that synthesis
can find an implementation, or that the source's logical wires suffice.
Target synthesis failure must not reclassify a semantically unitary program
as non-unitary. Inverse and coherent-control access have their own contracts;
neither follows from finding one realization.

Physical Realizability is a **forward correspondence obligation**. For an
accepted closed instance `p`, a checked realization of the actual output
artifact `C` under profile `T` must implement the accepted meaning of `p`,
subject to its explicit interface, encoding and workspace premises. A claim
about a circuit that was considered during search does not cover a different
circuit subsequently emitted or executed.

Synthesis and search produce candidates outside acceptance. An independently
supplied candidate can qualify through the same checks; possession of a
complete synthesis algorithm for the entire semantic domain is unnecessary.
A failure to find a candidate is not evidence of impossibility. An
impossibility claim requires an obstruction whose hypotheses match the target.

Domain-wide existence or synthesis completeness is optional profile
mathematics. For example, Giles and Selinger's Theorem 1 establishes exact
Clifford+T synthesis with at most one clean ancilla for `2^n × 2^n` unitary matrices over
`Z[1/√2, i]`, using their specified gate and phase conventions. That result
neither grants arbitrary dirty workspace nor verifies a particular compiler's
output. See the [original theorem](https://arxiv.org/html/1212.0506v3#S2).

## Closed specialization

A generic definition describes a family. A **closed specialization** fixes
every choice needed to determine its meaning and interface:

- the resolved definition and complete dependency/source identities;
- ordered static arguments, including natural sizes and basis types;
- selected providers, their types, required capabilities and meaning bindings;
- all relevant static constraints and finite evaluation results;
- the declared constitutional edition and applicable semantic profile.

For a target claim, the realization also fixes the target/profile, ordered
layout and encoding, workspace contract and any target-dependent choices.
An unresolved parameter, capability, constraint or budget expression cannot
be treated as a successful concrete certificate. A spelling, bit width or
function name is not a specialization identity. The
[exact type tree](type-model.md#structural-equality-coherence-and-physical-maps) remains part
of that identity, including Unit factors and zero-width owners.

Generic checking must cover the generic body's admitted cases under its
declared premises. A favorable specialization cannot excuse an invalid generic
body or erase an obligation in an unselected branch. Conversely, a well-typed
family need not fit one fixed target at every parameter value.

A family theorem may quantify over all admissible substitutions. Its statement
must retain those premises; it must not describe one fixed finite circuit as
implementing an unbounded family. Static totality, computation of an instance's
resource bounds, and feasibility of those bounds on a target are separate
properties. The static language and specialization implementation remain
tracked in [#28](https://github.com/MGYamada/Qleisli/issues/28),
[#44](https://github.com/MGYamada/Qleisli/issues/44) and
[#47](https://github.com/MGYamada/Qleisli/issues/47).

## Workspace and exact correspondence

Source `clean`/`dirty` workspace is part of the author's program contract and
owner accounting. Backend workspace is additional implementation storage used
to realize that meaning. Backend storage does not become an implicit source
owner or permission to discard a source value. Its initialization, lifetime,
restoration and physical cost must appear in the realization claim.

For a clean-workspace unitary instance, a representative equation is

```text
(C ⊗ I_E)(encode_in ⊗ I_E)(|0>_W ⊗ ψ)
  = (encode_out ⊗ I_E)(|0>_W ⊗ (U ⊗ I_E)ψ)
```

Here `ψ` belongs to `L_in ⊗ E`, and `U` maps `L_in` to `L_out`.
The isometric encodings map `W ⊗ L_in` and `W ⊗ L_out` to the respective
physical interfaces; the reference `E` stays last and is untouched. Thus each
side uses the same explicit workspace/data/reference order. The equality is exact,
including scalar phase. `W` starts and finishes in the specified pure zero
state. A type width, owner name or an example input does not prove this
equation. For other encodings or differing input/output interfaces, the
realization must state its corresponding typed equation explicitly.

Dirty workspace requires the declared identity action on its unknown state
and all reference correlations. Returning its marginal state on a few inputs
is insufficient. Observing implementations require the complete unnormalized,
outcome-indexed instrument correspondence, including declared classical result
assembly; a normalized selected branch or matching measurement probabilities
cannot replace it. The exact clean/dirty requirements come from the adopted
QS interpretation and [#70](https://github.com/MGYamada/Qleisli/issues/70),
[#156](https://github.com/MGYamada/Qleisli/issues/156) and
[#157](https://github.com/MGYamada/Qleisli/issues/157).

Projective equality is different from exact operator equality. Dropping a
global phase can change a coherently controlled operation. The present exact
contract does not quotient by that phase. A different equality relation must
identify its boundary and compositional obligations explicitly; this chapter
introduces no approximate acceptance or error budget. Exact/approximate
profile decisions remain in [#31](https://github.com/MGYamada/Qleisli/issues/31)
and [#123](https://github.com/MGYamada/Qleisli/issues/123).

## Quantitative resource claims

A resource certificate must identify the actual closed instance, emitted
artifact, target/profile, resource measures, schedule or interpretation of
those measures, and checked bounds. Changing providers, layout, target,
workspace or output bytes invalidates reuse unless checked correspondence
establishes the new claim. A content hash establishes identity, not the bound.

Physical live width includes logical data, explicit source workspace,
backend synthesis workspace and routing/target storage. Count actual physical
locations once, accounting for their lifetimes and permitted reuse. Peak
width is the maximum simultaneous live count; a sum of separate peaks is a
conservative upper bound, not necessarily the realized peak. Logical width
alone does not bound the physical implementation width.

Gate count, depth and non-Clifford cost require declared target conventions.
Literal IR T-word counts are not automatically physical or optimal T counts.
Compiler memory, checker work limits, static termination, ownership safety
and target resource bounds are different claims. In particular, the existing
ownership-only predicate does not discharge quantitative RS.

An admitted symbolic family bound may strengthen RS within edition 2026.
It still needs the corresponding current proof and actual compilation/resource
binding. Before certifying a newly admitted family or construct whose resource
behavior lies outside current coverage, its corresponding bound and preservation
obligations must be discharged; existing guarantees remain in force.
Failure to meet a target budget rejects that target claim, without
changing the program's mathematical denotation. QCP implementation and concrete
target schemas retain their separately scheduled scope in
[#103](https://github.com/MGYamada/Qleisli/issues/103); this chapter is not their
implementation. Phase-aware target cost is tracked in
[#165](https://github.com/MGYamada/Qleisli/issues/165).

## Small obstruction examples

Embedding a `k`-qubit gate `G` into `n` wires, under a fixed ordered basis,
gives determinant `det(G)^(2^(n-k))`. Determinants multiply under composition.
Consequently a target generator set restricts same-wire determinants.
This is a necessary obstruction; sufficiency requires a separate theorem for
that precise generator, phase and workspace profile.

The repository retains two exact small examples:

| Operator | Semantic property | Same-wire obstruction for the stated profile |
| --- | --- | --- |
| Positive-exponent three-qubit Fourier operator `F8` | Unitary, with `det(F8) = i` | The embedded H/T/X and NCT generators considered by the regression have determinants only `±1` on three wires. |
| Four-bit `c3x` basis permutation | A bijection with one transposition, hence determinant `−1` | Those embedded generators have determinant `+1` on four wires. |

Both programs remain semantically accepted. The regression
`tests/static_semantics.rs::review_same_wire_obstructions_do_not_reject_semantic_unitaries`
checks the original four-bit table, the complete exact F8 operator and the
embedded-generator determinant calculation. Its retained source is
`tests/fixtures/review_v023/c3x.qli`. These examples do not establish a universal
obstruction for other target vocabularies, arbitrary controlled gates or a
profile that permits additional workspace.

## Current production status and diagnostics

The [production inventory](production-boundary.md) identifies actual native
acceptance, proposal, execution and export routes. Ordinary native acceptance
does not itself issue a target realization or resource certificate. The two
admitted QLV1 guarantees cover original-root ownership and classical scope;
they do not certify source lowering, target emission or quantitative bounds.

The current terminal exporter in `src/interop/export.rs` performs bounded
untrusted rewrites after program verification. It explicitly allocates and
uncomputes conjunction scratch and rejects output exceeding its physical
qubit capacity. The independent `scripts/test_review_v024.py` oracle checks
emitted small QFT/control circuits, including complex phase, output axes and
zero-return scratch. Such bounded numerical validation is distinct from a
general transformation proof or resource certificate. External schema entries
remain disabled until their binding gates are completed.

Diagnostics for a failed realization/resource claim must identify the closed
instance, requested profile and failed premise, and distinguish a proved
obstruction from unsupported synthesis or exhausted checking capacity. An
unsupported target operation or target-width error must not be presented as
failure of semantic unitarity. The current exporter already reports unsupported
operations and the synthesis-workspace capacity limit; a general specialization
certificate, profiler and obstruction diagnostic are not implemented by those
messages. Pending diagnostics and release evidence remain part of
[#48](https://github.com/MGYamada/Qleisli/issues/48),
[#120](https://github.com/MGYamada/Qleisli/issues/120) and
[#127](https://github.com/MGYamada/Qleisli/issues/127).

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
