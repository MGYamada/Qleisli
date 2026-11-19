# Type foundation and common frontend

This chapter is the record of a retired design packet. The packet proposed one
common frontend for both lowering profiles and the minimum explicit type
surface of the 0.3.0 language. It was a nonnormative design analysis. It
implemented no feature, issued no Guardian ruling and discharged no guarantee.

The Reference states the rules that were selected.
[Ordinary types, quantum owners and equality](../reference/type-model.md)
holds the type rules, and
[Operations, meanings and capabilities](operations.md) records the decisions
on operations. A form that the packet proposed, and that no decision adopted,
is not part of the language. Git history holds the full text of the packet.

## History

### The approved implementation order

The approved order was one source syntax tree, one module and name resolver,
and one static elaboration with type and ownership checking, followed by
separate finite and hierarchy lowerings. The release performs one 0.3.0 source
cutover with a migration mapping, and it supports no second source dialect.
The edition stays 2026: it identifies the constitutional regime, and release
compatibility carries the syntax change.

Both lowering profiles use the mandatory common original-source judgment, as
the [type model](../reference/type-model.md) states. The changelog records the
removal of the separate `frontend::sized` module and of the `sized` command
namespace.

### Decision basis

| Issues | Role in the packet |
| --- | --- |
| [#22](https://github.com/MGYamada/Qleisli/issues/22), [#27](https://github.com/MGYamada/Qleisli/issues/27), [#43](https://github.com/MGYamada/Qleisli/issues/43) | The adopted direction: ordinary finite types are unmarked, `Q<T>` is linear ownership, there is no `C<T>` universe, and `Q<Unit>` retains its owner and its scalar phase. |
| [#84](https://github.com/MGYamada/Qleisli/issues/84), [#100](https://github.com/MGYamada/Qleisli/issues/100) | The recorded boundary: definitional equality, canonical coherence and physical maps are distinct. Only unique static structure is inferred, never quantum meaning. |
| [#44](https://github.com/MGYamada/Qleisli/issues/44), [#45](https://github.com/MGYamada/Qleisli/issues/45), [#46](https://github.com/MGYamada/Qleisli/issues/46), [#83](https://github.com/MGYamada/Qleisli/issues/83), [#89](https://github.com/MGYamada/Qleisli/issues/89) | Basis kinds, operator interfaces, Meaning and capability judgments, and callable categories. [Operations, meanings and capabilities](operations.md) records their decisions. |
| [#32](https://github.com/MGYamada/Qleisli/issues/32), [#33](https://github.com/MGYamada/Qleisli/issues/33), [#35](https://github.com/MGYamada/Qleisli/issues/35), [#37](https://github.com/MGYamada/Qleisli/issues/37), [#196](https://github.com/MGYamada/Qleisli/issues/196) | Surface normalization. An example in an Issue adopts no grammar by itself. |
| [#197](https://github.com/MGYamada/Qleisli/issues/197) | Later convenience work for 0.4.0: automatic coherence, richer patterns, omitted static arguments and a general policy for reuse across stages. |
| [#63](https://github.com/MGYamada/Qleisli/issues/63) | Bounded constant and static computation. The maintainer excluded it from all of v0.3.0, and the Issue is closed as not planned. |

### Selected rules

The target type contract selected the rules below as ordinary implementation
choices under the approved plan. It records no human Guardian ruling.

| Subject | The packet wrote | The language |
| --- | --- | --- |
| Ordinary finite types | `CBit`, `CBits<n>` | `Bit`, `Bits<n>`, with no `C<T>` universe |
| Bit literals | `0`/`1` for basis values and `true`/`false` for ordinary values | `0` and `1` for both |
| Tree identity | `Bit` and `Bits<1>`, `Unit` and `Bits<0>`, and each tuple arity and nesting, kept distinct | The same. No implicit coherence or physical conversion is inserted. |
| Total finite functions | `basis fn` | `classical fn` |
| Boolean operators | `!`, `&`, `^` | `not`, `and`, `xor` |
| Static parameters | The marker `static` | The marker `const`, with explicit positional arguments |
| Operator interface | `Op<A,B>` | `Op<A -> B>`, with `Op<A>` for `Op<A -> A>` |
| Capability requirements | `Apply`, `Adjoint`, `Controlled`, `inverse(U)` | `Applicable`, `Adjointable`, `Controllable`, `adjoint(U)` |

### Recommendations without a recorded decision

The packet recommended a mandatory final expression for a quantum block, an
explicit `()` for an ordinary Unit result, and no `return` in quantum core
source. It set this against [#196](https://github.com/MGYamada/Qleisli/issues/196)
and [#37](https://github.com/MGYamada/Qleisli/issues/37). This record names no
decision on those recommendations.
[One structured quantum result boundary](../reference/source-text.md#one-structured-quantum-result-boundary)
states the rules of the language.

### Preserved authoring experiment

The informed session at
`tests/fixtures/authoring_sessions/type-foundation-v030/session.json` preserves
complete first sources, source hashes, command arguments and JSON diagnostics.
It is an informed design study. It is neither a blind model benchmark nor an
adoption of its generic syntax. The recorded tool version is `0.3.0-alpha`,
and all four observations used `qleisli check --format=json` with an explicit
local native checker path.

| Preserved source and observation | Recorded result |
| --- | --- |
| `attempt-01/ordinary-bit`, `ordinary-bit-initial.json` | Exit 1, `type_mismatch`: `Bit is a basis type; ordinary functions use CBit or Q<basis type>` |
| `attempt-01/generic`, `generic-initial.json` | Exit 1, `parse`: ``parse error: expected `Op`, found identifier`` at the proposed `Basis` parameter |
| `attempt-01/unit`, `unit-initial.json` | Exit 1, `invalid_entry`: `main must be observe fn main() with a classical result` |
| `attempt-02/unit`, `unit-entry-repair.json` | Only the entry effect changes from `unitary` to `observe`; exit 0, `verified: true` |

The original failures stay preserved, and the repair is a separate attempt.
The successful Unit check exercises no controlled scalar phase. It proves no
source preservation and establishes no generic typing.

### Constitutional impact recorded by the packet

| Obligation | Recorded impact |
| --- | --- |
| QS | Shared judgments must preserve linear owners, exact trees, ordered axes, phase, classical scope, effects and independently requested meanings. A lowering correspondence cannot be inferred from the validity of its output. The scoped QLV1 guarantees keep their exact predicate and artifact boundary. |
| PR | A common source frontend grants no target realization and no correctness of an exported artifact. Target synthesis and its workspace are separate. |
| RS | The parser, type and specialization work and storage are bounded before construction. These engineering limits are not the quantitative Resource Safety theorem. |

The packet implemented no constitutional interpretation. An ordinary design
choice within the adopted QS, PR and RS obligations is a maintainer decision.
A claim of formal discharge, or a change to the interpreted boundary, needs
the established human adequacy and admission process.

### Proof components for access work

The packet also recorded two Lean proof components for the access work of
[#303](https://github.com/MGYamada/Qleisli/issues/303).
[Surface-to-core elaboration](../reference/elaboration.md#status-and-limits)
states them under its proofs.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
