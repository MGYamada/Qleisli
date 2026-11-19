# Operations, meanings and capabilities

This chapter is the record of a retired design packet. The packet proposed how
operation descriptions, Meanings and capability requirements would work in the
0.3.0 language, together with the [type foundation](type-foundation.md). It
was a nonnormative candidate for an ordinary implementation decision. It
ratified no text, recorded no Guardian judgment, admitted no guarantee and
changed no adopted interpretation.

The Reference states the rules that the decisions below adopted. A form that
the packet proposed, and that no decision adopted, is not part of the
language. Git history holds the full text of the packet.

## History

### Decisions that followed the packet

| Subject | Decision | Rules |
| --- | --- | --- |
| Capability requirements | [#45](https://github.com/MGYamada/Qleisli/issues/45) selected `Applicable`, `Adjointable` and `Controllable` on 2026-10-08, with `adjoint(U)` as the general constructor. The packet wrote `Apply`, `Adjoint`, `Controlled` and `inverse(U)`. A two-sided inverse API would require its own law. | [Operation repetition and access](../reference/static-language.md#operation-repetition-and-access) |
| Checked operations | [#82](https://github.com/MGYamada/Qleisli/issues/82) selected `checked_op(implementation, Meaning)` for the closed-declaration constructor. The packet wrote `bind`. | [Checked operations](../reference/checked-operations.md) |
| Arrows | The implementation contract of [#83](https://github.com/MGYamada/Qleisli/issues/83#issuecomment-6096747939) selected `Op<A -> B>` on 2026-10-10, with `Op<A>` as the endomorphic abbreviation. The packet wrote `Op<A,B>`. The slot after the comma holds a Meaning refinement. | [General pure operation arrows](../reference/type-model.md#general-pure-operation-arrows) |
| Meaning composition | `compose(First, Second)` and `tensor(Left, Right)` on declared finite Meanings were implemented on 2026-10-10. | [Meaning declarations](../reference/checked-operations.md#bounded-exact-meaning-composition) |
| Reference Meanings | The maintainer [adopted](https://github.com/MGYamada/Qleisli/issues/46#issuecomment-6103631623) `meaning M: A = reference(f);` on 2026-10-11, under a [concrete contract](https://github.com/MGYamada/Qleisli/issues/46#issuecomment-6103615741). | [Reference programs](../reference/checked-operations.md#reference-programs) |

### Scope of general arrows

- On 2026-10-11 the maintainer deferred general operation arrows beyond all of
  v0.3.0 under [#83](https://github.com/MGYamada/Qleisli/issues/83).
- #83 was then resumed for 0.3.0-beta under the
  [release audit](https://github.com/MGYamada/Qleisli/issues/142). The
  resumption supersedes the deferral. The
  [roadmap](https://github.com/MGYamada/Qleisli/blob/main/ROADMAP.md) records
  its scope: separate operation and Meaning ports, ordinary project
  integration and independently checked rectangular pure equations.
- Resumption is not implementation or proof completion. The state of a GitHub
  Issue is not completion evidence.
- The maintainer excluded completion of the QFT implementation from v0.3.0.
  The Reference specifies two fixed Fourier matrices as
  [reference programs](../reference/checked-operations.md#fixed-fourier-specifications).
  It has no `fourier[n]` constructor.

### Proposals that no decision adopted

The packet also proposed the forms below. No recorded decision adopted them,
and the Reference does not specify them.

- The kinds `Meaning<A>` and `Meaning<A,B>`, the declaration form
  `meaning M : Meaning<A> = ...` and the labelled refinement
  `Op<A, meaning M>`. The language declares `meaning M: A = ...` and
  `meaning M: A -> B = ...`, and it refines an operation as `Op<A,M>`.
- The Meaning constructors `identity[A]`, `zero[A]`, `hadamard`, `inverse(M)`,
  `controlled(M)`, `power(M,n)` and `fourier[n]`.
- `InstrumentMeaning<A,B,C>` and `instrument_reference(f)`. Observing contracts
  use the
  [function instrument overload](../reference/type-model.md#direct-runtime-transforms-and-opaque-operations).
- The constructor spellings `then` and `tensor` for operations, and an
  operation `identity[A]`.
  [Admitted operation construction](../reference/functional-boundary.md#admitted-operation-construction)
  lists the constructors of the language.
- A constructed operation expression as the first argument of `checked_op`.
- Named static builders that receive or return operations.
- Certified external providers.
- `controlled(U)` applied to one packed `Q<(Bit,A)>` owner. The language
  writes `controlled(U)(c, q)`.
- The parameter marker `static`. The language writes `const`.

### Retained evidence

No historical source or observation was rewritten. The studies below keep
their first sources, their diagnostics and their failed attempts.

| Study | Content |
| --- | --- |
| [Operator-arrow study](https://github.com/MGYamada/Qleisli/blob/09e21a305c7e6fca1e8d82378756ca35ae5a305b/tests/fixtures/authoring_sessions/operator-arrow-v030/README.md) | The first observation of preparation, unitor and closure sources. It is a historical observation, not a list of limitations. |
| [Arrow-interface study](https://github.com/MGYamada/Qleisli/tree/main/tests/fixtures/authoring_sessions/arrow-interfaces-v030) | Six unchanged first sources, recorded on 2026-10-10 |
| [Composition study](https://github.com/MGYamada/Qleisli/tree/main/tests/fixtures/authoring_sessions/meaning-composition-v030) | The observing and pure-entry adapters for Meaning composition, with their profile refusals |
| [General-arrow study](https://github.com/MGYamada/Qleisli/tree/main/tests/fixtures/authoring_sessions/general-arrows-v030) | Manifest, parser and lowering failures from before the repair, beside the later checks |

The packet named `tests/static_operations.rs`, `tests/meaning_evidence.rs`,
`tests/function_contracts.rs` and `tests/operation_parameters.rs` as the
regressions to migrate.

The packet read [#45](https://github.com/MGYamada/Qleisli/issues/45),
[#46](https://github.com/MGYamada/Qleisli/issues/46),
[#83](https://github.com/MGYamada/Qleisli/issues/83) and
[#89](https://github.com/MGYamada/Qleisli/issues/89) on 2026-10-04, when all
four were open design issues. It was reviewed against source and Issue text
only. It claimed no Rust or Lean execution, proof result, release readiness or
guarantee discharge.
