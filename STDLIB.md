# Standard-library contribution conventions

Status: **initial contribution discipline adopted on 2026-09-30; conventions
will be refined through corpus examples**. The user selects a mathlib-style
open-source library effort from v0.5.0: shared mathematical conventions,
readable implementations, explicit proof coverage and continuing review.
This concerns contribution discipline, not a dependency on Mathlib in the
runtime or a claim of existing community maintainers.

The maintainer has excluded QFT implementation completion from v0.3.0 and
the current development goal. Generic QFT exposure and fixed/generic QFT
equivalence are outside that scope, with no future target selected. The semantic
namespace migration in [#317](https://github.com/MGYamada/Qleisli/issues/317)
continues; existing fixed-QFT implementations retain their contracts and
regression evidence. Historical family studies are not current release gates.

Until v0.5.0, do not expand `stdlib` as a general rule; add algorithms to
`corpus` under its [existing intake policy](corpus/POLICY.md). Prepare the
conventions, reference contracts and checking tools now. Existing library
maintenance and documentation retain their compatibility obligations. From
v0.5.0, library growth follows reviewed adoption rather than automatic promotion
of everything in the corpus. Adoption requires explicit source contracts and independent review.

## Shared decisions before individual implementations

**The standard library is a qrate now, named `std`**, declared by
[stdlib/Qargo.toml](stdlib/Qargo.toml) using qargo schema 2, Qleisli edition
`"2026"` and the compiler's release version. Its `src`, `tests` and `docs` roots
exist; see the [qrate guide](stdlib/docs/README.md). `stdlib/` is the directory
name; `std` is the qrate name and public `std::` namespace. Other source trees
currently declare only their edition and will all migrate to qrate management
in the future. Library adoption and semantic/proof gates remain in force.

The purpose is to reduce decisions each author must make again. Fix a component
family's independently requested mathematical meaning and conventions before
comparing implementations. A proof of implementation conformance does not show
that the chosen specification is the intended one; review that choice separately.

| Initial rule | Contribution obligation |
| --- | --- |
| **SC-01: contract first** | Record a source contract before proposing standard adoption. State the whole-input operator or complete instrument, exact type tree, owner transitions, encodings and premises. Give totality/domain rules for basis functions. A name such as "QFT" is not a contract. |
| **SC-02: preserve canonical conventions** | Reuse the existing family's sign, scalar phase, integer/axis encoding and output convention. Current QFT2/3 use positive Fourier phase, first leaf least significant and included reversal; current addition is unsigned modular addition with amplitude +1. Future sized APIs still require specification and adoption. |
| **SC-03: distinguish changed meaning** | An optimization under the same contract must preserve its phase, ordering, effects, error and cleanup promises. An inverse, omitted reversal or approximate variant needs an explicitly distinguished contract and reviewed name/parameter. Do not introduce a hidden implementation-dependent switch. |
| **SC-04: report intermediate permissions** | Use current consume/return ownership APIs. Specify preserved basis labels and whole-state/reference behavior separately. Final restoration does not by itself authorize intermediate writes or borrowing. |
| **SC-05: evidence with scope** | Show source checking, semantic tests, actual-IR conformance proof, source preservation and specification review separately. State widths, input/entry premises, tolerance or exact domain, actual definitions and remaining assumptions. Do not use a single unqualified `verified` badge. |
| **SC-06: readable and interchangeable** | Connect concept, derivation, source, examples and proof status. Compare optimized implementations to the fixed contract, not only to each other. Keep resource accounts implementation-specific under an explicit model. |

For new `.qli` names use the existing `snake_case` convention. Preserve public
names and signatures. Write parameter roles in contract order: controls or
preserved inputs, destination/work data, then explicit scratch if exposed;
returned owners keep the documented correspondence. This is a drafting default
for future APIs, not permission to reorder existing parameters, flatten products
or adopt `&`/`&mut` syntax. Final generalized signatures and exception rules
remain subject to the type-system and API design process.

For phase oracles the pilot uses `O_f|x> = (-1)^f(x)|x>`, negating marked
labels. State the Boolean predicate, domain and phase convention explicitly.
Reflections such as `2|psi><psi| - I` have a different fixed sign; they must not
be silently identified with their negatives under coherent control.

## What contracts must make composable

Specify mathematical basis coordinates, source tuple leaves and actual output
axes separately from printed bit strings. `q[0]` in a mathematical discussion
does not adopt register-index syntax. An integer equality does not erase type
trees, reorder wires or permit implicit conversion. For controlled composition,
operator equality includes global phase; channel equality alone is insufficient.

A whole-basis equation with complex amplitudes and the same output/scratch
space extends by linearity and tensoring with reference identity. For an
encoded-input equation, the guarantee covers the explicitly promised encoded
subspace; prove entry validity separately. Neither statement establishes source
lowering correctness without its own correspondence evidence.

Scratch contracts state initial state, ownership and exact final state and
separation. Pure cleanup needs its checked factorization for every permitted
input and reference. Approximation of the data operation never excuses dirty
scratch. Observing procedures list every outcome, residual state and explicit
discard; a success branch alone is not a complete instrument.

Resource accounts state units, model, scope and evidence: live data and scratch,
gate counts, depth, measurements and any host/search work claimed. Distinguish
logical operations, routed physical gates, representation sharing and repeated
execution. An unknown cost is recorded as pending with a reason. Current
structural counts are not the future quantitative Resource Safety Theorem.

## Ownership and future borrowing

The language determines aliasing, permission and lifetime rules; library style
cannot introduce or weaken them. General quantum `&`/`&mut` borrowing is not a
current API. Revisit library argument conventions after the v0.3.0 type-system
specification decides any such feature, with acceptance/rejection and lowering
rules before using it in standard source.

If a future read-only borrow permits basis-label-preserving controls, document
that meaning without claiming preservation of the owner's reduced density
operator. For example, CNOT takes `|+>_c|0>_t` to a Bell state: the control label
is unchanged on each basis input, but its reduced state changes. An adder that
temporarily changes a preserved input and restores it may need a different
permission from an implementation that never changes that label. A final
equation or an API style rule alone cannot select those permissions.

## Template and reference implementations

Use the source's English documentation for the meaning, interface/encoding,
premises/access, ancillas/effects, approximation, resources and evidence scope.
Keep teaching examples beside executable source. `None` is meaningful for scratch
or approximation; `pending` names the missing obligation and its scope.

| Source | Fixed contract | Review focus |
| --- | --- | --- |
| [QFT2](stdlib/src/transforms.qli) | Positive F4, exact phase and included reversal | Uniform probabilities and inverse round trips do not determine sign or order. |
| [Add2](stdlib/src/arithmetic.qli) | Preserved addend; destination overwritten modulo four | Basis outputs cannot detect extra phase or invented zero-input promises. |
| [AND phase](corpus/qualtran/and_phase/kernel.qli) | (-1)^(a and b), with explicit cleanup | Marking polarity, clean return, phase and attribution; this remains outside std. |

These existing implementations do not establish general-size or source-preservation
proofs. The retired template and pilot prose are no longer required CI inputs.

## Checking responsibilities

| Mechanism | Responsibility and limit |
| --- | --- |
| Type/IR/evidence checker | Enforce the specified ownership, effects, access, semantics and cleanup rules. Borrowing is enforced only if a language extension implements it. No style waiver bypasses rejection. |
| Documentation checks; `qlippy` planned | Check active links, agent instructions and metadata. Future source-aware advice follows adopted syntax; presence checks do not establish equation truth. |
| Semantic tests | Compare small full complex columns or a complete instrument against an independent formula; use coherent/control probes for scalar phase, references, order and scratch. Retain deliberate type-correct faults. An inverse round trip is supplementary. |
| Semantic proofs | State premises and prove conformance for the actual checking/execution definitions and declared range. Abstract-model theorems, actual IR binding and source preservation remain distinguishable. |
| Human review | Review intended meaning, family conventions, integration, explanation, licensing and usability; assess proof coverage and blocking findings independently of implementation tests. |

The prose-only template/pilot linter is retired with those documents. Existing
corpus/semantic CI and Lean proof audits retain their independent responsibilities.
Run `python3 scripts/check_docs.py` for active documentation and metadata checks.
`qlippy` remains planned, not an implemented executable or acceptance authority.

## Review and rollout from v0.5.0

Before v0.5.0, refine source contracts through corpus authoring and review.
During 0.4.x, prepare contributor setup, issue/review procedures and source-aware
linting proposals alongside the existing community plan. At v0.5.0, begin
reviewed library growth as a mathlib-style open-source effort after its own
theorem/release gates. Contributor and reviewer identities are not appointed
by this document.

A contribution should connect its corpus motivation and at least two reuse
contexts to the contract, reference code, independent positive/fault checks,
status table, ledger entry and compatibility review. Include a use not involved
in extracting the abstraction. Review specification intent and implementation/
proof correspondence as distinct responsibilities, with independent review
recorded where available and blockers resolved before adoption. Keep `pending`
visible; do not claim a generalized theorem for a bounded tested API.

For future sized QFT/QPE adoption, implement the public algorithm in ordinary
`.qli`, check it through the shared verification path, and let callers reuse
its bound contract evidence. Exercise equivalent commuting schedules and calls
under unrelated function names. Compiler recognizers remain untrusted proposal
optimizations; library adoption requires reusable contracts and independent
checking of the actual implementation.

Semantics-changing conventions require an explicit versioned migration.
Refining an explanation does not renumber a historical contract or rerun its
validation. Library admission does not close S05, Physical Realizability,
Resource Safety or V1 algorithm gates, or confer trust on an evidence producer.

## References for the design discussion

The user linked the versioned [Qiskit 2.1 QFT documentation](https://quantum.cloud.ibm.com/docs/en/api/qiskit/2.1/qiskit.circuit.library.QFT),
which exposes inverse, final-swap and approximation choices. Those choices
illustrate why a composable contract must select a meaning. This is a historical
API example, not a Qleisli dependency or a recommendation to use that deprecated
class.

[Mathlib's style-linter documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linter/Style.html)
describes checks for library coding conventions and separates them from
correctness. Qleisli adopts that separation of responsibilities; it does not
copy Mathlib's Lean naming rules into `.qli` or import the linter into the
Mathlib-free runtime.
