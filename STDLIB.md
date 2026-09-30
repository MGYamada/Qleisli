# Standard-library contribution conventions

Status: **initial contribution discipline adopted on 2026-09-30; conventions
will be refined through corpus examples**. The user selects a mathlib-style
open-source library effort from v0.5.0: shared mathematical conventions,
readable implementations, explicit proof coverage and continuing review.
This concerns contribution discipline, not a dependency on Mathlib in the
runtime or a claim of existing community maintainers.

Until v0.5.0, do not expand `stdlib` as a general rule; add algorithms to
`corpus` under its [existing intake policy](corpus/POLICY.md). Prepare the
conventions, reference contracts and checking tools now. Existing library
maintenance and documentation retain their compatibility obligations. From
v0.5.0, library growth follows reviewed adoption rather than automatic promotion
of everything in the corpus. The [library goal](docs/stdlib-roadmap.md#adopted-library-goal)
and [adoption criteria](docs/stdlib-roadmap.md#5-標準への採用とaiからの還流) remain in force.

## Shared decisions before individual implementations

The purpose is to reduce decisions each author must make again. Fix a component
family's independently requested mathematical meaning and conventions before
comparing implementations. A proof of implementation conformance does not show
that the chosen specification is the intended one; review that choice separately.

| Initial rule | Contribution obligation |
| --- | --- |
| **SC-01: contract first** | Complete the [short template](docs/stdlib-contract-template.md) before proposing standard adoption. State the whole-input operator or complete instrument, exact type tree, owner transitions, encodings and premises. Give totality/domain rules for basis functions. A name such as "QFT" is not a contract. |
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

The template has eight short sections. Use the source's English documentation
for a concise summary and link the full contract/derivation where needed.
`None` is a meaningful answer for scratch or approximation; `pending` must name
the missing obligation and scope. The template is descriptive documentation,
not a new machine evidence schema or a replacement for ledger format v1.

| Pilot | Current source and fixed contract | What it teaches |
| --- | --- | --- |
| [QFT2](docs/stdlib-contract-examples/qft2.md) | Existing `std::transforms::qft2`, positive `F4`, exact phase and included output reversal | Uniform Z probabilities and an adjoint round trip do not select Fourier sign or output order. |
| [Add2](docs/stdlib-contract-examples/add2.md) | Existing `std::arithmetic::add2`, preserved addend and destination overwritten modulo four | Basis outputs alone do not detect extra phase; no input zero promise may be invented. |
| [AND phase oracle](docs/stdlib-contract-examples/and-phase.md) | Existing corpus `kernel`, `(-1)^(a and b)` with exact structured scratch cleanup | Marking polarity, clean return, full phase and source-specific attribution must be explicit. This remains outside `std`. |

These are completed contract-writing pilots over existing code, not three new
library APIs or general-size proofs. The linked source is the reference code;
avoid an independently maintained copy in the guide. Their existing validation
records remain historical evidence. No pilot gains a proof merely by fitting
the template.

## Checking responsibilities

| Mechanism | Responsibility and limit |
| --- | --- |
| Type/IR/evidence checker | Enforce the specified ownership, effects, access, semantics and cleanup rules. Borrowing is enforced only if a language extension implements it. No style waiver bypasses rejection. |
| Contract-document linter now; `qlippy` later | Enforce mandatory sections, structured status dimensions and source/evidence links. Future source-aware naming/argument-role advice follows adopted syntax. Presence checks do not establish equation truth. |
| Semantic tests | Compare small full complex columns or a complete instrument against an independent formula; use coherent/control probes for scalar phase, references, order and scratch. Retain deliberate type-correct faults. An inverse round trip is supplementary. |
| Semantic proofs | State premises and prove conformance for the actual checking/execution definitions and declared range. Abstract-model theorems, actual IR binding and source preservation remain distinguishable. |
| Human review | Review intended meaning, family conventions, integration, explanation, licensing and usability; assess proof coverage and blocking findings independently of implementation tests. |

The initial [contract-document checker](scripts/check_stdlib_contract_docs.py)
runs in CI with its mutation regressions. It checks this template and all pilot
contracts, their mandatory sections, status table structure and local links.
It checks that each pilot links to an existing `.qli` source; it does not parse
that source or certify its signature/meaning, re-run cited results, validate a
Lean theorem or lint all twelve bundled definitions. Existing corpus/semantic
CI and proof audits retain those separate responsibilities.

```sh
python3 scripts/check_stdlib_contract_docs.py
python3 scripts/test_check_stdlib_contract_docs.py
python3 scripts/check_docs.py
```

`qlippy` is a planned role/name, not an implemented executable, reserved package
or acceptance authority. Reuse this small checker as a first contribution; do
not build a second language checker to enforce prose conventions. Move naming
and argument-role checks into syntax-aware tooling once the language/API rules
are settled. Review lint exceptions with a reason; they cannot waive semantics.

## Review and rollout from v0.5.0

Before v0.5.0, refine the template through corpus authoring and these pilots.
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
