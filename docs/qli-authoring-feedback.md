# Feedback from writing QLI programs

**2026-09-28; observed in the 0.1.8 development tree.** The user requested
source/examples/tests first, with language requirements discovered from actually
writing algorithms. The [protocols](../examples/protocols/README.md),
[operation algorithms](../examples/operation_algorithms/README.md) and
[source fixtures](../tests/fixtures/qli_authoring/README.md) are the deliverable.
This report records observations and candidates; it adopts no new syntax.

The user also supplied Claude's account of a successful first-attempt
teleportation and Ubuntu build. Those are external reports, not locally
reproduced timing, first-attempt or Linux results. We reproduced the supplied
body's four-branch distribution, with explicit imports, on macOS. The new
programs were authored and revised in this session: there is no controlled
comparison of models or estimate of general LLM success rate.

## What writing and running code established

Linear rebinding and ordinary `if` express feed-forward directly. Bell preparation,
measurement and corrections can be reused for teleportation, dense coding and
swapping. Static operation arguments reuse one QPE body across T powers and X,
and one amplification body across four marked predicates. These are concrete
reductions in duplicated algorithm bodies, within one exact interface type.

Type-correct faults show why authoring success must include semantic tests.
Omitting teleportation's Z correction still passes the zero-input test but
fails for minus on half the message branches. Swapping the correction bits
also fails on half the minus-state branches. Forward QFT returns phase 7/8
instead of 1/8. Reference-sensitive tests and signed T/T† overlap tests exercise
more than a plausible-looking final bit string. They remain finite regressions.

## Reproduced friction and next candidates

Fixture paths below are relative to
[the corpus](../tests/fixtures/qli_authoring/README.md). Priorities are a proposed
implementation order, not adopted source/API changes.

| Priority / issue | Reproduction and current workaround | Obligation to remove; checking boundary |
| --- | --- | --- |
| 1: product-valued basis functions cannot inspect components | `rejected/meaning_pair_predicate.qli` gives `type_mismatch`: `phase_by` needs one argument of the exact pair type, while the useful predicate has two arguments. `basis_tuple_pattern.qli` gives `parse`; there are no basis projections. `accepted/pair_contract.qli` checks the same phase against an independently written circuit using `apply_contract`. | Let authors state nonconstant pair targets directly. Specify basis parameter patterns or projections with totality/types and basis-table correspondence; no new semantic acceptance axiom is needed. |
| 1: tuple arity and association leak into composition | `tuple_arity.qli` gives `parse` at the third comma. `product_association.qli` gives `type_mismatch` calling qft3 on a right-associated tree. `accepted/product_reassociation.qli` spells out the split/join adapter. | N-ary sugar can remove punctuation bookkeeping; choose one exact association and preserve leaf/axis order, Unit factors, pattern ownership and spans. It does not by itself equate all existing product trees. Test meaning preservation and migrations; the cost is not zero. |
| 1: dropped-owner location is too broad | `dropped_owner.qli` names `b` correctly but points to line 3, column 27 (the body opening), rather than its line-4 binding. | Retain binding provenance for an actionable primary/related location. Keep rejection; change no ownership rule. The test deliberately does not freeze the poor location. |
| 2: gate providers need wrappers | `sealed_provider.qli` rejects `[h]`, although `adjoint(h,q)` is supported. [states](../examples/protocols/states.qli) and [gates](../examples/operation_algorithms/gates.qli) add closed ordinary wrappers. | Consider uniform static access to eligible sealed operations through the existing elaboration/checking path. Preserve exact signatures, effects and capability distinctions; never infer access merely from unitarity. |
| 2: type/size abstraction is missing | `basis_type_parameter.qli` and `static_nat.qli` give `parse`. `phase2`/`phase3` and `amplify_once`/`amplify_twice` retain duplication. The four-bit [order-finding QPE](../examples/order_finding/estimation.qli) cannot call the Bit-target client. | Separate finite template authoring from scalable family checking; see the decision question below. M1 alone does not satisfy shared Shor/QPE. |
| 2: anonymous classical result roles are easy to exchange | Both correction-order faults compile: phase and parity are both `CBit`. Comments and descriptive bindings are the current aid. | Consider named result structure or clearer generated signature docs; preserve full message/reference-sensitive tests even if records are introduced. |
| 2: cleanup evidence is hard to discover | `rejected/auxiliary_hh.qli` gives `unsupported`, although H H is identity. `accepted/auxiliary_hh.qli` succeeds with the explicit three-argument logical identity contract. | Explain the two forms and suggest the evidence-bearing form. Do not widen the two-argument body's certificate by assertion. |

The `spent_owner`, `aliased_owner`, `missing_adjoint` and
`controlled_is_not_apply` fixtures are useful guardrails, not rules to weaken.
`missing_import` is resolved by complete copyable examples. During this session,
the separate-value spelling `--format json` failed; the supported flag is
`--format=json`. A draft prose reference also incorrectly mentioned `channel fn`;
the AST has only basis/unitary/iso/observe function kinds, and the reference now
uses the implemented `observe`. Checking code fences cannot validate all prose.

## Finite templates and the R14 ordering question

Claude's suggestion identifies a real distinction: an untrusted template could
expand only concrete, bounded instances and submit each to the existing checker,
without claiming a theorem over the family. This is a plausible authoring
experiment. Checked instances and a family theorem are different evidence tiers.
The hierarchical profile's checked-instantiation semantics does not, by itself,
supply source substitution, type arithmetic, termination/budgets, diagnostics,
dependency identity or evidence binding for such templates.

The current [R14 prerequisite](imaginary-v1/requirements.md#scaling-prerequisite-for-r14)
and [roadmap](v0x-roadmap.md) explicitly put evidence-bound hierarchy and
non-dense composition before size generalization. Moving a bounded template
slice earlier would revise that policy; this corpus does not silently do so.
A concrete follow-up decision should compare a finite-only template profile
against that gate, name its unchanged bounds, check every instantiated body
and reject unsupported sizes. Generic definition-time access checking and
instantiation-only checking must have distinct documented guarantees.

Nor is scalable QPE merely the same source with a larger bound: four phase bits
already need π/8, outside the current exact gate profile, and general arithmetic
needs synthesis rather than whole-space tables. Keep those failures explicit.

## A shorter authoring entry point

The [single-page reference](qli-quick-reference.md) separates implemented syntax
from proposals and links to complete projects. Every `qli` fence there compiles
and runs in the existing Rust CI suite. The lightweight Python document checker
continues to check links/status without requiring a compiler. Norms remain in
their authoritative documents; adding this entry point does not duplicate them.
For a future LLM benchmark, record prompt/context, model/version, first source,
diagnostics, repair attempts and semantic results separately; this exercise is
not that benchmark.

The version-policy suggestion is valid as an alternative convention:
[Cargo's compatibility guide](https://doc.rust-lang.org/cargo/reference/semver.html#change-categories)
treats 0.y.z's z as a compatible minor step. Qleisli currently deliberately uses
the stricter [project policy](versioning.md). Adopting Cargo's convention would
reduce exceptions for compatible additions, but not erase the reserved-name and
public AST breaks already recorded in 0.1.8. This source-corpus task retains
0.1.8 and historical records; a policy revision is a separate decision.
