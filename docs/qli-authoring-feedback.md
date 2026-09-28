# Feedback from writing QLI programs

**2026-09-28; observed in the 0.1.8 development tree.** The user requested
source/examples/tests first, with language requirements discovered from actually
writing algorithms. The [protocols](../examples/protocols/README.md),
[operation algorithms](../examples/operation_algorithms/README.md) and
[source fixtures](../tests/fixtures/qli_authoring/README.md) are the deliverable.
The initial observations below led to the user-selected 0.1.8 fixes; the
[grammar](syntax-v0.md#authoring-forms-added-in-product-018) specifies the
delivered forms. Unresolved candidates now live in the
[v0.2.0 backlog](v0.2.0-backlog.md), with stable IDs and acceptance experiments;
this report retains the observations and reasoning that motivated them.

The user also supplied Claude's account of a successful first-attempt
teleportation and Ubuntu build. Those are external reports, not locally
reproduced timing, first-attempt or Linux results. We reproduced the supplied
body's four-branch distribution, with explicit imports, on macOS. The new
programs were authored and revised in this session: there is no controlled
comparison of models or estimate of general LLM success rate.

## Review follow-up, 0.1.9

The supplied 0.1.8 review exposed a parser panic on truncated static arguments
such as `unitary fn f(q: Q<Bit>) -> Q<Bit> { g[`. This is especially relevant to
incomplete generated source. The [parser regressions](../tests/parser.rs) now
exercise every token-boundary prefix of static constructors, executable examples
and bundled library files; [CLI tests](../tests/cli_json.rs) preserve the single
JSON parse diagnostic at EOF. This is robustness validation, not a new measured
authoring session or a model benchmark.

[A020-09 and A020-10](v0.2.0-backlog.md) retain two open design/implementation
issues: constructor-derived access beyond direct header constraints, and source
snapshot copies consuming the reuse budget. The [0.1.9 record](releases/v0.1.9.md)
separates compatible repairs and clarifications from future breaking changes.

Claude's additional supplied feedback reports ten diagnostic probes and about
13 seconds for 35,786 mutated-project checks in a release build. These are
external observations, not a reproduced timing benchmark. It praises precise
ownership/type diagnostics and JSON, while identifying coarse effect locations,
missing rewrite hints, single-error reporting, repeated imports/adapters and
noisy numerical output. The local [repair regressions](../tests/repair_diagnostics.rs)
reproduce the effect/import/provider cases and check their improved locations
and working rewrites. Effect provenance covers primitive and imported calls,
both classical arms, conditions, coherent lifts and stronger declared effects.
Snapshot-limit messages now expose retained sources. A020-11–13 retain multi-error
collection, boilerplate and optional numerical presentation as open candidates.
This is regression work informed by feedback, not a new controlled repair study.

## Three-source translation exercise, 0.1.9

The [input corpus](../corpus/README.md) adds 24 executable finite translations,
eight each from QuantumKatas, Qualtran and PennyLane Demos, under the
[adopted source/license policy](../corpus/POLICY.md). The
[session](../corpus/authoring/session.json) records prior repository and upstream
access, untouched first sources, hashes and actual JSON checks. No external
model or upstream Q#/Python framework was executed. This was informed authoring,
not a controlled evaluation of how well an unfamiliar LLM writes QLI.

The first check accepted 19 cases and rejected five. Unsupported Boolean `or`
and local `let` in basis bodies caused two parse errors; `repeat_static` in a
restricted auxiliary phase body caused three unsupported-body errors. The next
attempt used existing expression syntax and seven explicit T calls, accepting
all 24. The third attempt only removed unused imports and also checked.
A020-14/15 retain the concrete obligations and the actual rejected source.

Semantic validation covers 20 whole finite unitaries by every complex matrix
entry under controlled X/Y interference, two branch-sensitive teleportation
instruments, measurement polarity and four dense-coding messages: 9,412 probes
plus all 24 shipped mains. Four deliberate QLI counterexamples reject. These
checks caught no semantic discrepancy after the source repairs. They validate
the recorded specializations numerically, not upstream frameworks, scalability,
Rust adequacy or a general translation theorem.

The applications expose further scope limits: fixed angles, a changed-angle
QPE example, a signed-permutation VQE kernel and host-side observable aggregation.
The experiment did not import optimizers or chemistry data. A020-07/16 retain
those limitations. The rotation adapter preserves its scalar using seven
explicit T calls in this implementation; the Qualtran reflection needs the opposite sign from the existing
standard reflection. This is why ordinary outcome-only comparisons would be
insufficient evidence for reusable controlled operations.

These results follow the [adopted development method](design-philosophy.md#start-with-the-quantum-programs-we-want-to-write):
start with the quantum program we want to write, then develop the language with
AI from concrete gaps while retaining its contracts and independent checking.

## Iterative QPE and repair observations, 0.1.8

The [iterative QPE source](../examples/iterative_phase_estimation/README.md)
passed its initial check/run without source repair, then matched all exact
phase cases and independent off-grid Bell-branch tomography. This was an
informed repository session. The [saved records](../tests/fixtures/authoring_sessions/README.md)
also retain two curated diagnostic repairs; the accepted workarounds were
already known, so they do not measure how much diagnostics help an unfamiliar LLM.

Three explicit rounds and a Bit-specific helper remain necessary. This adds
concrete source evidence to A020-02/03. Each measured meter requires fresh
logical preparation; no implicit reuse is introduced. Type errors now show
exact expected/actual trees; restricted cleanup points to the explicit contract
form, with a negative test ensuring false cleanup still rejects.

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

## Reproduced friction, delivered fixes and next candidates

Fixture paths below are relative to
[the corpus](../tests/fixtures/qli_authoring/README.md). The user selected the
first three issues for implementation and explicitly deferred type/size
parameters and cross-interface QPE reuse. The
[0.1.8 regressions](../tests/fixtures/ergonomics/README.md) exercise the new forms.

| Priority / issue | Reproduction and current workaround | Obligation to remove; checking boundary |
| --- | --- | --- |
| 1: product-valued basis functions — addressed in 0.1.8 | The original `rejected/basis_tuple_pattern.qli` parse failure is now `accepted/basis_tuple_pattern.qli`: a unary pair pattern supplies an independently checked CZ meaning. The separate two-argument `rejected/meaning_pair_predicate.qli` still rejects, as required by the unary contract. | Basis parameter patterns remove manual workarounds for nonconstant product targets. They preserve full domain types and source arity and reuse finite basis binding/table checks. |
| 2: tuple arity — addressed in 0.1.8; layout equality remains explicit | The original third-field parse failure is now `accepted/nary_tuple.qli`. `rejected/product_association.qli` still rejects a right-associated input for a left-associated interface; `accepted/product_reassociation.qli` shows the adapter. | Types, expressions and patterns left-fold to existing pairs: `(a,b,c)` means `((a,b),c)`. Evaluation order, Unit factors, ownership, leaf order and depth limits are tested. This removes punctuation but does not equate all product trees. |
| 3: dropped-owner location — addressed in 0.1.8 | `rejected/dropped_owner.qli` originally pointed to the body opening, line 3 column 27. It now points to binding `b`, line 4 column 9. | Locate the actual parameter/local/computed binder without changing ownership rejection. Regressions include nested patterns, shadowing, UTF-8/CRLF and module paths. |

The remaining observations are tracked as [A020-01–08](v0.2.0-backlog.md#candidates):
product layout, target-type/size reuse, gate providers, classical result roles,
cleanup discoverability, QPE angle prerequisites and LLM evaluation. Type/size
work remains deferred; the backlog does not change R14 or implement a template.

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

The user explicitly deferred this issue while selecting authoring fixes 1–3.
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

**Follow-up adopted on 2026-09-28:** the user requested the Cargo-compatible
[version policy](versioning.md). Compatible features in 0.y.z (y > 0) now use
PATCH without exceptions; breaking changes use MINOR. Historical decisions and
0.1.8's documented reserved-name/public-AST migration remain recorded. This
policy change alone did not implement the language candidates above. The
subsequent continuation implements issues 1–3. The user retained 0.1.8 after
the temporary 0.2.0 selection; the public Rust `Param` migration stays explicit.
Continue evaluating LLM authoring through actual source and independent
semantic regressions, preserving failures that reveal missing abstractions.
