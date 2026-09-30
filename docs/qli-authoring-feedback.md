# Feedback from writing QLI programs

The user subsequently prioritized corpus implementation. The
[shared Xor/GHZ experiment](../corpus/sized/README.md) now starts from actual
`.qli` definitions, using one body at every selected size. Direct framing hit
the checker budget at Xor width four; flattening all bits still failed at eight.
Keeping register tails and explicit one-bit adapters admitted all selected
widths under the unchanged budget. This is a development source path, with
native checking and complete basis/reference diagnostics; production CLI
integration and general source preservation remain open. The
[first sources and actual failures](../tests/fixtures/authoring_sessions/sized-corpus-v021/session.json)
are retained. The subsequent [QFT/inverse source continuation](../corpus/sized/qualtran_qft/README.md)
now connects guarded affine sizes, controlled dyadic phases, ordinary source
modules and adjoint. The first lexer and missing-module diagnostics are
preserved; all selected widths pass native checks and independent forward/
inverse formulas. The [coherent QPE continuation](../corpus/sized/qualtran_qpe/README.md)
now connects `Op<Bits<n>>`, controlled repetitions and the same QFT source at
small selected sizes. Full phase/reference tests include off-grid phases,
non-basis eigenvectors and phase-sensitive provider changes; initialization,
measurement and `CBits` remain open. Remaining validation uses small qubit
systems by the 2026-09-30 user decision; the prior (8,8) capacity failure stays
historical, without further maximum-size checks. The measured
width-eight execution cost is 255 H/phase applications after gradient sharing,
versus 36 in the source staircase; two shared calls execute 510. Sharing removes
verification/storage duplication, not execution multiplicity. Track this actual
cost separately while completing H1–H5 and production integration.

The [shared AddK/Equals continuation](../corpus/sized/qualtran_arithmetic/README.md)
starts from preserved recursive source. Its first concrete failure was
`unknown static operation parameter all_ones`: recursive control needed a
transparent ordinary definition, not an abstract entry parameter. Explicit
multi-owner call groups and control/adjoint lowering now support that source.
No new arithmetic acceptance rule is needed. The first small width-three
Equals then exceeded the checker budget; extracting the repeated complement
and sharing identical imported graph/evidence entries admits it at 1,604,715
structural units, below the unchanged two-million limit. Both attempts remain
in the [session](../tests/fixtures/authoring_sessions/sized-arithmetic-v021/session.json).

All widths 0–3 pass complete basis/reference checks, with local empty ownership,
wraparound constants, inverse and controlled clients. Wrong carry order and
missing restoration remain type-correct circuit faults detected by independent
arithmetic oracles. Lexical operation hiding is checked even after a binding
has moved; the older Xor phase-fault generator now renames its `x` owner before
importing the gate `x`, so it remains a valid semantic counterexample. AddK's
nK execution cost is recorded. This is an informed development experiment,
with production source integration, named arithmetic contracts and universal
source preservation still open, and no new maximum-size checks.

The [local order/amplitude clients](../tests/fixtures/sized_clients/README.md)
now reuse that same coherent QPE. Their desired source first failed while
parsing a transparent operation in the callee's bracket arguments. The
producer now distinguishes natural and operation arguments in declaration
order and checks access at every forwarding boundary. Instantiation identity
includes nested providers, not just function and sizes; a phase-sensitive
two-provider case checks that distinction. Both clients pass small full-input
and reference diagnostics, including the N=15 baseline and p=0/1 amplitude
boundaries. Removing preparation or reversing a modular cycle can leave an
expected histogram unchanged while altering the residual target, which is why
the full complex operator remains the regression contract. The
[first source record](../tests/fixtures/authoring_sessions/sized-qpe-clients-v021/session.json)
is retained. Initialization/measurement, `CBits` and production integration are
still required; no new external corpus intake occurred.

The [measured QPE first attempt](../tests/fixtures/authoring_sessions/measured-qpe-v021/session.json)
now makes the next gap concrete: the desired wrapper imports initialization
and readout helpers, and the first check stops at missing `registers::init_zero`.
Inspection also finds no explicit assembly of measured `CBit` slots into
`CBits<m>` in the current hierarchy. Existing node typing for initialization
and one-bit measurement does not establish the complete instrument. The
[checkpoint](../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md)
retains this unfinished source experiment; work pauses at the user's request
before new checker or proof implementation.

The 0.2.1 [actual QFT hierarchy experiment](../tests/fixtures/hierarchical_ir/qft-binding-first/README.md)
now refines the preserved desired shared-QPE source before frontend integration.
The first circuit incorrectly attempted a within-register rewire for reversal;
explicit extraction, data swapping and reinsertion repairs it. Valid width-three
and width-four graphs initially hit repeated type/layout-checking work. Reusing
the proved actual type context now admits them under the same budget. A
[shared-gradient follow-up](../tests/fixtures/hierarchical_ir/qft-shared-gradient-native.json)
retains recursive register boundaries and shares phase subgraphs through
existing controlled/repeat rules. Every width 1–8 passes under the same budget;
the directly lifted width-eight failure remains a regression. This identifies
actual hierarchical reuse as a source requirement, rather than expanding every
gate around a whole register. These are informed IR-authoring and
independent Fourier-oracle results, not executable generic `.qli`, a model
benchmark or completed QFT-schema binding.

**2026-09-28; observed in the 0.1.8 development tree.** The user requested
source/examples/tests first, with language requirements discovered from actually
writing algorithms. The [protocols](../examples/protocols/README.md),
[operation algorithms](../examples/operation_algorithms/README.md) and
[source fixtures](../tests/fixtures/qli_authoring/README.md) are the deliverable.
The initial observations below led to the user-selected 0.1.8 fixes; the
[grammar](syntax-v0.md#authoring-forms-added-in-product-018) specifies the
delivered forms. Unresolved candidates now live in the
[v0.2.0 backlog](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md), with stable IDs and acceptance experiments;
this report retains the observations and reasoning that motivated them.

The user also supplied Claude's account of a successful first-attempt
teleportation and Ubuntu build. Those are external reports, not locally
reproduced timing, first-attempt or Linux results. We reproduced the supplied
body's four-branch distribution, with explicit imports, on macOS. The new
programs were authored and revised in this session: there is no controlled
comparison of models or estimate of general LLM success rate.

## Code-driven continuation, 0.2.0

The [0.2.0 review reproductions](../tests/fixtures/review_v020/README.md) preserve
six informed source fixtures before checking. The first CLI invocation mistakenly
passed a file where a directory is required; that diagnostic is retained, followed
by the corrected invocations on unchanged source. Long sampling and 40-receipt
IR export now succeed with no source repair. Doubling expansion and exact
`repeat_static` capacity still reject, with clearer locations and explanations;
A020-03 retains the underlying scalability burden. These are maintenance
regressions, not controlled authoring or model-performance measurements.

The later [0.2.1 reshape attempt](../tests/fixtures/authoring_sessions/reshape-v021/session.json)
preserves desired `reshape::<(Bit,Bit,Bit)>(q)` source and its real parse failure
at `::`. This informed draft has no repaired executable successor yet. The
[Lean experiment](size-expressions.md) removes enumeration from the canonical
adapter's encoding argument, but does not yet remove handwritten adapters from
user `.qli` programs. A020-01 retains source production and ergonomic validation
as open work; this is not a measured authoring-success result.

The [QLT first-source packet](../tests/fixtures/qlt_design/README.md), recorded
on 2026-09-29, captures a future mathematical test language. It retains QFT/DFT,
modular-increment, cost and doctest drafts, plus deliberate sign/reversal/phase
faults and an unsupported-domain case. The current `.qli` subjects check with
zero repairs, while `qleisli test` is still rejected as an unsupported command.
No QLT assertion was executed. The proposed improvement is removal of repeated
host harness and diagnostic plumbing, while keeping independent mathematical
references. Before/after authoring and evaluation costs remain unmeasured;
[A020-21](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md#a020-21--mathematical-quantum-tests-require-separate-host-harnesses)
tracks the future experiment without adding a 0.2.0 release requirement.

The [shared-QPE first source](../tests/fixtures/authoring_sessions/shared-qpe-v020/session.json)
was saved before its actual 0.1.9 parse failure. Current design adopts `CBits<m>`;
the old `CWord<m>` snapshot remains unchanged. The later
[coherent source experiment](../tests/fixtures/authoring_sessions/sized-qpe-v021/session.json)
now uses one body across (1,3) and (2,4) with actual controlled provider graphs.
It measures structural work and numerical semantics separately, without
claiming a production measured API. The initially measured (8,8) budget failure
is retained, and the user's 2026-09-30 scope change defers further maximum-size
validation. This is informed development, not a controlled authoring benchmark.

The [Grover session](../tests/fixtures/authoring_sessions/grover-trial-v020/session.json) records one real repair: adding the original missing local kernel. After that, the exact same source moves from an unsupported sample command to four fresh `11` samples at seed 0, with 22 execution steps each. Sampling required **zero subsequent source revisions**; body duplication and layout conversions are unchanged. The author no longer writes a random trajectory executor or retry-state/error bookkeeping. The [sampled Shor15 host](../examples/sampled_shor15.rs) is the second use: seed 0 accepts on attempt 3 after two invalid candidates, with validated period 4 and factors 3 and 5. These are informed development observations.

[Independent tests](../tests/sampling.rs) use Bell/reset/feedback correlation and the analytic H T H probability, including RNG/numerical/limit failures. [Portable evidence tests](../tests/interchange.rs) distinguish matching contracts from type-correct wrong phase and equal-width wrong type trees. Current finite tests do not establish shared QPE, general Shor or a controlled model-performance result.

The later [0.1.9 review reproductions](../tests/fixtures/review_v019/README.md)
preserve first source bytes and real before/after diagnostics. A bare CR now
points directly to a lexical error; one explicit CRLF repair exposes the X
line and changes the measurement from zero to one as intended. The nested
static argument needs no source repair after repeated squaring (observed debug
check: 12.333 to 0.892 seconds); repeated calls share a checked exact budget.
No algorithm body duplication or manual layout conversion was removed by these
repairs. Structurally valid wrong phase/control/axis circuits fail the independent
meaning comparison. These are development observations, not a model benchmark.

## Review follow-up, 0.1.9

The supplied 0.1.8 review exposed a parser panic on truncated static arguments
such as `unitary fn f(q: Q<Bit>) -> Q<Bit> { g[`. This is especially relevant to
incomplete generated source. The [parser regressions](../tests/parser.rs) now
exercise every token-boundary prefix of static constructors, executable examples
and bundled library files; [CLI tests](../tests/cli_json.rs) preserve the single
JSON parse diagnostic at EOF. This is robustness validation, not a new measured
authoring session or a model benchmark.

[A020-09](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md#a020-09--controlled-access-can-derive-inverse-access-through-constructors)
retains the future opaque-provider capability design question.
[A020-10](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md#a020-10--source-snapshot-copies-exhaust-the-shared-lowering-budget)
is resolved by private shared retention: source bytes are copied/charged once
across providers and contract pairs, with public identities and exact checking
preserved. The 100 KB/256-provider and unrelated-comment regressions pass.
The [0.1.9 record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.9.md) separates compatible repairs and clarifications from future breaking changes.

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

## Simple corpus expansion, 0.2.2

The [six first attempts](../corpus/authoring/v022-simple/session.json) add
SWAP/Fredkin, constant XOR/bitwise complement, and RX/one-bit phase kickback.
Every source was saved before checking; all six first checks passed with no
source repairs. This was informed authoring with known tuple/control/rotation
workarounds, not a controlled model evaluation.

The simple sources exercise separate obligations: SWAP keeps logical owner
positions while exchanging amplitudes; Fredkin preserves a coherent control;
constant XOR makes low-bit ordering explicit; RX still requires its scalar
under control (existing A020-15). The one-bit kickback explicitly narrows the
original four-bit secret and returns both owners. No newly discovered syntax
friction or new language/library API is claimed. Existing phase/host boilerplate
records remain applicable. Six labelled semantic mutations are separate from
the successful first-attempt sequence and require independent oracle rejection.

## Corpus expansion, 0.2.1

The [six new translations](../corpus/authoring/v021-expansion/session.json)
cover majority-oracle Deutsch–Jozsa, Bell measurement, modular constant addition,
equality, LCU projector embedding and quantum-kernel overlap. All six original
sources were saved before checking, and all six first checks passed. No source
repair was needed. Existing tuple routing and phase-preserving rotation
workarounds were known; this is informed authoring, not a controlled benchmark.

The additions make two obligations concrete. The overlap author still writes
exact scalar phases and host-side probability aggregation (A020-15/16). The
LCU author must choose a full unitary PREP completion, retain selector ownership
and distinguish its projected block from a deterministic operation or clean
return. [A020-23](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md#a020-23--state-preparation-and-projected-blocks-need-distinct-contracts)
records that new friction and its checking experiment. No language abstraction
or production evidence rule is added by these translations.

Six separately labelled [semantic faults](../corpus/semantic_faults/README.md)
were deliberately authored after the successful first checks. They are not
repair attempts. Their independent oracles check full complex entries or Bell
measurement's branch/reference Choi state; observing a plausible output from
the shipped example alone is insufficient.

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

The authorized 0.2.1 continuation preserves a [sized-Xor session](../tests/fixtures/authoring_sessions/sized-xor-v021/session.json)
and a [linear-size reshape session](../tests/fixtures/authoring_sessions/sized-reshape-v021/session.json).
Xor's reserved-name repair reaches the unsupported range token `..`; the
reshape draft rejects `+` in `Bits<n+m>`. These are informed first-source
observations under the [adopted size design](size-expressions.md), not measured
model trials or working APIs. No reduction in authoring obligations is claimed
until the shared source checks, lowers and executes with bound evidence.

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

The remaining observations are tracked as [A020-01–08](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md#candidates):
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

## Lean kernel migration development record (2026-09-29)

The [first executable-kernel record](../tests/fixtures/lean_kernel/README.md)
preserves a current `.qli` target, desired phase-word artifacts, the actual
missing-executable baseline, a failed proof attempt and native after-results.
The public obligation removed in this slice is trusting a proposed phase
summary: an actual proved Lean function now compares the gate word with a
separate required action. It removes no `.qli` duplication or manual wiring;
those counts stay zero rather than being presented as an authoring improvement.
The T-equivalent positive case is paired with a well-typed global-phase
counterexample and a separate exact Rust circuit experiment. General dyadic
source, shared QPE and translation validation remain future work. This is
informed development, not a controlled model evaluation or fourth corpus source.

## Tuple equality correction and type contract (2026-09-29)

The user superseded the historical left-fold choice above: flat and nested
products must be different types. The [consolidated type contract](type-system.md)
and [tuple migration](tuple-shapes.md) now specify exact arity, nesting, ownership
and explicit conversions. The [preserved counterexample](../tests/fixtures/tuple_shapes/baseline.json)
shows the old checker accepting a flat basis result as a nested result; the
updated checker rejects it with both shapes in the diagnostic. The
[explicit adapter](../tests/fixtures/tuple_shapes/explicit_layout.qli) is checked
by exact function evidence and an entangled-reference execution test.

This correction removes an implicit source-to-type association, not manual
conversion work: explicit adapters are now visible where shapes differ. Three
external-corpus kernels spell their former binary shapes explicitly, retaining
their licenses, numeric contracts and all old authoring snapshots in the
[appended migration attempt](../corpus/authoring/session.json). QPE fixture
consumers now match their producer's actual three-field result. This is an
informed migration with real diagnostics, not a controlled model evaluation.

## Shared hierarchy continuation (2026-09-29)

The [CD-3 record](../tests/fixtures/lean_hierarchy/README.md) preserves the first
nested-repeat source, its actual finite-evidence rejection, the desired shared
artifact, an initial failed Lean proof and later native results. The experimental
DAG checker now validates the three-definition artifact without expanding its
16,777,216 implied primitive operations. A second reuse experiment checks mixed
call/sequence/repetition DAGs against independent small execution, including
well-typed wrong-phase counterexamples and false intermediate claims.

The removed burden is expanding repeated bodies for this IR verification.
The original `.qli` still rejects: zero duplicate source definitions or manual
layout conversions have been removed. Complete repair counts were not measured;
the first failed proof is retained, without claiming a full editing transcript.
Costs distinguish input/evidence size, stored definitions, charged checker work
and implied execution multiplicities. A020-02/03/07, shared order-finding and
amplitude-estimation clients remain open. This is an informed implementation
experiment, not a measured model-performance result.


## Typed layout continuation (2026-09-29)

The [first multi-owner source](../tests/fixtures/lean_layout/first_source/main.qli)
already checks in Rust but could not be represented by the earlier one-owner
Lean phase DAG. The [typed layout component](lean-layout-slice.md) now checks
full owner/axis maps independently, retaining exact n-ary shape and Q<Unit>
ownership. Its two-sided permutations and reference-coefficient round trip
are proved about executable definitions. This removes manual assurance about
a submitted layout, not source adapters: `.qli` generation/integration and
broader authoring improvements remain open. Actual first diagnostics, corrected
proof/test attempts and after-state metrics are in the
[development record](../tests/fixtures/lean_layout/README.md). The experiment
adds no new external source and is not a controlled model benchmark.

## Shared typed calls (2026-09-29)

The [first source](../tests/fixtures/lean_layout_dag/first_source/main.qli) reuses
one ordinary swap definition twice while retaining `Q<Unit>`. It required zero
source repairs; the old experimental Lean command rejected the desired DAG.
The [continuation](lean-layout-dag-slice.md) now validates explicit call adapters,
dependency identity and ordered composition with a direct-graph soundness proof.
A second independent exercise composes noncommuting permutations, arbitrary
reference amplitudes and differently shaped registers. Type-valid wrong
dependencies/adapters/orders fail an unchanged consumer request.

The removed checker obligation is expanding shared layout bodies or relying on
manual assurances about call wiring. No source definition duplication or manual
source adapter has been removed yet: there is no source-to-layout-DAG producer.
The retained [development record](../tests/fixtures/lean_layout_dag/README.md)
includes the actual initial Lean, compiled-audit and oracle diagnostics. These
are informed engineering observations, not measured model performance.

## Phase and typed-call composition (2026-09-29)

The [first source](../tests/fixtures/lean_phase_layout/first_source/main.qli)
applies the same phase-and-swap body twice, retains a quantum Unit owner and
adds a controlled T. It required no source repair. The previous experimental
Lean command could not check a joint phase/layout graph. The
[combined component](lean-phase-layout-slice.md) now binds actual phase axes,
call adapters and sparse composition to an independently requested cyclic action.
The removed checker obligation is manual phase/axis accounting or expanded
shared bodies; source duplication and manual source conversions are unchanged.

A separate [finite interference client](../tests/fixtures/lean_phase_layout/interference_client/main.qli)
prepares and measures both bits. Its four probabilities agree with an independent
Fourier sum on both installed Rust toolchains. It uses supported T phases;
π/8 and finer angles belong to the new Lean experiment. This does not establish
source-to-new-IR translation. [Actual diagnostics and observations](../tests/fixtures/lean_phase_layout/README.md)
include polynomial proof repairs, kernel reduction choices and work-accounting
review. No full repair count, generation-time improvement or LLM benchmark is claimed.

## Interference foundation (2026-09-29)

The [retained source experiment](../tests/fixtures/lean_interference/README.md)
uses H;T;H;H;T;H and a second client acting on half of a Bell pair. Both original
sources execute unchanged; their independent expectations are two equiprobable
outputs and four equiprobable joint outputs. The executable Lean normalizer now
has an amplitude-preservation proof, and the separate proof package instantiates
the actual definitions over complex numbers. This removes a proof obligation
from future compiler-generated H-pair rewrites. It has not yet reduced source
body duplication, wiring or source repairs: each remains unchanged. Initial
proof diagnostics and native/complex comparisons are retained; no controlled
model-performance or QPE-completion claim follows.

## QFT circuit proof (2026-09-29)

The [retained round trip and wrong-reversal source](../tests/fixtures/lean_qft/README.md)
exercise ordinary qft3. Both initial programs pass typing without repair; the
second fails the intended round trip and agrees with an independent F† R F
calculation. Source duplication and wiring costs remain unchanged. The new
symbolic-path/Fourier theorem removes the obligation to prove that literal QFT
pattern separately at each width 1–8. Native symbolic visits and small complex
oracles are recorded separately from proof elaboration and source execution.
This is informed development, not a measured model-performance study.

## QPE instrument and completeness (2026-09-29)

The [retained off-grid Bell client and dephasing fault](../tests/fixtures/lean_qpe_instrument/README.md)
have identical phase-label marginals but different residual X correlations.
Both first sources check without repair. Native plan checking visits precision
stages without executing their powers; actual controlled execution retains up
to 255 provider applications. The component theorem proves full branch maps,
then completeness and reference-trace preservation under a provider-isometry
premise. U=2I is a counterexample to omitting that premise. This removes a
repeated schema-proof obligation; source body duplication and manual wiring
are unchanged until the external hierarchy and sized source are integrated.

## Registry and dependency integration (2026-09-29)

The same retained shared-QPE source now motivates the shipped component
type/source manifest and full-profile dependency scheduler. They remove no
source-level duplication or manual wiring yet. They make stale theorem types,
changed provider/schema metadata and unsafe dependency schedules reviewable and
continuously checked. The [152 native graph cases](../tests/fixtures/hierarchical_ir/README.md)
include sharing and capacity boundaries; no runtime expanded-use speedup or
controlled model-performance claim follows. Typed graph extraction and exact
logical/physical endpoint binding are now implemented by the artifact preparer.
Its 54 structural and 22 reference cases preserve flat/nested distinctions and
zero-width owners, and charge repeated endpoint comparisons against the same
budget as graph scheduling. The retained phase mutation intentionally prepares
without receiving semantic evidence. Full node/provider/encoding/derivation
checks and sized-source implementation remain the next obligations; authoring
duplication and manual conversion counts have not decreased in this step.
The subsequent 39 side-map cases check whole port/axis permutations and exact
types, including zero owners. The mathematical round-trip result supports
future call/rewire checking, while source authors still need the explicit
conversion and sized-source implementation.

## Actual definition-node typing (2026-09-29)

The [node checker and fixture](../tests/fixtures/hierarchical_ir/README.md)
now apply those maps to both sides of real calls. Cases with two separately
valid maps but inconsistent owner/wire names fail, as do tensor frames that
capture identities across their input/output lifetimes. All 69 native cases
pass their independent expected decisions. A locally closed zero-repeat parent
is paired with a malformed body: the whole-definition pass rejects it.
Preparation, map checks and node typing share one budget. The resulting theorem
is structural; the well-typed wrong phase and opaque leaf remain semantic
obligations. Source duplication and manual conversion burdens are unchanged.


## Meaning/encoding typing and controlled target types (2026-09-29)

The next [164 native cases](../tests/fixtures/hierarchical_ir/README.md) cover
all meaning and encoding constructors, including the 64 selected QPE width/
precision headers. Zero-repeat meaning bodies and scratch ownership are
checked under the same budget as the actual definitions. The pre-change
controlled Bit-to-Bits(1) counterexample was retained before tightening the
inactive-sector target-type rule; consistent renaming remains accepted.
The actual checker has whole-table coverage theorems and passed compiled
runtime audits. These structural results do not discharge finite semantics or
mathematical equations. Desired shared source remains unimplemented, so this
step does not claim a reduction in author duplication or manual conversions.


## Explicit register and tuple conversion boundary (2026-09-29)

The desired [take/put helper](imaginary-v1/qpe.md#visible-algorithm-and-ownership-routing)
now has an internal [structural conversion checker](hierarchical-ir-spec.md#explicit-structural-conversions).
It covers all eight widths and every selected axis, requires the Bits(0)
remainder at width one, and preserves immediate tuple arity and nested fields.
Both definition and meaning typing call this actual predicate. Its basis
bijection and arbitrary-reference coefficient round trips are proved without
matrices; 123 native cases include 7,216 independently checked basis routes.
The first source, actual harness failure and repair record are retained.
Source lowering is still pending, so no source-length, duplicate-definition or
manual-conversion reduction is claimed yet. This closes an internal prerequisite
of A020-01 rather than the authoring obligation itself.


## Controlled phase and reference correlation (2026-09-29)

Two retained ordinary [QLI source probes](../tests/fixtures/lean_qpe_instrument/README.md#coherent-controlled-power-completion)
prepare a control/reference Bell pair and a |+> target, then apply controlled
X or −X. Uncompute and interference distinguish 000 from 100. Both first source
attempts passed without repair; the second program is a type-correct semantic
counterexample. The new native exact oracle independently distinguishes X^2
from (iX)^2 even when their basis probabilities agree. The actual coherent
runtime action now has a complex operator/reference proof and the registry
binds that stronger statement. These are informed development observations,
not an algorithm correctness proof, controlled model study or sized-source
completion. Source duplication and manual routing burdens remain unchanged.

The [subsequent binding packet](../tests/fixtures/hierarchical_ir/power-binding-packet.md)
extracts control/repetition and logical power directly from the actual hierarchy.
Seven well-typed count/polarity changes pass structural typing but fail the new
projection. Independent definition/meaning table permutations check that their
indices cannot be confused. The component's native tests retain pending provider
proofs, including deliberately false meaning data, so an author cannot replace
semantic checking with a schema name. The actual operator/reference bridge is
proved with explicit provider premises. This removes an internal duplicated
circuit witness obligation; sized source and author-visible code reduction
remain unfinished. First sources, real diagnostics and repairs are retained.

The [provider derivation continuation](../tests/fixtures/hierarchical_ir/derivation-packet.md)
now rejects the false and opaque provider obligations instead of treating their
projection as sufficient. Whole-space rules bind exact actual children and
premise equations; an empty internal cache prevents supplied success flags from
replacing those checks. The 235-case native suite includes an independent
recursive rule oracle and exact phase/permutation interpretation. The Lean
closure proof concerns this actual pass; complete complex interpretation,
finite leaves, source lowering and author-visible burden reduction remain open.

The [next interpretation packet](../tests/fixtures/hierarchical_ir/operator-packet.md)
proves those supported derivation equations under interpretation of actual
definition/meaning bodies and instantiates them with complex operators and
arbitrary reference maps. The direct-power bridge now obtains its provider
equation from the accepted derivation. Six mathematical example theorems retain
phase, orientation, tensor ordering and control counterexamples. This removes
an internal assumed provider-equation obligation; construction of the complete
semantic environment, provider unitarity, finite leaves and source support
remain open. No reduction in source duplication or manual author wiring is
claimed at this proof-only checkpoint.

The [constructed-evaluation continuation](../tests/fixtures/hierarchical_ir/evaluation-packet.md)
then removes the assumed interpretation environment for supported accepted
derivations. Actual implementation and meaning tables have equal successful,
unique mathematical denotations, even when their index orders differ. Zero
repeat does not hide a missing or cyclic body; unsupported finite claims remain
failures. Nine kernel-checked example theorems exercise these cases through
π/8. This discharges a proof obligation rather than changing source ergonomics;
whole-space unitarity, finite reconstruction, remaining schema/rule integration
and the common QLI source still need implementation and acceptance evidence.

## Published 0.2.1 review follow-up (2026-09-30)

The user-supplied review describes a natural flat Toffoli result pattern and
TH repetition capacity failure. [Curated minimal sources](../tests/fixtures/review_v021/README.md)
are preserved before local checks; these are review reproductions, not measured
LLM first attempts. In 0.2.2, grouped/nested imports eliminate separate-use
rewrites; serial-copy validation accepts TH 400/512/1000/1024 without computing
the full product matrix. One-body finite checks, explicit contract/adjoint/qif
capacities and flat expansion remain. Toffoli's nested public result stays for
PATCH compatibility, with a checked nested repair and the existing tuple issue
tracking the v0.3 migration question. The independently authored seeded harness
exercises exact extraction and numerical X/Y/Z/reference/control/feedback
statistics; it is not the reviewer's unprovided 6000-case harness or a model
benchmark. [The review response](releases/v0.2.2.md) separates fixes and open work.
