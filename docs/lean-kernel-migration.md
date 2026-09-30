# Rust frontend and Lean 4 verification kernel

Status: **staged migration adopted; experimental phase-word, phase-DAG, typed-layout, typed-call and combined phase/layout
slices implemented; production verification remains in Rust**. The user selected this
direction during 2026-09-28–29 JST. The development version is 0.2.2, currently
unreleased; see its [record](releases/v0.2.2.md). The latest published release is
[0.2.1](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.1.md). Foundation publication evidence
remains in the [0.2.0 record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md). The [0.2.0 foundation scope](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md) retains
the implemented components. The 2026-09-30 [0.2.1 boundary](v0.2.2-plan.md)
retains completed experiments and bounded connections; heavy production
hierarchy/common-QPE integration and proofs move to [0.2.2](v0.2.2-plan.md),
with M0–M5 and H1–H5 intact. The later 2026-09-30 user instruction assigns
verification implementation to [eight packets through 0.2.2–0.2.9](verification-migration-v0.2.md),
superseding the K1/0.3.0 and K2/0.4.0 schedule. Shared-QPE feature integration
retains its dependencies and gates across that continuation; it is no longer
all assigned to the first 0.2.2 packet. Production authority is unchanged.
The 2026-09-29 refinement makes proof of the
[Qleisli Soundness Theorem](release-milestones.md#qleisli-soundness-theorem-v050)
the central v0.5.0 milestone, with broader community development from v0.5 onward.
The subsequent 2026-09-29 decision adds the
[Physical Realizability Theorem](release-milestones.md#physical-realizability-theorem-v1)
and substantive Lean backend implementation/proofs as requirements by v1.
The explicit 2026-09-30 [trust-boundary amendment](../TRUST_BOUNDARY.md#resource-safety-amendment-2026-09-30)
adds the [Resource Safety Theorem](release-milestones.md#resource-safety-theorem-v1)
as a third pillar, to prove. Actual static resource analysis and pass-bound
preservation must meet RS-C1–C5 by v1; resource proposals remain untrusted and
present acceptance/production authority is unchanged.

## Architecture and authority

During K0–K3, Rust retains source parsing, diagnostics, CLI/JSON, interop,
simulation and untrusted generation of IR and evidence. The acceptance core
moves in bounded steps to Lean 4: exact arithmetic, semantic evidence checking, then raw IR
ownership/effect verification. New production M2 kernel work starts in Lean;
the Rust [research kernel](../research/semantic-kernel/README.md) remains an
experiment and an independent differential oracle.

The longer-term direction is to migrate the implementation beyond the frontend
to Lean, beginning with the correctness-critical backend transformations and
checkers needed for realizability. This is not a goal of rewriting all code
in Lean: candidate and proof search may remain external, as specified by the
[LeafRealizer policy](#external-search-and-the-leafrealizer-checker).
Rust frontend output remains untrusted and needs source-to-IR translation
validation for source-level guarantees. Migrating the backend is a project
prerequisite for the intended end-to-end Lean guarantee, not a claim that
using Lean alone proves correctness. Auxiliary CLI/interop/simulator migration
can continue beyond v1; the v1 gate is the actual supported synthesis and
emission path with its correspondence proofs.

The separate [QLT plan](https://github.com/MGYamada/Qleisli/issues/50) deliberately starts its experimental
mathematical test evaluator in Rust from v0.4.0 onward, after the
[0.3.0 type-system work](v0x-roadmap.md#v030-qleisli-type-system-specification), then migrates evaluation and
cost definitions to Lean from 0.5 onward. It issues no production acceptance
evidence and does not authorize new Rust M2 checker rules. Its adequacy and
certificate work is independent of the S05/PR release gates; the later runtime
retains the same Mathlib-free boundary and separately imported proof bridge.

The executable package [lean-kernel](../lean-kernel/README.md) depends only on
Lean's `Init`/`Std` libraries, pinned to **Lean 4.30.0**. Its manifest has no
external packages. Existing [lean](../lean/README.md) models and mathematical
proofs retain Mathlib 4.30.0. The [first complex bridge](lean-interference-slice.md)
imports the actual executable H/diagonal definitions and the phase/layout
checker's theorem through a local dependency. The executable package must
never import that bridge or Mathlib. Full hierarchical/instrument interpretation
remains open beyond those local amplitude and weighted-basis-transition laws.

The **Qleisli Soundness Theorem**, targeted for **v0.5.0**, is about the actual
pure executable function. In shorthand:

\[
\operatorname{verify}(p,C,\pi)=\mathrm{true}
\quad\Longrightarrow\quad \llbracket p\rrbracket\models C.
\]

Here the caller supplies `C` independently of the artifact. The theorem must
cover exact phase, interfaces, encodings, effects, auxiliary zero return and
arbitrary references where the profile requires them. A Lean implementation
alone does not establish this implication. Each enabled rule needs its own
soundness proof and composition into the complete checker theorem. The
[authoritative S05-C1–C5 gates](release-milestones.md#qleisli-soundness-theorem-v050)
fix its full declared production scope, proof/audit, binding and public review
requirements. The existing phase-word and cyclic-action DAG theorems do not
close this milestone.

Serialized Rust handles, pointer identity and producer-supplied theorem IDs
carry no authority. A checker reconstructs evidence from bounded data, checks
all references and compares it with an independently fixed request. Execution
and emission must use the very artifact checked, or a separately validated
meaning-preserving transformation. Full IR validity does not establish source
translation, optimization or backend preservation.

The future [Lean-assisted debugger](https://github.com/MGYamada/Qleisli/issues/51) uses this checking
boundary to report mathematical obligations and independently replayable
mismatch witnesses, with later K4 source/backend tracing. The presentation and
repair layer remains untrusted. Its witness-checking correctness is a separate
obligation; rejection by the acceptance checker does not itself refute the
requested mathematical claim. This tooling adds no K0–K4 release gate.

## Pipeline migration with a stable IR verification boundary

**User-adopted migration policy, 2026-09-29:** move pipeline passes from one
end in a deliberate sequence, either backend to frontend or frontend to
backend. At every stage, preserve independent IR checking at the Rust/Lean
boundary. Record the chosen direction and the IR contract at that boundary
for each migration packet.

For backend-to-frontend migration, moving and proving one adjacent pass at
a time extends the verified downstream segment upstream and shrinks the Rust
producer. The target arrangement evolves as follows:

```text
Rust upstream + pass P -> IR check -> verified Lean downstream
Rust upstream -> earlier IR check -> proved Lean P -> verified Lean downstream
```

These are migration targets, not a diagram of today's proof coverage. The
invariant is **independent checking of the boundary IR, followed by the
verified downstream segment**. Its position and IR level may move; the
[fixed trust partition](../TRUST_BOUNDARY.md) does not change. In particular,
Lean implementation code does not become a new trusted assumption merely
because it has moved across the language boundary.

Each pass migration must preserve the following obligations:

- Reconstruct the actual immutable IR and evidence at the boundary and check
  them against an independently supplied contract. Types, ownership, effects,
  phase, reference behavior and auxiliary return retain their specified checks.
  Producer flags, cached success or a Rust handle cannot bypass that check.
- Prove meaning preservation for the actual migrated transformation under its
  declared input/output profiles, or independently validate its translation
  before claiming its output is covered. Compose that result with downstream
  correctness. A well-formed output alone does not prove preservation of the
  input meaning; exact and certified-approximate contracts remain distinct.
- Keep execution/emission bound to the checked artifact and proved or validated
  transformations. Preserve audits, differential/mutation checks, explicit
  native/transport assumptions and public compatibility obligations. Retire the
  corresponding Rust path only after its replacement meets the applicable gates.

Frontend-to-backend migration follows the same invariant: any remaining Rust
transformation still produces untrusted IR, which must cross an independent
check before entering the verified downstream segment. An isolated Lean
frontend pass does not make the remaining Rust backend verified. Record any
unproved segment or transitional Rust premise explicitly rather than letting
a language boundary imply a guarantee.

This fixes the migration method, not a new trusted component or immediate
production-authority transfer. Current Rust acceptance, the transitional
finite-leaf premises and the K0–K4/S05/PR gates remain as recorded below;
source adequacy and backend preservation remain separate proof obligations.

## External search and the LeafRealizer checker

**User-adopted refinement, 2026-09-29:** apply the de Bruijn criterion at the
level of each pipeline pass. Separate finding a result from checking its
correctness. Move correctness-critical transformations and their checkers to
Lean with proofs; keep expensive candidate/proof search outside the trusted
boundary when its results admit independent checking. There is no requirement
to migrate every Rust component or search algorithm to Lean.

For rotation synthesis, norm-equation search may remain an **untrusted external
oracle** that proposes a circuit and witnesses. Put the **`LeafRealizer`
checker in Lean**, and prove soundness of its actual executable acceptance
function. Here `LeafRealizer` names the adopted future checking role, not an
implemented type, command, serialized schema or enabled synthesis profile.
The external oracle is a classical search service, not an assumed quantum
operation capability.

The checker must bind the independently requested ideal operation, target
gate profile, interfaces and any error budget to the actual proposed circuit
and certificate. Check the norm-equation witness and its connection to the
circuit realization; a solved auxiliary equation alone does not establish the
requested synthesis contract. Exact realization retains phase, ownership and
clean return. Approximate realization requires the declared metric and a
certified bound, including the specified reference and composition behavior;
[approximation never substitutes for exact cleanup](coefficient-domains.md#exact-approximate-and-device-contracts).

Only a successful check authorizes use of the candidate in the verified
pipeline. The search strategy, language, heuristic and success flag carry no
authority. Search failure or budget exhaustion remains an explicit failure
to obtain a realization, not a proof that none exists. The checker and its
composition into the backend require proofs and the usual bounded transport,
artifact-binding, audit and mutation checks; the search procedure itself need
not be proved correct or rewritten in Lean.

This refinement preserves the IR-boundary invariant: external search can feed
proposals into any migrated pass, but only its checked result enters the
verified downstream segment. It changes where computation lives, not PR-C2's
realizability/synthesis obligation or the declared success/failure contract.
It adds no current approximation API or new 0.2.1 scope.

## Backend execution must match kernel definitions

**User-adopted requirement, 2026-09-29:** a substantive proved Lean backend
remains necessary by v1. Keeping synthesis search external does not replace
that requirement with an external backend plus a certificate wrapper. The
backend's correctness-critical transformations, realization checking and
emission must meet PR-C1–C4 over their actual definitions.

For project-owned executable kernel and backend code, forbid all four escape
hatches in both source policy and compiled-declaration CI:

| Forbidden construct | Why the backend policy rejects it | Compiled audit check |
| --- | --- | --- |
| `unsafe def` | Bypasses Lean's safe-definition discipline. | `ConstantInfo.isUnsafe` |
| `@[implemented_by]` | Substitutes a runtime implementation for the definition seen by the logical kernel. | `Compiler.getImplementedBy?` |
| `@[extern]` | Supplies an external implementation outside the checked Lean definition. | `getExternAttrData?` |
| `partial def` | Does not expose its recursive implementation as a total definition whose execution is covered by the intended theorem. | `ConstantInfo.isPartial` |

An axiom allowlist alone is insufficient: an axiom-free theorem about a
logical definition can coexist with an `implemented_by` or `extern` runtime
replacement. Keep declaration-metadata checks alongside transitive axiom
checks, the existing `native_decide` prohibition and fresh kernel replay.
Inspect declarations by **origin module**, including private, unreachable and
compiler-generated helpers, even if their declaration names use a different
namespace. A generated partial helper is a violation even when the author
wrote an ordinary `def`.

The existing [source checker](../scripts/check_lean_kernel.py),
[compiled audit](../lean-kernel/Audit.lean) and
[CI regression suite](../scripts/test_check_lean_kernel.py) already enforce the
four bans for `lean-kernel/`. The suite now explicitly covers nested backend
modules, private declarations outside the module's namespace, axiom-free
replacement examples and generated partial helpers. Source modules omitted
from the root import/audit fail; build-time audit and reduction-test harnesses
cannot enter the executable import graph. The current package has no separately
implemented backend or `LeafRealizer` API. Any future separate backend package
must establish the same source, complete import/declaration audit and negative
CI gates before entering the executable pipeline; moving files is no exemption.

The audit harness itself runs only during development and is not shipped as
kernel/backend code. Lean's allowed standard-library primitives, native compiler,
runtime and transport assumptions remain explicit in the trust ledger. These
checks forbid project escape hatches; they do not prove native compilation or
hardware correctness. This policy strengthens implementation discipline without
claiming the planned backend or its preservation proofs are already complete.

## Staged migration

These are intended integration boundaries, not deadlines. Compatible work can
ship as PATCH under [versioning](versioning.md); a stage number does not itself
justify a MINOR. Public acceptance/capacity/format or authority changes get an
explicit compatibility and migration review.

**Schedule revision, 2026-09-30:** the user selects 0.2.2–0.2.9 for verification
implementation migration. The [packet plan](verification-migration-v0.2.md)
provides the inventory, exact/finite, pure/observing IR, hierarchy and transport
sequence. K1/K2 implementation moves earlier; the v0.3.0 type-system target,
v0.4.x review preparation and v0.5.0 theorem/authority gates remain.

| Stage and intended boundary | Implementation | Gate before advancing |
| --- | --- | --- |
| **K0 / shipped 0.2.0 foundation, 0.2.2 inventory** | Reuse the separate Mathlib-free package, actual component theorems, experimental protocols, Rust launcher and audits. VM-22 inventories every existing acceptance path and fixes the next boundary contracts. | Shipped components remain reproducible. New M2 rules stay disabled until actual-checker proofs, binding and H1–H5 pass; hierarchy closure is assigned to VM-27, not inferred from K0 or the 0.2.2 version. |
| **K1 / 0.2.3–0.2.4: exact meanings and contracts** | VM-23/24 migrate canonical exact scalars, bounded matrices/leaves, contract equations and evidence reconstruction, with separate complex interpretation proofs over the same definitions. | Equality and operations agree with interpretation; phase/type/axis/source mutations reject. Preserve public arithmetic/capacity failure behavior and aggregate work limits. Raw-program evidence also requires K2 extraction. |
| **K2 / 0.2.5–0.2.9: complete checking and dual integration** | VM-25/26 migrate pure/observing raw IR, ownership, effects, SSA, complete phi/frames and cleanup. VM-27 closes supported hierarchy/finite/root obligations; VM-28/29 integrate and audit the complete opt-in dual path. | Individual-rule proofs cover every migrated variant with no substitute Rust-checker premise. Both checkers receive the same immutable artifact/request; either failure or disagreement rejects that path. Complete native/adversarial/platform checks and record remaining full-theorem/review obligations for S05. Preserve compatible Rust-only installation and APIs in 0.2.x. |
| **K3 / 0.5.0: Qleisli Soundness Theorem and production authority** | Prove the named theorem for the complete declared production IR profile, integrating K1/K2 results. Transfer acceptance to Lean after fresh serialized reconstruction; Rust becomes a producer/oracle. Prepare the community development foundation. | Complete [S05-C1–C5](release-milestones.md#qleisli-soundness-theorem-v050), including independent review, proof reproduction, full coverage and artifact binding. Package the audited kernel on supported platforms; validate failures, parity and capacity migration. No unproved Rust-checker premise or silent fallback. |
| **K4 / 0.6.0 onward, through v1: translations, realizability and resource preservation** | Validate Rust source lowering; implement correctness-critical backend lowering, optimization, gate-realization checking and emission in Lean with proofs about those actual definitions; retain external synthesis search behind the proved `LeafRealizer` checker. Derive CPTP semantics from soundness, construct its isometric dilation and synthesize it for the target profile. Retire duplicated Rust acceptance code through versioned migration, with broader contributors and reviewers. | Preserve S05-C1–C5 and complete [PR-C1–C4](release-milestones.md#physical-realizability-theorem-v1) and [RS-C1–C5](release-milestones.md#resource-safety-theorem-v1) by v1 alongside V1-C1–C5. Bind emitted artifacts to checked meanings and resource contracts under explicit cost models; distinguish exact synthesis, certified approximation and device assumptions. Retain reproducible audits, native compiler/runtime assumptions, diagnostics and migrations. |

K1 and K2 migrate the remaining existing finite acceptance surface during the
0.2.2–0.2.9 continuation; they do not postpone proofs required by an enabled
M2 rule. Full M2 integration must provide the executable checking and semantic
interpretation needed for its selected QFT/QPE schemas. A Rust-checked finite leaf must be
reconstructed from the same bound data by the explicit transitional boundary;
a serialized Rust success flag or handle cannot become Lean evidence. Any
remaining Rust leaf premise stays visible in the theorem and production trust
ledger until its checker is migrated. The first phase-word experiment has no
such cross-language leaf-import rule.

K0–K4 are a verification migration axis alongside algorithm milestones M0–M5.
Grover synthesis, Shor arithmetic, standard contracts and cost reporting retain
their original obligations. Moving a parser or simulator to Lean is not a v1
gate; proving the actual Lean backend's realizability is. Renaming an unproved
implementation a kernel satisfies neither theorem. The existing
2026-10-04 JST checkpoint evaluates readiness, not publication. The
[community transition](v0x-roadmap.md#community-development-from-v05) starts from
the v0.5 proof milestone; preparation begins during 0.4.x. It does not change
the existing Apache-2.0 license, algorithm gates or then-current 0.2.0 version.

The subsequent [typed layout component](lean-layout-slice.md) checks multi-owner
interfaces, structural types and exact axis maps, with proved finite permutation
and reference reindexing laws. [Shared typed calls](lean-layout-dag-slice.md) now
compose these layouts with checked input/output adapters and prove actual
acceptance against direct graph semantics. The [combined phase/layout
checker](lean-phase-layout-slice.md) adds sparse controlled dyadic phases to typed
shared calls, with normalization/remapping and actual cyclic-action proofs.
The [interference foundation](lean-interference-slice.md) proves local H
cancellation and diagonal normalization on arbitrary joint amplitudes, with
a complex instantiation. The [QFT circuit proof](lean-qft-proof-packet.md) now
derives the matched width-1–8 circuit's normalized Fourier coefficients and
reference extension, without runtime matrix enumeration. The [typed graph
projection](lean-qft-graph-packet.md) extends that theorem to actual cached
graph checking and literal operational coefficients. The [QPE component](lean-qpe-instrument-packet.md)
adds actual branch/reference equations and conditional completeness/trace preservation. External schema binding,
general non-diagonal graph acceptance,
transforms/encodings, complete instruments and production integration remain open.

## First executable slice

The first contract is deliberately small: **one-bit words of X and ideal
256th-root phase gates**. This provides a phase-sensitive foundation for the
selected dyadic-angle work without adding an unproved QFT/QPE schema or a
second production Rust M2 checker. This first word profile does not implement
Hadamard, multi-bit ports, controlled calls, repetition/DAG evidence, ownership
or measurement. The subsequent [CD-3 slice](lean-hierarchy-slice.md) adds shared
calls, sequences and closed powers under a separate experimental profile with
its own actual-checker theorem; full M2 integration remains pending.

For `0 ≤ k < 256`, `phase k` denotes the intended action
`|b⟩ ↦ exp(2π i k b / 256)|b⟩`. The implemented and proved semantics is a
**cyclic phase action**, `(bit, phase mod 256)`, rather than a Mathlib complex
matrix. A summary `(flip, phase0, phase1)` acts on an initial bit `b` and phase
`a` as `(b xor flip, (a + phase[b]) mod 256)`. Both phase entries are retained;
global phase is never quotiented away.

The normalizer uses a constant-size summary and visits each gate once. The
independently defined operational semantics executes gates directly. In
[PhaseWord.lean](../lean-kernel/QleisliKernel/PhaseWord.lean):

| Contract | Implementation/proof status | Adoption boundary |
| --- | --- | --- |
| Valid word and canonical summaries | `wordValid_iff`, `verify_conditions`, `normalize_valid` proved. At most 4096 gates; phases in 0..255. | Experimental `phase256-word-v1`; not a general circuit format. |
| Normalized meaning equals execution | `normalize_correct` proved for every word, bit and initial natural phase. | Cyclic phase semantics only; complex interpretation bridge pending. |
| Actual acceptance implies requested action | `verify_sound` proved for `verify word claimed expected`; both the computed claim and separate expected summary must match. | Does not prove transport parsing, native compilation, source adequacy or full quantum soundness. |
| Native transport and Rust launch | Bounded parser/process adapter with independent positive, mutation and failure tests. | No `VerifiedProgram`, QIRF receipt or standard-library API is issued. |

`phase 16; phase 16` must match T (`phase1 = 32`). The well-typed word
`x; phase 16; x; phase 16` has summary `(false,16,16)` and **must reject** an
identity request `(false,0,0)`. The latter is the semantic counterexample to
discarding global phase, even though isolated measurement cannot distinguish
it. These examples, the original current-source equivalent and actual initial
diagnostics are retained in the [development record](../tests/fixtures/lean_kernel/README.md).

### Experimental wire contract

This is a separate, versioned experiment, **not QIRF1/QIRF2 or the planned
hierarchical wire format**. The native executable takes exactly two file paths,
an artifact `.qpk` and an independent requirement `.qpr`:

```text
qleisli.phase-word 1 phase256-word-v1
Bit->Bit
claim 0 0 32
2
phase 16
phase 16
```

```text
qleisli.phase-word 1 phase256-word-v1
Bit->Bit
expect 0 0 32
```

The artifact header/interface, claim, gate count and each gate occupy one line;
the request has exactly three lines. Fields are separated by one ASCII space.
Every line, including the last, ends in LF. The alphabet is printable ASCII
plus LF: CRLF, bare CR, tabs, NUL, BOM and non-ASCII text reject. Canonical
decimal integers have no sign, leading zero (except `0` itself), decimal point
or exponent. The flip is 0 or 1, phases 0..255 and count 0..4096. The count
must match all following gates, including zero; each gate is `x` or `phase k`.
Unknown fields, versions, profiles, types, instructions or extra lines reject.

Each input is limited to 65536 bytes, read with at most one extra byte before
UTF-8 decoding. Numeric tokens longer than four digits reject before integer
conversion. The pure function additionally checks the gate and summary bounds;
the totality of the pure function is separate from bounded file I/O latency.

The process emits one canonical JSON line, in this field order:

```json
{"format":"qleisli.kernel-result","version":1,"profile":"phase256-word-v1","accepted":true,"code":"accepted","stage":"verification"}
```

Exit 0 means accepted. Exit 1 uses `accepted:false` and `code` equal to
`rejected` (meaning mismatch), `syntax`, `limit` or `io`; the stage is
`artifact`, `requirement` or `verification` as applicable. Out-of-range numbers
use `limit`, while malformed spellings use `syntax`. Wrong argument count is
exit 2, `code:usage`, `stage:usage`. The Rust example requires the expected
exit/result agreement and canonical envelope, caps output and waits at most
five seconds for the kernel child. Missing binaries and malformed results are
errors; it has no fallback verifier. This is an adapter for the locally built
kernel, not an OS sandbox for arbitrary executables or their descendants.

## Audit and remaining trust

The proof object is checked by Lean's kernel. Native execution also relies on
Lean elaboration/code generation, the C compiler, runtime, standard library,
OS I/O and the Rust adapter. The adapter/parser correspondence and the
complex-number interpretation are not proved by `verify_sound`. This follows
the distinction between [proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
and [elaboration/compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/).

[Audit.lean](../lean-kernel/Audit.lean) inspects compiled declarations by
origin module, including private and generated helpers. Project axioms,
unsafe/partial/noncomputable declarations, extern bindings and implementation substitutions
reject; the permitted transitive logical axioms are only `propext`,
`Classical.choice`, `Quot.sound`. A source policy also rejects proof holes,
native decision shortcuts, noncomputable executable code and forbidden imports.
The pure runtime import closure is checked separately from the audit's own Lean
metaprogramming dependencies. Standard runtime primitives are an explicit
remaining trust boundary, not newly proved project code.

The bundled `leanchecker` also replays the compiled `QleisliKernel` modules,
`Protocol` and `Main` through Lean's kernel, including the CD-3 composition,
DAG, hierarchy, typed layout/call and sparse phase/layout modules.
This detects certain elaboration/environment failures without trusting their
original elaboration run. It is not an independent implementation of Lean's
logic, a native compiler proof, or a sandbox for arbitrary Lean metaprograms.

The audit is itself tested with compiled negative fixtures. In this initial
work it caught compiler-generated partial recursion helpers behind ordinary
`def` declarations; the definitions were rewritten with standard recursors and
folds. A source keyword scan alone would not have caught that condition.
Tests and audit results are recorded in the [0.2.0 record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md).
No finite differential suite proves equivalence of the two implementations or
closes the full source-to-execution theorem.
