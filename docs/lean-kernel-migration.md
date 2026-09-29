# Rust frontend and Lean 4 verification kernel

Status: **staged migration adopted; experimental phase-word, phase-DAG, typed-layout, typed-call and combined phase/layout
slices implemented; production verification remains in Rust**. The user selected this
direction during 2026-09-28–29 JST. The product version is 0.2.0; publication evidence
is recorded separately in the [release record](releases/v0.2.0.md). The [0.2.0 foundation scope](v0.2.0-plan.md) retains
the implemented components; the [0.2.1 continuation](v0.2.1-plan.md) carries the
remaining production hierarchy and common-QPE work, with M0–M5 and H1–H5 intact.
The 2026-09-29 refinement makes proof of the
[Qleisli Soundness Theorem](release-milestones.md#qleisli-soundness-theorem-v050)
the central v0.5.0 milestone, with broader community development from v0.5 onward.
The subsequent 2026-09-29 decision adds the
[Physical Realizability Theorem](release-milestones.md#physical-realizability-theorem-v1)
and substantive Lean backend implementation/proofs as requirements by v1.

## Architecture and authority

During K0–K3, Rust retains source parsing, diagnostics, CLI/JSON, interop,
simulation and untrusted generation of IR and evidence. The acceptance core
moves in bounded steps to Lean 4: exact arithmetic, semantic evidence checking, then raw IR
ownership/effect verification. New production M2 kernel work starts in Lean;
the Rust [research kernel](../research/semantic-kernel/README.md) remains an
experiment and an independent differential oracle.

The longer-term direction is to migrate the implementation beyond the frontend
to Lean, beginning with the backend transformations needed for realizability.
Rust frontend output remains untrusted and needs source-to-IR translation
validation for source-level guarantees. Migrating the backend is a project
prerequisite for the intended end-to-end Lean guarantee, not a claim that
using Lean alone proves correctness. Auxiliary CLI/interop/simulator migration
can continue beyond v1; the v1 gate is the actual supported synthesis and
emission path with its correspondence proofs.

The separate [QLT plan](qlt-design.md) deliberately starts its experimental
mathematical test evaluator in Rust during 0.3–0.4, then migrates evaluation and
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

The future [Lean-assisted debugger](lean-debugger-plan.md) uses this checking
boundary to report mathematical obligations and independently replayable
mismatch witnesses, with later K4 source/backend tracing. The presentation and
repair layer remains untrusted. Its witness-checking correctness is a separate
obligation; rejection by the acceptance checker does not itself refute the
requested mathematical claim. This tooling adds no K0–K4 release gate.

## Staged migration

These are intended integration boundaries, not deadlines. Compatible work can
ship as PATCH under [versioning](versioning.md); a stage number does not itself
justify a MINOR. Public acceptance/capacity/format or authority changes get an
explicit compatibility and migration review.

| Stage and intended boundary | Implementation | Gate before advancing |
| --- | --- | --- |
| **K0 / 0.2.x: establish the executable boundary** | 0.2.0 ships the separate Mathlib-free package, actual checker component theorems, bounded experimental protocols, Rust launcher, compiled audits and independent tests. Complete the production M2 hierarchy/schema checker in the 0.2.1 continuation. | The shipped components are reproducible without Mathlib. Every later M2 rule remains disabled until its theorem, binding tests and H1–H5 obligations are satisfied. Common QPE/QFT and sized source move to 0.2.1; their public API must remain compatible or select the next MINOR. Shipping 0.2.0 alone does not close full K0/M2. |
| **K1 / 0.3.0: exact meanings and contracts** | Canonical exact scalars, bounded matrices/leaves, contract equations and evidence reconstruction; separate complex interpretation proofs over the same definitions. | Canonical equality and operations agree with the mathematical interpretation; phase and type/axis/source mutations reject. Differential agreement with Rust includes overflow/capacity boundaries. Arbitrary-precision integers still have explicit bit/work limits. |
| **K2 / 0.4.0: complete raw IR checking** | Ownership, effects, SSA, complete phi/frame coverage, zero-width owners, cleanup and portable finite/hierarchical evidence. Use the existing Resource/Phi models as specifications. | Resource/effect and individual-rule proofs cover all implemented variants; keep an explicit ledger of remaining composition/interpretation obligations for the v0.5.0 theorem. Two checkers run on the same immutable artifact and request; disagreement or either failure rejects. Native cost and adversarial corpus gates pass. |
| **K3 / 0.5.0: Qleisli Soundness Theorem and production authority** | Prove the named theorem for the complete declared production IR profile, integrating K1/K2 results. Transfer acceptance to Lean after fresh serialized reconstruction; Rust becomes a producer/oracle. Prepare the community development foundation. | Complete [S05-C1–C5](release-milestones.md#qleisli-soundness-theorem-v050), including independent review, proof reproduction, full coverage and artifact binding. Package the audited kernel on supported platforms; validate failures, parity and capacity migration. No unproved Rust-checker premise or silent fallback. |
| **K4 / 0.6.0 onward, through v1: translations and physical realizability** | Validate Rust source lowering; implement backend lowering, optimization, gate synthesis and emission in Lean with proofs about those actual definitions. Derive CPTP semantics from soundness, construct its isometric dilation and synthesize it for the target profile. Retire duplicated Rust acceptance code through versioned migration, with broader contributors and reviewers. | Preserve S05-C1–C5 and complete [PR-C1–C4](release-milestones.md#physical-realizability-theorem-v1) by v1 alongside V1-C1–C5. Bind emitted artifacts to the checked meaning; distinguish exact synthesis, certified approximation and device assumptions. Retain reproducible audits, native compiler/runtime assumptions, diagnostics and migrations. |

K1 and K2 migrate the remaining existing finite acceptance surface; they do
not postpone proofs required by an M2 rule enabled in the 0.2.1 continuation.
K0's full M2 work must already provide the executable checking and semantic interpretation
needed for its selected QFT/QPE schemas. A Rust-checked finite leaf must be
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
the existing Apache-2.0 license, algorithm gates or current 0.2.0 version.

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
Tests and audit results are recorded in the [0.2.0 record](releases/v0.2.0.md).
No finite differential suite proves equivalence of the two implementations or
closes the full source-to-execution theorem.
