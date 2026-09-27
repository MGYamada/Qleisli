# Shared language and contract requirements

Status: **requirements extracted for imaginary design; no feature adoption**
(2026-09-27). Read the [corpus](README.md) and
[English specification framework](../language-evolution.md). Every facility
below is missing in its general form even where fixed finite operations exist.
The current [stdlib ledger](../stdlib-contracts.md) remains the record of the
12 shipped ordinary definitions; these proposals are not new ledger entries.

## Requirement matrix

L = proposed language form; B = proposed sealed built-in operation;
D = proposed ordinary definition. A mixed or unresolved classification records
a design decision still to make, not permission to bypass the verifier.
Host-only processing is explicitly outside current `.qli`.

| ID | Required facility and consumers | Proposed classification | Input/output, ownership and effects | Meaning and evidence / intended IR route |
| --- | --- | --- | --- | --- |
| R01 | Finite static sizes and register basis, all six drafts | L | `Bits<n>` and linear `Q<Bits<n>>`; static natural n, with zero width still owned; proposed classical words separately copyable | Ordered axis layouts, full type trees and capacity diagnostics; elaboration to finite register interfaces. General shape/size proof rules are open. |
| R02 | Static operation parameters and application, all six | L; exact representation unresolved | `UnitaryOp<A>` captures no live quantum owners; application consumes and returns `Q<A>` | Contract-bound bodies or certified access descriptions. Preserve actual implementation identity, phase, signatures and dependencies through final IR; an arbitrary matrix is not a gate primitive. |
| R03 | Adjoint, coherent control, powers, QPE/Grover/AE/Shor/walk/QSVT | L transformations; efficient power providers D or certified external capability, unresolved | Input/output owners stay complete; controlled application returns distinct control and target. Only eligible pure operations | Preserve phase and axes; derived repetition counts every use. Opaque apply access does not imply controlled access. Reject measurement or unsupported transformations rather than replacing meaning. |
| R04 | Ownership-preserving static folds and register access, all six | L fold; D helpers over a specified L structural interface | Same carried owner interface on each iteration, including zero-iteration validation; whole-register helpers return all untouched axes | Partition/reassembly and nonaliasing evidence independently checked in IR. Borrow syntax and shared-call IR are unselected; lexical lifetime alone proves no cleanup. |
| R05 | Fresh zero preparation, arbitrary-basis preparation, register measurement/discard, all six | D over current B where derivable; additional B require separate adoption | Preparation `Iso`, unitary extension separately supplied; measurement/discard `Observe` consumes owners | Full instrument with arbitrary references; retain every outcome and returned owner. Future whole-register APIs must derive their layout and primitive meanings. |
| R06 | General reversible predicate evaluation and exact private cleanup, Grover/AE/Shor | D with L evidence boundary; evidence rules unresolved | Total typed basis function, owned data and scratch, pure compute/use/uncompute returning data | Generalize `U E_in = E_out u`, exact zero return for all valid inputs and references; no truth-table enumeration as an efficient general construction. Retain physical body and checked bindings in IR. |
| R07 | Exact reflection and projector-phase operations, Grover/AE/walk/QSVT | D when derived from access; new B unresolved | Unitary descriptions consume and return the same register; a projector does not itself grant access to its reflection | Fix `2Π-I` versus `I-2Π`, and `exp(iφ(2Π-I))` conventions locally; require preparation/inverse or certified synthesis. Final evidence must retain the exact implemented phase. |
| R08 | QFT, rotations, real parameters and approximation, QPE/AE/Shor/QSVT | D circuits; angle representation and primitive basis unresolved | Same owned register; static precision/angle inputs; no observation inside a unitary transform | Phase/bit-order-fixed target, error metric, synthesis budget and composition. Approximate target agreement is separate from exact scratch cleanup. Current exact arithmetic is not silently extended to arbitrary angles. |
| R09 | General reversible modular arithmetic, Shor | D; integer/size support L | Whole-space permutation for valid coprime modulus/multiplier, scratch returned exactly zero | Specify action outside valid residues, inverse and efficient construction. Check modular-power identity, phase and reference extension; general arithmetic certificates and scalable construction remain open. |
| R10 | Coherent transition preparation and subspace access, walk | D or certified input capability, classification unresolved | A chosen unitary extension on all register labels and its inverse, preserving every owner | Row normalization and model promises do not provide a free state-preparation oracle. Reflections derive from the supplied extension; padded states and costs are explicit. |
| R11 | Projected-unitary/block-encoding and phase-sequence certificates, QSVT | Additional contract/evidence rules; L/B/D boundary unresolved | Full physical unitary and explicit input/output projectors; retain the whole output until observation or certified cleanup | Specify normalization, parity, polynomial bounds, phase synthesis and error. Success block is a contraction inside a unitary; do not authorize pure release or deterministic application of that block. |
| R12 | Instruments, accuracy and classical probability interpretation, QPE/AE/walk/QSVT | Contract rules; D postprocessing or host-only | Conditional residual quantum state plus classical outcome, with CP maps summing to TP | Error metric/statistical assumptions and all failure branches. Proposed generalized instrument evidence does not follow from the existing pure-equality checker. |
| R13 | Actual sampling, classical validation and bounded retries, Grover/AE/Shor | Host-only orchestration; boundary API unresolved | Fresh preparation per trial, classical results only when a trial is closed, explicit error/exhaustion | Do not inspect a simulator distribution in place of a sample. Verify candidates before reporting success; count quantum calls, classical work and rejected attempts. |
| R14 | Reusable implementation evidence and substitution, all six | Generalization of existing L contract boundary and independent verifier | Preserve type, phase, complete owner interface, entry premises and output layout | Source/dependency binding, transformations and final IR must share a fixed meaning contract. Current finite SC/FC checks are a foundation, not a proof for arbitrary n or new contract families. |

## Intended acceptance and rejection boundaries

Local draft records map to this index as follows. Follow each link for the
algorithm-specific type, equation, acceptance/rejection cases and unresolved
items; the shared rows do not replace those details.

| Draft records | Shared requirements |
| --- | --- |
| [QPE-SIZE, ACCESS, AXIS, FOURIER, OBSERVE, DECODE](qpe.md) | R01–R05, R08, R12–R14 |
| [GR-1–GR-6](grover.md) | R01–R07, R13–R14 |
| [AE-1–AE-5](amplitude-estimation.md) | R02–R08, R12–R14, with R01/R04 inherited from QPE |
| [SHOR-MUL, POW, QPE, CLASSICAL, SAMPLE](shor.md) | R01–R06, R08–R09, R12–R14 |
| [WALK-1–WALK-5 and WALK-O1–O5](quantum-walk.md) | R01–R05, R07–R08, R10, R12, R14 |
| [QSVT-1–QSVT-6 and QSVT-O1–O5](qsvt.md) | R01–R08, R11–R14 |

## Intended acceptance and rejection examples

| Requirements | Accept in a future specified profile | Reject or diagnose |
| --- | --- | --- |
| R01–R04 | Finite well-bounded sizes and distinct carried owners; apply/control/adjoint with matching capabilities | Aliased axes; a moved owner reused; hidden quantum capture; unchecked zero-iteration body; exceeding a capacity limit |
| R05–R07 | Fresh preparation; explicit measurement/discard; a phase-fixed reflection with exact private cleanup | Reversing a mere initializer; reflecting about an unknown owned state; substituting the opposite reflection sign under control; releasing approximately zero scratch |
| R08–R09 | Named angle/bit conventions, full-space arithmetic and justified error budgets | Implicit bit reversal; unsupported exact angle; noncoprime multiplication called unitary; only specifying a permutation on valid residues |
| R10–R11 | Coherent access implementation, specified subspaces and certified phase sequence | Treating a stochastic matrix as a unitary; ignoring off-block amplitude; arbitrary polynomial phases without an admissibility/synthesis argument |
| R12–R14 | Full measurement instrument, independently validated classical candidate, evidence bound to actual source/IR | Hiding failure outcomes; extracting a factor from an unverified period claim; reusing evidence after implementation modification; treating finite checks as compiler proof |

These are future design cases. The current parser is not expected to accept
the imaginary fragments. The existing executable acceptance/rejection suite
continues to test the shipped finite profile.

## Decisions still open and order of work

The first candidate specification slice is **static sizes plus static operation
parameters and their finite evidence-preserving elaboration** (R01–R04, R14).
This is a proposal for review, not a finalized 0.2.0 feature set. QPE additionally
forces a decision about Fourier angles and accuracy (R08, R12); Grover about
general predicate synthesis (R06); Shor about efficient arithmetic and host
execution (R09, R13). Walk and QSVT expose broader access and subspace contracts
(R10–R11) that need not all ship in 0.2.0 or v1.

The subsequent [v0.x plan](../v0x-roadmap.md) prioritizes operation capabilities
and permits narrowing this combined candidate before specification. Through
v0.1.9, these are decision-dossier tasks, not new production features. The
symbolic prerequisite below still applies, and the kernel's separate deferral
is not lifted by assigning conditional themes to later minor releases.

Before implementing a selected feature, write its English inference/grammar
rules, actual IR representation, checker algorithm and soundness premises,
bounded examples and counterexamples, capacity policy, and migration impact.
Then validate reuse across multiple supported sizes and operations. Do not
raise limits or adopt shared-call IR as a patch merely to make a draft compile.

Outstanding cross-cutting decisions include exact versus approximate angle
representations, scalable independent evidence checking, treatment of classical
data in quantum signatures, host sampling errors and retry budgets, and the
formal connection from generalized elaboration to IR. None is resolved by
writing a type name or requiring an unimplemented certificate.

### Scaling prerequisite for R14

Clarified by the v0.1.2 review and adopted as a design constraint on
2026-09-27: **generalized contract composition must not require materializing
or multiplying the whole logical operator's dense matrix.** This is an
architectural prerequisite for size generalization, not a later performance
optimization. A dense operator on n bits has `4^n` entries; the current
straightforward square-matrix product takes `O(8^n)` scalar operations.
Merely adding `Bits<n>`, increasing a capacity, or caching checked physical
circuits does not remove that representation cost.

The current bounded checker already has soundness arguments for composition
and implemented constructors. However, `CheckedContract::then` computes the
logical matrix product; tensor, adjoint and control also construct dense
logical matrices, and encodings are matrices. This finite profile remains
supported in 0.1.3. See the [review verification](../reviews/v0.1.2.md).
The `apply_contract` function-evidence checker also constructs and compares
whole implementation/specification matrices; its acceptance path must be
generalized along with composition.

A candidate architecture retains typed symbolic meanings and shared proof
derivations, with nodes such as composition, tensor, adjoint, control and
static repetition. These names are design metanotation, not accepted syntax
or APIs. It must also represent encodings and their equality without expanding
whole-space matrices. Acceptance of a composition checks its component
evidence and matching intermediate types, encodings, phase conventions and
axis layouts, and retains binding to the actual implementation and final IR.
Different symbolic terms require a checked equivalence derivation when they
are not definitionally equal; a descriptive name or hash alone is not evidence.

Keep dense exact comparison for explicitly bounded leaves and finite
regressions. Size-dependent arithmetic and circuit families need separately
checked parameterized derivations, for example induction and algebraic
identities, rather than whole-basis enumeration. Lean may supply such proofs;
a dedicated evidence calculus is also possible. The proof/import boundary
and implementation correspondence must be specified whichever method is used.
General symbolic equality is not assumed decidable by simplification alone.

Before claiming scalable composition, record the symbolic meaning and encoding
representation, allowed inference rules and their premises, proof sharing,
independent checking algorithm and budgets, and final-IR binding. Demonstrate
that composition in the selected profile checks the derivation without
expanding a global dense matrix, including negative cases for wrong interfaces
and stale evidence. This does not promise efficient checking of every possible
equivalence or polynomial circuit size for every algorithm. Production
integration and parameterized algorithm generalization remain unimplemented.

The subsequent v0.1.3 [system design](../symbolic-contract-architecture.md) and
[independent prototype](../../research/semantic-kernel/README.md) begin this
work in an explicitly limited research profile. Their implemented subset does
not constitute generalized source support or discharge R14 for the six drafts.

### First generalized QPE profile: decisions required by R08/R12/R14

The selected specification must state supported phase/target widths, the
required Fourier-angle set, exact or approximate synthesis, the independent
evidence method, its capacity diagnostics, and any error metric and composition
budget. In the displayed QFT circuit, a four-bit phase register requires
`2*pi/16 = pi/8`, with phase `exp(i*pi/8)`. This lies outside the current
exact coefficient ring `Z[zeta_8,1/2]`; the width-four Python convention check
uses floating-point arithmetic and does not implement exact QFT4 in Qleisli.

Extending exact phase arithmetic and approximating the target using an
available gate set lead to different evidence obligations. Select and document
the approach before claiming generalized QPE support. Approximate operator
accuracy and sampling failure remain separate from exact auxiliary zero
return. This review records the required decision; it selects neither angle
representation nor a new primitive or error API in 0.1.3.
