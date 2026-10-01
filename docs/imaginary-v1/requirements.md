# Shared language and contract requirements

Design requirements shared by the six [imaginary drafts](README.md), not adopted generic APIs. Existing bounded source/components have separate contracts and [status](../current-status.md).

## Requirement matrix

L=language, B=sealed built-in, D=ordinary-definition candidate; unresolved classifications need a decision. Host-only processing is not a current quantum API.

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

Local IDs preserve their algorithm-specific contracts and open obligations; shared rows do not replace them.

| Draft records | Shared requirements |
| --- | --- |
| [QPE-SIZE, ACCESS, AXIS, FOURIER, OBSERVE, DECODE](qpe.md) | R01–R05, R08, R12–R14 |
| [GR-1–GR-6](grover.md) | R01–R07, R13–R14 |
| [AE-1–AE-5](amplitude-estimation.md) | R02–R08, R12–R14, with R01/R04 inherited from QPE |
| [SHOR-MUL, POW, QPE, CLASSICAL, SAMPLE](shor.md) | R01–R06, R08–R09, R12–R14 |
| [WALK-1–WALK-5 and WALK-O1–O5](quantum-walk.md) | R01–R05, R07–R08, R10, R12, R14 |
| [QSVT-1–QSVT-6 and QSVT-O1–O5](qsvt.md) | R01–R08, R11–R14 |

## Intended acceptance and rejection examples

Future intended cases; current executable acceptance/rejection tests still cover the shipped profile.

| Requirements | Accept in a future specified profile | Reject or diagnose |
| --- | --- | --- |
| R01–R04 | Finite well-bounded sizes and distinct carried owners; apply/control/adjoint with matching capabilities | Aliased axes; a moved owner reused; hidden quantum capture; unchecked zero-iteration body; exceeding a capacity limit |
| R05–R07 | Fresh preparation; explicit measurement/discard; a phase-fixed reflection with exact private cleanup | Reversing a mere initializer; reflecting about an unknown owned state; substituting the opposite reflection sign under control; releasing approximately zero scratch |
| R08–R09 | Named angle/bit conventions, full-space arithmetic and justified error budgets | Implicit bit reversal; unsupported exact angle; noncoprime multiplication called unitary; only specifying a permutation on valid residues |
| R10–R11 | Coherent access implementation, specified subspaces and certified phase sequence | Treating a stochastic matrix as a unitary; ignoring off-block amplitude; arbitrary polynomial phases without an admissibility/synthesis argument |
| R12–R14 | Full measurement instrument, independently validated classical candidate, evidence bound to actual source/IR | Hiding failure outcomes; extracting a factor from an unverified period claim; reusing evidence after implementation modification; treating finite checks as compiler proof |

## Decisions still open and order of work

Before a feature is selected, specify English grammar/types/effects/ownership, IR, meanings/checker, limits/migration and independent acceptance/fault tests. M1 is fixed-width; M2 adds evidence-bound sharing/sizes; M3/M4 require efficient synthesis. Actual bounded implementation does not adopt all imaginary notation.

### R02 notation and representation alternatives

The two draft static-parameter syntaxes and operation-returning builders are alternatives, not interchangeable APIs. M1 uses checked static access constraints; wrapper/constraint/evidence-producer roles cannot infer control from unitarity. Controlled V W V† derives from V/inverse and controlled W with exact phase; [fixed-width tests](../../tests/operation_parameters.rs) cover that rule, not generic builders.

### Scaling prerequisite for R14

R14 requires symbolic compositional meanings and encodings without global dense matrices before size generalization. Current finite then/tensor/adjoint/control/extraction remain dense bounded reference paths. Shared typed derivations must bind actual implementations/dependencies/final IR, phase, axes and encodings; differing symbolic terms need checked equality evidence. A name/hash/simplifier cannot grant universal equality. Demonstrate independent bounded checking and interface/stale-evidence faults without full expansion.

### Complementary scaling gates: R02/R04 and R06/R09

R14 alone removes neither exponential basis tables nor expanded calls. R02/R04 need hierarchy/calls/folds jointly bound to evidence; R06/R09 need reversible circuit synthesis without whole-space truth tables. Cost/phase/full-space arithmetic/clean return remain separate scaling gates.

### First generalized QPE profile: decisions required by R08/R12/R14

Fix widths, phase angles/domain, exact or approximate realization, independent evidence, budgets/diagnostics and instrument/error conventions. Width four needs exp(i pi/8), outside R8. M2 selects bounded ideal exact dyadic phases; backend approximation is separate and cannot weaken exact scratch. [Hierarchy](../hierarchical-ir-spec.md) fixes its selected profile; this requirement adds no primitive or production authority.
