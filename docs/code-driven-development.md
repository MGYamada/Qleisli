# Code-driven development after the finite foundation

**User direction, 2026-09-28:** complete the finite B019 foundation in 0.1.x;
from 0.2.0 onward, practice the
[program-first method](design-philosophy.md#start-with-the-quantum-programs-we-want-to-write)
through concrete quantum programs and their checked contracts. This document
prepares that work. It does not select 0.2.0, adopt new syntax, or declare any
pending M1/M2 implementation complete. Current development remains 0.1.9.

## What the 0.1.x handoff must establish

All six [B019 conditions](v0x-roadmap.md#v019-acceptance-boundary) must have
recorded dispositions and reproducible evidence for the candidate being handed
over. In particular, close current supported-contract defects and audit findings;
do not move one to this future backlog merely to make B019 appear complete.
The [completion record](reviews/b019-completion.md), current release record and
generated [status](current-status.md) record whether that has actually happened.

The handoff must also leave a usable development baseline: preserved first
sources and diagnostics, independently checked finite examples and deliberate
semantic faults, phase/reference-sensitive oracles, pinned input provenance and
licenses, and the concrete future obstacles below. A fresh checkout must be able
to run the recorded checks without author-specific files or unrecorded evidence.

Completion is relative to the declared finite B019 contract. It does not assert
absence of all possible bugs, a general proof of the Rust compiler, scalable
checking, a hardware guarantee, or completion of v1. Those distinctions in the
[proof ledger](formal-core.md#4-theorem-status-and-proof-work) remain part of
the foundation. Requiring every future ergonomic feature before starting a
code-driven cycle would prevent the very experiments that select those features.

## Source and evidence already available

Use these artifacts together instead of copying hypothetical syntax into a
directory presented as working programs. The six drafts are Qleisli design
artifacts; external translated inputs remain restricted to the three sources
in the [adopted corpus policy](../corpus/POLICY.md). New local fixtures and
counterexamples are verification material, not an additional external corpus.

| Desired program | Current executable or failed source | Evidence and unresolved gap |
| --- | --- | --- |
| Shared [QPE](imaginary-v1/qpe.md), also used by [amplitude estimation](imaginary-v1/amplitude-estimation.md) and [Shor](imaginary-v1/shor.md) | [Bit-target phase2/phase3](../examples/operation_algorithms/estimation.qli), [four-bit target phase3](../examples/order_finding/estimation.qli), rejected [type parameter](../tests/fixtures/qli_authoring/rejected/basis_type_parameter.qli) and [static natural](../tests/fixtures/qli_authoring/rejected/static_nat.qli) | [Source semantic cases](../tests/qli_corpus.rs) and [iterative QPE](../tests/iterative_qpe.rs); A020-01–03/07. These are different finite bodies, not a shared sized implementation. |
| [Grover's preparation/oracle/reflection/retry structure](imaginary-v1/grover.md) | [Once/twice amplification](../examples/operation_algorithms/amplification.qli), [Katas Grover2](../corpus/quantum_katas/grover2/README.md) | Four marks, overshoot and signed-control cases in the source suite; A020-03/12/18/19. An exhaustive distribution is not a sampled trial. |
| Shor's reusable modular powers and shared QPE | [Finite arithmetic](../stdlib/src/arithmetic.qli), [order finding](../examples/order_finding/main.qli), [host example](../examples/shor15.rs) | [Arithmetic and host checks](../tests/order_finding.rs); A020-02/03/07/18/19. N=15 and a correct factor check do not establish general synthesis or retries. |
| Application layers with explicit parameters and observables | [PennyLane rotation](../corpus/pennylane_demos/qubit_rotation/README.md), [QAOA](../corpus/pennylane_demos/qaoa_vertex_cover/README.md), [VQE excitation](../corpus/pennylane_demos/vqe_excitation/README.md), [Qualtran reflection](../corpus/qualtran/reflection2/README.md) | [Independent finite corpus runner](../scripts/check_input_corpus.py), original [first checks](../corpus/authoring/check-initial.json); A020-07/14–16. Fixed angles and host aggregation are explicit restrictions. |
| [Quantum walk](imaginary-v1/quantum-walk.md) and [QSVT](imaginary-v1/qsvt.md) | Desired source and [mathematical counterexamples](../scripts/check_imaginary_v1_examples.py), without claimed compiled counterparts | R10–R12 and their local open questions. Use these as contract stress tests; they are not extra executable v1 gates or evidence of current block-encoding support. |

For example, the desired QPE interface in its draft is **unimplemented design
notation**:

```text
observe fn qpe<n,m>(static U: UnitaryOp<Bits<n>>,
                    target: Q<Bits<n>>) -> (CWord<m>, Q<Bits<n>>)
```

The current [source](../examples/operation_algorithms/estimation.qli) instead
has a fixed interface and explicit rounds:

```text
pub observe fn phase3[static U: Op<Bit>](q: Q<Bit>)
    -> ((CBit, CBit, CBit), Q<Bit>)
requires Controlled(U)

let (a, q) = controlled[U](h(init0()), q);
let (b, q) = controlled[repeat_op(2,U)](h(init0()), q);
let (c, q) = controlled[repeat_op(4,U)](h(init0()), q);
```

This excerpt is not a standalone project; the linked file supplies its body
and imports. The removed obligation must eventually be “write and verify one
algorithm body across supported interfaces and precisions”, not merely
“replace three lines with a loop”. The target's conditional quantum state and
every reference correlation remain part of QPE's instrument contract.

## Obstacles to record before selecting 0.2.0 work

The [backlog](v0.2.0-backlog.md) retains stable IDs, individual reproducers and
acceptance experiments. This table identifies which gaps actually block which
claims. An entry is not a blanket prerequisite for starting another cycle.

| Obstacle and author burden | Required boundary and experiment | Dependency / compatibility decision |
| --- | --- | --- |
| A020-01/05: manually rebuild product trees and remember same-typed result roles | Preserve full trees, Unit ownership, ordered axes and reference correlations; compare the same QFT/teleportation clients and deliberate bit swaps. Role names alone cannot prove an algorithm. | Layout investigation can begin now. Changing the current left-fold meaning or public AST requires MINOR; explicit additive adapters may be PATCH. |
| A020-02/03: duplicate bodies across target types, precision and iteration count | Source substitution must bind complete interfaces, dependencies, effects and capabilities; check zero-sized/zero-repeat boundaries and excessive work. | R14 and joint hierarchy are prerequisites for size generalization. A finite-template exception remains an unadopted scheduling alternative. G020-1 is required before source implementation. |
| A020-07: four-bit QPE needs a controlled π/8 phase outside the finite exact gate profile | Bind the selected ideal dyadic semantics to actual hierarchical circuits and checked QFT/QPE schemas; reject unsupported angles and compare branch instruments. | M2 H1–H5 and pinned Lean schema obligations. Raising a finite limit or using floating tolerance cannot supply this evidence. Public IR migration is reviewed separately. |
| A020-09/17: a provider's label or serialized claim cannot replace independently checked access/evidence | Retain the current transparent constructor closure; mutate phase, type, dependencies and requested meaning in a fresh process. Opaque access needs its own contract. | M1 X2–X3 are specified but unimplemented. Tightening current access acceptance is MINOR; additive interchange need not change existing APIs. |
| A020-18: host authors have distributions but no supported actual-sample/retry API | Execute fresh trials, return typed success/retry/error and account for all attempts; check Bell marginals, feedback, injected RNG errors and exhaustion. | M1 X4–X5 can precede M2. Additive APIs/commands may be PATCH; keep existing exhaustive `run` behavior. |
| A020-20: generated projects can exhaust input I/O/tokenization before core work limits apply | Bound automation jobs externally now; implement the specified byte loader with boundary/UTF-8/many-file/overflow tests and preserve the explicit legacy path. | X6's newly rejecting default is MINOR. Its absence is a documented current capacity policy, not a new finite B019 defect; it blocks treating the current CLI as a resource-isolated unattended service. |
| A020-19: predicates/arithmetic are finite tables instead of reusable circuit constructions | Check reversible Boolean DAGs and arithmetic stages with exact scratch return, full-space action and actual-circuit binding; report construction/checking growth. | R06/R09, M3/M4 after M2. A general-sized program cannot be accepted on a finite truth table or cached matrix alone. |
| A020-16: specialize application parameters and assemble observable/optimizer handling on the host | Separate ideal expectation, sampled estimates, approximation bounds and classical convergence; check angle/parameter/bit-order binding with analytic small cases. | A020-07 and the selected host interface. Continuous parameters, gradient rules and new error contracts need their own specifications. |
| A020-04/06/11/12/14/15: wrappers, imports, restricted bodies and one-error repair loops | Prefer ordinary definitions or untrusted desugaring to existing rules; replay real failed sources plus access, phase, ownership, cleanup and work-limit negatives. | Ergonomic opportunities, not evidence-gate replacements. Additive behavior can be PATCH; review names, AST and existing special-form semantics individually. |
| A020-08/13: evaluation and presentation can hide what actually improved | Preserve first attempts and raw distributions, distinguish informed/curated work from a controlled model study, and retain genuine low-probability branches. | Applies to reporting every cycle. Display changes are optional and never affect exact evidence or raw-result compatibility. |

The source-retention defect A020-10 belongs to the finite B019 disposition,
not a reason to defer completion of the 0.1.x foundation. Its historical
reproducer and the implemented resolution remain linked from its backlog entry.
The separate X6 loader policy is a future capacity/migration change; solving
repeated snapshot retention does not silently impose that new source-size cap.
Before unattended authoring runs, the driver must have explicit per-job time,
memory, input/output and filesystem boundaries and retain a distinct resource
failure result. Such driver limits do not change what the language claims to
accept; they must be disclosed as limits of that experiment. Never treat a
lowering-work budget as a bound on initial file reading or tokenization.

## A repeatable development cycle

Each cycle produces one reviewable change with the following artifacts. Reuse
the existing [authoring session procedure](../tests/fixtures/authoring_sessions/README.md)
and corpus manifest; do not start another competing evidence/status system.

1. **Save the desired program and the first current-language attempt.** Name
   the task, baseline commit, available context and intended author obligation
   to remove. Label imaginary source as unimplemented. Save and hash a new
   attempt before checking it; append actual diagnostics and revisions. If
   reusing an old failure, label it a curated replay, not a new authoring result.
2. **Fix the mathematical contract before shortening the code.** Record types,
   complete owners, effects, phase/axis conventions, entry and cleanup premises,
   output instrument or pure equation, supported bounds and expected failures.
   Choose an independent oracle and a type-correct wrong program that it rejects.
3. **Select the smallest justified change.** Identify whether it is an ordinary
   definition, a language form, or a necessary new sealed meaning/evidence rule.
   Prefer existing-core desugaring for convenience. Update the extension
   specification and compatibility decision before implementing new semantics;
   obtain a separate scope decision for an unresolved design alternative.
4. **Implement and independently check.** Submit generated IR/evidence to the
   same verifier regardless of author. Check claimed meaning against the actual
   body, dependency identity, full interface and fixed requested contract.
   Verifier-valid IR alone does not prove preservation of the source meaning.
5. **Replay positives and counterexamples.** Use the same pre-change clients
   where compatible, plus a held-out composition. Exercise phase under control,
   entangled references, false cleanup, stale evidence and limits as applicable.
   Compare removed author obligations, repair rounds and generation/checking
   costs; a line-count reduction or passing compiler is insufficient.
6. **Record the result and stop at the scoped claim.** Link implementation,
   tests, actual commands and remaining assumptions; retain the old failed
   source with its historical result. Update the backlog, authoring report,
   public contract ledger if relevant, and generated current status. Select a
   version by compatibility only when the concrete change is ready for release.

A cycle is done when its declared acceptance and rejection experiments pass
and its source/semantic/migration obligations are recorded. A failing semantic
oracle is an implementation or contract problem to investigate; it is never a
reason to suppress a branch, discard phase, weaken zero return, or bypass the
checker. A discovered current-contract defect reopens maintenance regardless
of the version in which the experiment was attempted.

## Bounded first cycles for the remaining M1 and M2 work

These are prepared work packets, in dependency order, not claims of implemented
features or a promise that all ship in 0.2.0. The maintainer selects a packet and
its compatibility impact; assign an implementer when execution starts. The
first two M1 packets are independent and may proceed concurrently.

| Packet | First retained program and smallest deliverable | Acceptance experiment / completion boundary |
| --- | --- | --- |
| CD-1: one real closed trial | Preserve [Katas Grover2](../corpus/quantum_katas/grover2/main.qli) unchanged. Implement the specified X4 sampler and X5 typed host trial boundary; a host client samples a fresh checked trial and validates the marked bits. Use the [Shor15 host](../examples/shor15.rs) as the next composition, without rewriting its exhaustive reference example. | Follow all X4/X5 adversarial and statistical gates, including non-deterministic Bell/feedback tests, seed words, no partial result on failure, zero attempts and no state reuse. Grover's deterministic `11` result alone is insufficient. Do not claim general Grover or Shor from this host slice. |
| CD-2: external independent finite checking | Reuse existing [function-contract](../tests/function_contracts.rs) and [meaning-evidence](../tests/meaning_evidence.rs) clients. Implement QIRF1, then its specified QIRF2 extension, with the current finite verifier behind the untrusted decoder. | X2/X3: all variants round-trip, fresh-process checking without source/cache, independently supplied expected meaning, type-tree/Unit mismatches, wrong phase/body/dependency, cycles, deep input and budget failures. A JSON `verified` field or source hash never authorizes evidence. |
| CD-3: evidence-bound hierarchical composition | Start from the existing fixed-width QPE building blocks and [bounded research kernel](../research/semantic-kernel/README.md). Implement the selected successor IR/checker path first, retaining the finite adapter and its exact leaves. | H1/H2/H5 component gates: independently bind shared calls/repeats/transformations to meanings and encodings; check invalid zero-repeat bodies, stale dependencies and complete ports. Establish required Lean schema statements and audits. A prototype pass is not production integration or complete H1–H5. |
| CD-4: shared QPE across declared widths | After the hierarchy prerequisite is established, complete the sized-source G020-1 specification, then implement one QPE/QFT source with its declared type/size and angle profile. The existing [QPE draft](imaginary-v1/qpe.md) guides source shape without predetermining final notation. | Complete H1–H5, including H3 instances `(n,m)=(1,3),(2,4),(8,8)`, H4 reference-sensitive instruments and π/8 cases, no dense matrices above six-bit leaves and no expansion of shared repeats during checking. Preserve old finite clients and document public migrations. Only then claim this M2 profile. |

CD-3 does not authorize premature sized source: its first deliverable is the
specified verification architecture with concrete bounded interfaces. The
hierarchy and source layers are developed in stages but neither can be declared
complete by demonstrating the other alone. CD-4's larger case is a generation/
checking experiment under the selected profile, not a demand to run an
exponentially sized exhaustive simulator or a proof for all natural sizes.

M3 predicate synthesis and M4 arithmetic then use A020-19's construction
experiments, with M1 trials for the host boundary. The six ideal drafts remain
active design inputs throughout; correcting a draft after a counterexample is
progress, provided the old assumption and its resolution are retained.

## Readiness decision and check entry points

The transition is ready when B019 is closed for the recorded candidate, this
source/evidence map remains valid, and the selected first packet has its
current contract, bounded oracle and negative experiments. Pending M2–M5,
optional ergonomics, controlled model benchmarking and general compiler proofs
are reported honestly; they do not prohibit CD-1/CD-2.

Existing entry points for the baseline are:

```sh
cargo test --test qli_corpus --test iterative_qpe --test input_corpus
python3 scripts/check_authoring_sessions.py
python3 scripts/check_input_corpus.py
python3 scripts/check_imaginary_v1_examples.py
python3 scripts/check_docs.py
```

For exhaustive finite translation semantics, build the CLI and run
`python3 scripts/check_input_corpus.py <path-to-built-qleisli> --exhaustive`.
These checks have distinct scopes: session/corpus metadata checks protect
records and attribution, mathematical draft checks do not execute imaginary
source, and finite numerical comparison does not issue exact semantic certificates.
Record actual executed commands and results in the selected cycle's record;
the command list here is an entry point, not a new validation claim.
