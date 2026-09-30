# Program-first development

Start from quantum programs as they should be written, then make the language
express and independently check them. The [design principle](design-philosophy.md#start-with-the-quantum-programs-we-want-to-write)
and [session procedure](../tests/fixtures/authoring_sessions/README.md) govern
this method. Ideal drafts are design inputs, not executable APIs. Use the three
frozen [corpus sources](../corpus/POLICY.md); retain original attempts and
semantic counterexamples.

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
   source with its historical result. Update the GitHub Issue or, for work
   without an Issue, the backlog; no duplicate backlog record is required.
   Update the authoring report, public contract ledger if relevant, and
   generated current status. Select a
   version by compatibility only when the concrete change is ready for release.

A cycle is done when its declared acceptance and rejection experiments pass
and its source/semantic/migration obligations are recorded. A failing semantic
oracle is an implementation or contract problem to investigate; it is never a
reason to suppress a branch, discard phase, weaken zero return, or bypass the
checker. A discovered current-contract defect reopens maintenance regardless
of the version in which the experiment was attempted.


## Work packets

| Packet | Contract and independent checking experiment | Current boundary |
| --- | --- | --- |
| CD-1: closed trials | X4/X5: fresh checked preparations, seed behavior, Bell/feed-forward distributions, zero attempts and explicit failure; never reuse one unknown state. | Finite sampling/trials implemented; [0.2.0 record](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.2.0.md). General Grover/Shor claims remain separate. |
| CD-2: portable finite checking | X2/X3: fresh-process QIRF1/2 checks against independent expected meaning; complete type trees/owners, wrong phase/body/dependency, cycles, depth and budget failures. | Finite interchange implemented; hashes or a serialized `verified` field never issue evidence. |
| CD-3: hierarchical composition | Bind shared calls/repeats, transformations, encodings and exact leaves to independent contracts; reject stale dependencies, invalid zero-repeat bodies and incomplete ports. Audit executable Lean acceptance proofs. | Bounded component proofs exist; complete production/profile binding and H1–H5 remain open. |
| CD-4: shared QPE | One source across declared widths and operations; controlled powers, phase/bit order, residual-target instrument, arbitrary references and exact cleanup. No global dense matrix above six-bit leaves or repeat expansion during checking. | Experimental [sized corpus](../corpus/sized/README.md) exists; production source/runtime integration remains open. |

The [current continuation](v0.2.2-plan.md#ordered-implementation-packets) contains
the remaining obligations and small-system validation scope. Advance source
experiments when they expose a concrete gap; production acceptance retains
R14/H1–H5 and G020-1 specification/compatibility gates. M3 predicate and M4
arithmetic construction require reversible synthesis, not full-space tables.
The six [imaginary programs](imaginary-v1/README.md) remain stress tests.

## Required completion evidence from 0.2.0

For each declared slice, supply saved source and diagnostics, its mathematical
contract, actual implementation/evidence binding, independent positive and
fault checks, cost/limit behavior, public migration review and executed commands.
The [acceptance criteria](release-milestones.md) determine the claim; compiler
success or a component theorem cannot close another layer's obligations.
Current Rust authority, disabled external schemas and the heavy-work pause remain
as stated in the current plan. General source adequacy and backend soundness
remain open.
