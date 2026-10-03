# First executable Lean kernel development record

This is informed, curated development on 2026-09-28–29 JST, not a controlled
LLM authoring benchmark, an external input corpus source, or an algorithm proof.
The migration contract
fixes the experimental wire format and limits of its theorem.

The [first source](first_source/main.qli) uses the existing T gate as the
executable target for two ideal π/8 phases. Current `.qli` syntax still cannot
express the general dyadic gate or common sized QPE. The source is deliberately
kept unchanged: this packet removes the need to trust a proposed phase-word
summary, not source boilerplate or hand wiring. It introduces no `.qli` form or
standard-library definition.

[baseline.json](baseline.json) preserves source hashes and actual observations
before a native Lean kernel existed: the current source checked successfully,
and invoking the desired checker failed because the executable did not exist.
[after.json](after.json) retains the actual native acceptance of
[phase_pair.qpk](phase_pair.qpk) against [t_expected.qpr](t_expected.qpr), the
rejection of [global_phase.qpk](global_phase.qpk) against
[identity.qpr](identity.qpr), and the unchanged source check. Both words are
valid one-bit programs. Only their independently requested meaning differs.

The [first proof source](first_proof_attempt.lean.txt) and
[real first diagnostics](first_proof_diagnostics.txt) preserve an unsuccessful
Lean proof attempt before the final associativity repair. They are inert text,
not imported modules. A later compiled audit found generated partial helpers
behind total source `def` declarations. Direct execution was rewritten using
the standard structural fold, and file reading uses an explicit structural
recursor; the audit rule was retained. That implementation repair does not
change the four original wire fixtures or the `.qli` source.

A separate [clean-build record](clean-build-record.json) identifies source hashes,
toolchain, commands, audit scope and the temporary native executable. It uses
no previous `.lake` artifacts or external packages and does not claim a whole
Git release/distribution check.

The [native differential experiment](../../../examples/lean_kernel.rs) is
the held-out use: exhaustive short words over X/I/T/T-adjoint are checked
against the existing Rust exact matrix evaluator, then all 256 dyadic scalar
phases are checked against independent basis trajectories. Claim, circuit and
independent request mutations, syntax/capacity failures and missing/malformed
kernel results must reject. The tests do not assert that the source compiler
produced these wire artifacts; that translation-validation link is future work.

| Development observation | Before | After |
| --- | --- | --- |
| Source revisions / duplicated `.qli` bodies removed | 0 | 0; source ergonomics unchanged |
| Native phase-word acceptance | Missing executable | Exact action checked against an independent request |
| Mathematical justification | External reasoning about the intended summary | Actual `verify_sound` theorem over cyclic phase action |
| Checking cost | No native checker to measure | At most 4096 gates; constant-size summary, no dense matrix construction |
| Broader claims | Common sized QPE and complex semantics unavailable | Still pending; this experiment does not satisfy H1–H5 |

## Backend execution policy regression checkpoint

The [2026-09-29 validation record](backend-policy-validation.json) captures the
expanded [source/compiled audit suite](../../../scripts/test_check_lean_kernel.py)
and the actual runtime-package build, reduction tests and declaration audit.
Temporary nested backend modules test all four forbidden execution constructs,
private names, omitted imports and generated partial helpers. Axiom-free
logical theorems do not authorize `implemented_by` or `extern` replacement.
These are policy fixtures, not an implemented backend or `LeafRealizer` API.

## Proof importance and temporary-label checkpoint

The [2026-09-29 label validation](proof-labels-validation.json) rebuilds both
Lean packages, audits every imported project declaration, independently replays
the kernel and exports the unchanged component theorem types after documentation
comment changes. The inventory
classifies 27 declarations in six retirement groups, with importance and explicit
replacement/removal conditions. No proof body or executable definition changed;
this record is not a new semantic regression run or feature completion.

Copyright 2026 Masahiko G. Yamada. Apache-2.0.
