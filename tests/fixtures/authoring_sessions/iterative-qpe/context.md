# Iterative QPE authoring context

Task: implement fixed three-bit iterative phase estimation in existing QLI,
compare it with the existing coherent QPE, improve repair diagnostics and
preserve the first source and subsequent observations. Keep development at 0.1.8.

Author: the current Codex assistant (GPT-6 family; exact deployment identifier
and sampling parameters are not exposed). This is one informed development
session, not an independent or blinded model trial. No other model was run.
The assistant had the prior conversation, AGENTS.md and repository access;
context was not restricted to the quick reference. The task was proposed by
the assistant and accepted by the user with “やりましょう”.

Relevant source read before this first attempt: operation_algorithms/estimation.qli,
operation_algorithms/gates.qli, stdlib/src/transforms.qli, QLI quick reference,
algorithm corpus/routine contracts and existing phase/reference tests.
Derivation: measure U^4 first to obtain the low-weight bit; subtract low/4
before measuring U^2, then low/8 + middle/4 before measuring U.
Only T and T^2 inverse corrections are required. Each measurement consumes its
logical meter; the next meter is prepared fresh. This does not assert physical
wire recycling by the current simulator/backend.

attempt-01 is saved before its first compiler/executor invocation. Never edit
it to match the final implementation. Later checks must be new observations,
not overwritten initial results. If source changes, save the next full project
snapshot and the reason. Absence of a failed attempt means zero repairs, not
missing evidence. Intentional fault fixtures are mutations, not author repairs.
