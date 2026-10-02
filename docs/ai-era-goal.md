# Development goal 1: a quantum language for the AI era

Human and AI source undergo identical type/effect/ownership and independent IR checks.
Diagnostics identify failing obligations/locations; author identity, explanation and
proposed certificate grant no authority. [Design](design-philosophy.md),
[current status](current-status.md) and [formal core](formal-core.md) separate goals
from implemented/tested/proved results.

## Levels of guarantees

Linear ownership protects exclusive operation rights and rejects duplicate/unhandled
owners and protected conflicts; general borrowing remains future. Ideal quantum
soundness additionally needs valid primitives, injective lifts, full phase, certified
separation/cleanup and composition. Protocol correctness (e.g. teleportation) and
algorithm success need independent specifications/proofs. Quantitative
[Resource Safety](resource-semantics.md) needs actual execution/compilation bounds,
not ownership or checker budgets. Types alone do not prove the latter guarantees.

## Intended soundness theorem

Finite terminating valid rules imply a quantum instrument on arbitrary references:
each outcome CP/TNI, total TP; pure Iso V†V=I, Unitary also VV†=I, closed main normalized
classical distribution. Actual frontend/Rust IR/backend correspondence remains open.
The bounded [SC/FC foundation](finite-contracts.md) is implemented/validated; initial
[six drafts](imaginary-v1/README.md) complete only a design prerequisite, not v1.
[Milestones](release-milestones.md) fix the full actual-checker theorem gates.

## Development workflow and acceptance

Preserve desired first source under [session procedure](../tests/fixtures/authoring_sessions/README.md),
state independent meaning, frontend-check/lower, independently verify raw evidence,
execute the exact accepted artifact under backend capabilities. Specify complete
correlated-system acceptance/rejection, prove actual checker acceptance and bind
translations before claiming compile-time soundness. Bell/phase/feedback supplement
proofs; prior [QWIRE](https://arxiv.org/abs/1803.00699)/[Proto-Quipper](https://arxiv.org/abs/1812.03624)
work is not implementation evidence.
