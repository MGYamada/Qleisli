# Qleisli design principles

English authoritative. Aim for mathematical quantum source and a BLAS/LAPACK-like library unifying concepts, derivations, reusable code and formal contracts. Until0.5 algorithms go to [corpus](../corpus/POLICY.md); [STDLIB](../STDLIB.md) community growth follows.

## Follow Rust for type and ownership discipline

Follow Rust identity/arity/nesting/moves/scopes; quantum/evidence differences require explicit rules. Preserve linearity, discard, exact clean release and complete returned/residual/pending/caller interfaces. Unspecified Rust features are not APIs.

## Start with the quantum programs we want to write

Keep desired first source, executable translation, actual diagnostics/counterexamples under [sessions](../tests/fixtures/authoring_sessions/README.md). State removed obligation/replacement evidence/independent checker before extending acceptance. [Imaginary drafts](../docs/imaginary-v1/README.md), informed studies and model benchmarks differ.

## Resource semantics as a first-class account

Resource Safety needs actual compilation-preserved bounds, distinguishing live space/cumulative work/shared description/repeated execution. Ownership and budgets alone prove no resource theorem.

## Keep the trusted core small

[Trust boundary](../TRUSTBOUNDARY.md) fixed. Convenience desugars to specified operations without new meanings/acceptance; identical independent checks for every producer. Valid IR proves no source preservation. New M2 acceptance belongs in Mathlib-free Lean under transfer gates; retire public support only with versioned migration.

## Quantum data and effects

Q<A> owns ordered operation rights (including zero width), not states/effects. Basis-copy injection is not unknown-state cloning. Effects Unitary<=Iso<=Observe; total pure functions compose compatible interfaces/join effects, adaptive histories sum CP maps. Loading has no quantum state/I/O. Kleisli motivation grants no strict monad/free-vector bind execution API.

## Open central issue: separating ownership from entanglement

Separate owners may remain correlated; local actions extend by reference identity. Gates/partial observation/discard/reset/boundaries act globally; need cleanup semantics, not general entanglement inference. Measurement consumes, init creates fresh logical wire. Pure release requires exact all-input factorization, never Clean names/lifetimes; unitarity grants no inverse/control access. Types/language/formal scope specify rules.
