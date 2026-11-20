# Compiler architecture

Every diagnostic you repaired in the lessons had a code before its message:
`project`, `ownership`, `effect`, `contract`. This chapter walks through the
stages of the Rust compiler in order and shows where each of those
diagnostics arose.

The compiler loads and checks Qleisli source, then lowers supported programs
into IR and evidence proposals. Source checks explain errors in source
terms. The independent [native verifier](verifier.md) decides acceptance of
the resulting artifacts.

![The Rust compiler loads and parses the project, performs common source checks, and selects a lowering route before submitting IR and evidence to Lean.](diagrams/compiler.svg)

[Mermaid source](diagrams/compiler.mmd)

## Loading and parsing

Project loading fixes the source modules, imports and edition. This stage
read your `Qargo.toml` and found `pair.qli` when `main.qli` imported from
it. The `project` diagnostic about a function that
[is not public](../learn/functions-and-modules.md#move-the-function-into-a-module)
comes from here.

The parser builds syntax trees with source locations. Those locations are
the line and column at the start of every diagnostic. A `parse` diagnostic
means the parser could not read the text as a program.
[Source text](../reference/source-text.md) specifies both steps.

## Source checking

The common source checker resolves names and checks types, effects,
ownership and the requirements of operation calls. It checks both arms of a
branch and the body of a zero-iteration fold.

| Diagnostic | What the source checker did |
| --- | --- |
| `ownership` in [Following a quantum owner](../learn/ownership.md) | The parser read both calls to `measure_z`. The checker recorded that the first call consumed `q`, so it could point to the second use. |
| `ownership` on an `if` | The checker compared the owners that each block consumed and found a difference. |
| `effect` in [Choosing an effect](../learn/effects.md) | The checker computed the effect of the body from its calls and compared it with the word before `fn`. |

All of this happens before lowering, which is why these messages can use
the names from your source. The [type model](../reference/type-model.md)
describes the checks.

## Specialization and lowering

**Specialization** resolves static arguments to concrete types, sizes and
operation providers. In [Stating what an operation means](../learn/contracts.md),
`client[checked_op(direct, Flip)]` is a static argument. Specialization
produced one concrete copy of `client` for `direct` and one for `sandwich`.

**Elaboration** expands supported surface forms into operations in a
selected intermediate representation. For example, the source checker
checks both arms of `if static`, then elaboration selects the arm
determined by the concrete condition.

The compiler has three lowering routes. Each produces a different proposal.

| Route | Proposal |
| --- | --- |
| Finite project | Finite Raw operations and a serialized QIRF artifact. |
| Selected Raw | A Raw operation program for the selected source entry. |
| Selected hierarchy | A composition of operations and proposals for the finite leaves on which it depends. |

The `coin.qirf` file you wrote with `emit-ir` is a QIRF artifact from the
first route. The [elaboration contracts](../reference/elaboration.md)
specify which forms each route supports.

## Handing over

Concrete artifacts and any applicable requests go to the
[native verifier](verifier.md). The host can map failures back to source
locations when it has the corresponding source information.

The `contract` diagnostic is an example. The compiler lowered the gates of
`sandwich` and proposed them together with the meaning `Flip`. The verifier
compared the two and rejected the equation. The host then reported that
rejection at the `checked_op` in your source.

## Status and limits

A generic declaration may pass source checks before a concrete instantiation
has a native decision. Support for a source form depends on the chosen
lowering route. An IR check establishes the properties of the submitted
artifact in its checked scope. A source-preservation claim also needs
evidence connecting the original source and dependencies to that artifact.
That gap is the line `source preservation: not proved` in every check report.

## Going deeper

Continue with [Verifier architecture](verifier.md).
[Diagnostics and recovery](../reference/diagnostics.md) lists the diagnostic
codes. [Surface-to-core elaboration](../reference/elaboration.md) and
[Static values, constraints and bounded specialization](../reference/static-language.md)
give the rules for the two lowering steps, and the
[production boundary](../reference/production-boundary.md) states the scope
of each check.
