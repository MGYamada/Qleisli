# Project name and pronunciation

This is the canonical project-identity wording for Qleisli 0.3.0, following
the decision in [Issue #234](https://github.com/MGYamada/Qleisli/issues/234).
Other introductions and naming guidance should link here or reproduce this
meaning without changing it.

**Qleisli is pronounced exactly like Kleisli.** The name expresses a
**Kleisli-style lift of the classical software ecosystem into a quantum
ecosystem**. The spelling is **Q + Kleisli**. The initial **Q** denotes quantum:
it changes the semantic world indicated by the spelling, not the pronunciation.

## The ecosystem naming principle

The same classical-to-quantum naming principle appears in:

| Classical ecosystem | Qleisli ecosystem |
| --- | --- |
| `cargo` | `qargo` |
| `crates` | `qrates` |

The `c` to `q` transition is intentional. Mature classical software-engineering
structures are retained where appropriate and lifted across the
classical/quantum boundary, rather than reinvented merely for novelty.
This naming relationship does not establish feature parity or the availability
of a tool or command; those require their own documented contracts and status.

## Metaphor and formal semantics

“Kleisli-style lift” is the name's origin and a design metaphor. It does not
require every language construct, compiler layer or theorem to be formalized
as a literal Kleisli category or as one particular monad. Any formal
categorical semantics is a separate technical claim that must be specified
and justified independently under the [authority hierarchy](authority.md).
The name itself changes no language acceptance rule or proof obligation.

**The Q changes the world, not the pronunciation.**

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
