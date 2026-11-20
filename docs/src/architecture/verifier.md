# Verifier architecture

The [compiler](compiler.md) ends by handing over a proposal. This chapter
follows the proposal into the native verifier. It explains the last three
lines of the check report from [Working with the tools](../learn/tools.md):
the checker identity, the entry request and source preservation.

The native verifier is the `qleisli-kernel` executable built from the
Mathlib-free Lean package in `lean-kernel/`. You built it in the first
lesson and selected it with `QLEISLI_KERNEL`. The Rust host submits a
proposal to this process. The verifier decodes the input independently and
checks the artifact, request and evidence required by the selected mode.

![Lean validates the request and checks the artifact. Inspection returns a scoped report. Execution and caller scopes also compare execution views before a successful decision.](diagrams/verifier.svg)

[Mermaid source](diagrams/verifier.mmd)

## Request and independent checks

The host sends a versioned **QLV3 envelope** containing the edition,
requested scope, original payload and any required views. The invocation
selects a mode and product version. The verifier checks this context and
applies the mode's checks to the decoded data.

The verifier does not reuse the compiler's conclusions. It decodes the
bytes it receives and checks them itself. Two modes are familiar from the
lessons.

| Mode | What the verifier checks | Where you saw it |
| --- | --- | --- |
| Ordinary QIRF check | Ownership and classical scope of the decoded program | The line `native checks` of every report, and `verify-ir` on `coin.qirf` |
| Finite contract | The requested equation against the decoded artifact | The rejected `checked_op` in [Stating what an operation means](../learn/contracts.md) |

The compiler had already checked ownership in your source. The verifier
checks ownership again in the IR, because the IR is what runs.

## Execution binding

Passing the checks is not yet permission to run. The host could, by
mistake, simulate something other than the program the verifier checked.
The execution binding closes that gap.

An **execution view** describes the data the Rust host retains for
execution. The host encodes the view in the canonical **QDV1** format. The
verifier derives its own view from the data it decodes and checks, then
compares the encoded bytes. The requested scope determines which views it
compares. An inspection result covers inspection. The host constructs its
private accepted execution handle only from a matching execution decision.

You can see the two scopes in the [Bell-pair project](../learn/bell-pair.md).
`qleisli check bell-lab` checks the project's concrete functions. When you
run `qleisli run bell-lab`, the CLI requests an execution decision for
`main` before it simulates the two measurements.

## Rejection

A malformed input, a failed check or a view mismatch rejects the request.
The host also rejects when the selected verifier is missing or
incompatible. There is no fallback checker and no automatic download. The
[execution-view reference](../reference/execution-view.md) specifies the
envelope, scope, comparison and reply formats.

## What a decision does not cover

The report states three limits, and each has a reason.

| Report line | The limit |
| --- | --- |
| `checker identity: unpinned` | The host ran the executable you selected. It did not compare that file with a known build. |
| `entry request checked: false` | The verifier checked `main` for ownership and scope. It received no separate statement of what `main` must compute. |
| `source preservation: not proved` | The decision covers the IR. No proof connects that IR to the source text. |

## Status and limits

The separate `lean/` package contains mathematical models and proofs about
the executable checks. The two admitted guarantees concern ownership and
classical scope of the decoded ordinary root. Source and runtime
correspondence, target realization and full quantitative resource bounds
have separate proof obligations.

## Going deeper

The [production boundary](../reference/production-boundary.md) gives the
scope of each check and every field of the report. The
[execution-view reference](../reference/execution-view.md) defines the
binding, and the [primitive boundary](../reference/primitive-boundary.md)
defines the operations the verifier admits. The
[authority hierarchy](../reference/authority.md) and the
[initial guarantees](../design/initial-guarantees.md) record what the
project claims on the strength of these checks.

[Rust core crate map](rust-crates.md) closes this part with a proposed
layout for the host's code.
