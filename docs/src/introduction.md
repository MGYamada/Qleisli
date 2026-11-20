# Qleisli Programming Language

Qleisli is an experimental language for structured quantum algorithms. In
your first program you will prepare one qubit and return one ordinary bit.
By changing a single operation, you can make that bit predictable or give
its two values equal probability.

## Getting started

If you can read a function and use a terminal, you can start with
[Measuring your first qubit](learn/first-qubit.md). You'll meet the quantum
operations as you use them. Keep the small projects you write along the way.
Each lesson tells you which file to open and where to run the commands.

The first project grows when you [follow a quantum owner](learn/ownership.md)
and use a compiler diagnostic to repair a measurement. In the second,
you'll [build a Bell pair](learn/bell-pair.md), then [give its circuit a
function and module of its own](learn/functions-and-modules.md). Use that
same circuit to [teleport a qubit](learn/teleportation.md) and see how a
measurement can reveal a missing correction. In the last project, you'll
[search four inputs](learn/search.md) using operations from the standard library.

## About Qleisli

Qleisli and its tools are independent projects. They are not affiliated with,
endorsed by, or sponsored by the Rust Project or the Rust Foundation.

**Qleisli is pronounced exactly like Kleisli.** Its initial Q marks the
classical-to-quantum ecosystem lift without changing the pronunciation. See
the canonical [project name and pronunciation](reference/project-identity.md).

The Qleisli Constitution establishes the Qleisli Soundness Theorem, the
Physical Realizability Theorem, and the Resource Safety Theorem as its three
fundamental proof obligations.

## What this book contains

| Part | Content |
| --- | --- |
| Language Reference | The rules of the language, from [source text](reference/source-text.md) and [types](reference/type-model.md) to the [standard library](reference/stdlib.md) and [realization](reference/realization.md) |
| Architecture | Follow a Bell-pair program through the [system](architecture/system.md), explore the [compiler](architecture/compiler.md) and [verifier](architecture/verifier.md), or see the [proposed Rust crate layout](architecture/rust-crates.md) |
| Design history | The decisions arising from two retired design packets and the proposals that were never adopted |
| Roadmap | The [six algorithm goals](imaginary-v1/index.md) for Qleisli 1.0.0 |
| Contributing | The [build guide](building.md) and the style guide for the chapters |

The [roadmap](https://github.com/MGYamada/Qleisli/blob/main/ROADMAP.md) records
planned language features and their status.
