# Qleisli Programming Language

Qleisli is an experimental language for structured quantum algorithms. A
Qleisli program prepares qubits, applies gates to them and measures them to
obtain ordinary bits. The checker reads the whole program before any of that
happens. It rejects a program that uses a qubit twice, loses one, or measures
where its signature promised not to.

## Three ideas

You will meet three ideas again and again in this book.

- A quantum value has one owner, and the program uses that owner once. A gate
  takes an owner and returns one. A measurement takes an owner and returns a
  bit. The checker follows every owner to the place where the program gives
  it up.
- A function declares its effect. The word before `fn` says whether the
  function computes on ordinary data, applies gates, prepares qubits or
  measures. The checker compares that word with the body.
- A separate verifier decides acceptance. The compiler translates your source
  and proposes a result. An independent native program, built from Lean,
  checks the proposal before anything runs. A program you write and a program
  a tool generates pass through the same checks.

## How to use this book

Read the first two parts in order. Each chapter builds on the projects and
the vocabulary of the chapters before it.

**Learning Qleisli** is a course of nine lessons. If you can read a function
and use a terminal, start with [Measuring your first qubit](learn/first-qubit.md).
You'll meet the quantum operations as you use them. Each lesson tells you
which file to open, asks you to predict a result, and lets you run the
program to check.

| Lesson | What you learn |
| --- | --- |
| [Measuring your first qubit](learn/first-qubit.md) | Set up the tools, write a function, read a distribution |
| [Following a quantum owner](learn/ownership.md) | Why the checker rejects a reused or forgotten qubit, and how to repair each case |
| [Building a Bell pair](learn/bell-pair.md) | Operations on two owners, and correlated measurements |
| [Writing functions and modules](learn/functions-and-modules.md) | Parameters, results, files and `pub` |
| [Choosing an effect](learn/effects.md) | What `classical`, `unitary`, `isometry` and `observe` promise |
| [Teleporting a qubit](learn/teleportation.md) | Measurement results that steer later gates |
| [Searching four inputs](learn/search.md) | The standard library and a small Grover search |
| [Stating what an operation means](learn/contracts.md) | A meaning, two implementations and a caller that accepts either |
| [Working with the tools](learn/tools.md) | Every `qleisli` command you need, on the projects you built |

**How Qleisli works** follows one of your projects through the implementation.
[System architecture](architecture/system.md) names the parts.
[Compiler architecture](architecture/compiler.md) shows where the diagnostics
you repaired come from. [Verifier architecture](architecture/verifier.md)
explains what an accepted check establishes and what it leaves open.

The other parts are for looking things up.

| Part | Content |
| --- | --- |
| Language Reference | The rules of the language, from [source text](reference/source-text.md) and [types](reference/type-model.md) to the [standard library](reference/stdlib.md) and [realization](reference/realization.md) |
| Design history | The decisions arising from two retired design packets and the proposals that were never adopted |
| Roadmap | The [six algorithm goals](imaginary-v1/index.md) for Qleisli 1.0.0 |
| Constitutional authority | The adopted records that bound what a check may claim, starting from the [authority hierarchy](reference/authority.md) |
| Contributing | The [build guide](building.md) and the style guide for the chapters |

The [roadmap](https://github.com/MGYamada/Qleisli/blob/main/ROADMAP.md) records
planned language features and their status.

## About Qleisli

Qleisli and its tools are independent projects. They are not affiliated with,
endorsed by, or sponsored by the Rust Project or the Rust Foundation.

**Qleisli is pronounced exactly like Kleisli.** Its initial Q marks the
classical-to-quantum ecosystem lift without changing the pronunciation. See
the canonical [project name and pronunciation](reference/project-identity.md).

The Qleisli Constitution establishes the Qleisli Soundness Theorem, the
Physical Realizability Theorem, and the Resource Safety Theorem as its three
fundamental proof obligations.
