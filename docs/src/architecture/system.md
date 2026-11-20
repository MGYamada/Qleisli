# System architecture

In [Working with the tools](../learn/tools.md) every report named a separate
checker executable. This chapter explains that design. It names the parts of
the system and follows one of your projects through them. The two chapters
after it look inside the [compiler](compiler.md) and the
[verifier](verifier.md).

## Two programs and one decision

Qleisli uses a Rust host and a separate native Lean verifier. The **host** is
the `qleisli` command you have been running. It reads source programs or
external artifacts and prepares an intermediate representation (IR) for
checking. The **verifier** is the executable you named in `QLEISLI_KERNEL`.
It decides whether the submitted artifact meets the checks for the requested
mode. An **execution decision** from the verifier authorizes the host to use
the checked representation for a supported run, sample or export.

![Source and external inputs reach the native verifier through the Rust compiler or adapters. An authorized execution view goes to simulation or export.](diagrams/system.svg)

[Mermaid source](diagrams/system.mmd)

The host proposes and the verifier decides. The host has no path around a
rejection. When the verifier is missing or incompatible, the host rejects
every command that needs a decision. A command that only reads source, such
as `qleisli doc`, runs without it.

The lessons said "the checker" for whatever accepted or rejected a program.
From here on the two programs have their own names. The compiler inside the
host checks source and reports the diagnostics you repaired. The verifier
decides acceptance.

## Components

| Component | Responsibility |
| --- | --- |
| Source project | Groups `.qli` modules and selects the language edition in `Qargo.toml`. The bundled standard library supplies reusable operations. |
| Rust host | Provides the `qleisli` CLI and Rust library. The Python client calls the CLI. The [compiler](compiler.md) lowers source, and input adapters prepare proposals for supported external formats. |
| Native verifier | Independently checks proposals in a separate process. The [verifier chapter](verifier.md) explains what an execution decision binds. |
| Simulation and export | The Rust host uses the accepted representation to simulate or sample supported programs. Export additionally requires the checks for the selected format and target profile. |

## A project through the system

Take the `bell-lab` project from the [Bell-pair lesson](../learn/bell-pair.md).
Each command you ran there drives a part of the diagram.

| Command | What the system does |
| --- | --- |
| `qleisli check bell-lab` | The compiler reads the project and checks the source. It lowers each concrete function to IR and submits the IR to the verifier. The report lists the decisions. |
| `qleisli run bell-lab` | The host also obtains an execution decision for `main`, then simulates the accepted representation. The result is a distribution over the measured bits. |
| `qleisli sample bell-lab` | The host follows the same path and reports sampled outcomes from the simulated model. |
| `qleisli emit-ir` and `verify-ir` | The first writes the checked IR to a file. The second sends such a file to the verifier without any source. |

A rejection can come from either program. The ownership diagnostic in
[Following a quantum owner](../learn/ownership.md) came from the compiler,
which could name the source line. The `invalid_ir` rejection of the edited
file in [Working with the tools](../learn/tools.md#keep-the-checked-program)
came from the verifier, which saw only the file.

## Why the decision is separate

The compiler does many things. It parses, resolves names, specializes and
lowers, and it grows with every convenience the language gains. A mistake in
any of those steps could let a wrong program through. So the system does not
rely on the compiler being right. The compiler's output is a proposal, and
an independent program checks it. That program is written in Lean, and it
decodes its input itself.

The same rule covers every way a program can arrive. Source you write,
source a tool generates and an IR file from elsewhere all reach the same
verifier and receive the same checks. Who wrote a program gives it no
authority.

## Status and limits

The simulator implements a reference model. External formats such as
OpenQASM 3 and QIR have bounded experimental profiles. Native acceptance
covers the submitted artifact and its requested checks. Correspondence to
the original source, the execution result, or emitted hardware operations
requires its own evidence.

## Going deeper

Continue with [Compiler architecture](compiler.md). For the policy this
chapter summarizes, read [Policy, constitutional harness and execution](../reference/architecture.md).
The [production boundary](../reference/production-boundary.md) lists what
each check covers, and [target realization](../reference/realization.md)
covers export.
