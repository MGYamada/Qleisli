# Qleisli Programming Language

Qleisli is an experimental language for structured quantum algorithms. It
combines linear quantum ownership, explicit measurement effects and exact
semantic contracts.

Qleisli and its tools are independent projects. They are not affiliated with,
endorsed by, or sponsored by the Rust Project or the Rust Foundation.

**Qleisli is pronounced exactly like Kleisli.** Its initial Q marks the
classical-to-quantum ecosystem lift without changing the pronunciation. See
the canonical [project name and pronunciation](reference/project-identity.md).

## What this book contains

| Part | Content |
| --- | --- |
| Constitutional authority | The records of the ratified Constitution, the [authority hierarchy](reference/authority.md), the adopted interpretations and guarantees, and the [boundary](reference/production-boundary.md) of what the native checker accepts |
| Language Reference | The rules of the language, from [source text](reference/source-text.md) and [types](reference/type-model.md) to the [standard library](reference/stdlib.md) and [realization](reference/realization.md) |
| Design history | The records of two retired design packets: the decisions that followed them and the proposals that no decision adopted |
| Retained drafts | The [imaginary-v1 drafts](imaginary-v1/index.md), with their original scope |
| Contributing | The [build guide](building.md) and the style guide for the chapters |

The book has no tutorial part. A guide that builds from small executable
programs toward reusable quantum algorithms is planned.

For a Bell-pair program and the distribution status, start with the
[repository guide](https://github.com/MGYamada/Qleisli/blob/main/README.md#example).
The [roadmap](https://github.com/MGYamada/Qleisli/blob/main/ROADMAP.md) records
planned language features and their status.

This introduction is descriptive. Normative requirements and proof claims
retain the scope of their adopted source documents. Rendering a page does not
establish a language rule or a correctness proof.
