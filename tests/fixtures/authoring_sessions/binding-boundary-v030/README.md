# Assignment and mutable-binding diagnostic probes

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

This informed maintenance study implements the fixed decisions in
[Issue #73](https://github.com/MGYamada/Qleisli/issues/73) and
[Issue #77](https://github.com/MGYamada/Qleisli/issues/77). No external model
was invoked. The [context](context.md), first source bytes, manifest and baseline
observations were saved before changing the implementation. The
[session](session.json) binds all sources and both sets of actual observations.
The original programs were not repaired or regenerated.

| Probe | Before | After |
| --- | --- | --- |
| Assignment of a live quantum owner | Parse refusal | Ownership refusal at the original destination |
| Assignment of a mixed quantum-containing tuple | Parse refusal | Ownership refusal at the original destination |
| Assignment of an ordinary binding named `q` | Parse refusal | Unsupported ordinary assignment |
| Mutable quantum binding | Parse refusal | Ownership refusal at the original `mut` marker |
| Mutable mixed quantum-containing tuple | Parse refusal | Ownership refusal at the original `mut` marker |
| Mutable ordinary binding named `q` | Parse refusal | Unsupported ordinary mutability |
| Explicit consuming `let` rebinding | Native check succeeds | Native check succeeds |
| Ordinary contextual identifier `mut` | Native check succeeds | Native check succeeds |

All eight exit statuses are unchanged. Each set records eight CLI invocations;
the six refusals confer no native acceptance. Commands, timestamps, executable
hashes and raw results are retained in `before/` and `after/`. The executable
hash is checked before and after each invocation; it does not attest the
compiler build or prove source preservation. No kernel rule, schema, release
version, accepted mutation construct or new guarantee was added.

The separate Rust regressions check nested zero-width owners, original byte
spans with Unicode/CRLF, a consumed destination, static/unknown targets, unused
definitions, both branches and empty folds. They are conformance checks, not a
general theorem about source semantics or arbitrary external references.
