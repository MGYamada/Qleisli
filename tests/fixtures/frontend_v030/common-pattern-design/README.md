# Local common pattern-rule candidate

This directory preserves a **non-normative local technical candidate** for the
next bounded #32 prerequisite. It neither adopts language rules nor changes
the Book, GitHub, source code, guarantees or the release gate. Read
[contract.md](contract.md) for the implementation proposal and its limits.

The proposal shares actual wildcard, repeated-name and exact pattern-shape
judgments at existing binding call sites. It leaves declaration/static policy,
scope closure, effect inference, value storage, capacity accounting and native
acceptance in their existing paths. The existing sized pattern projection is
an explicitly temporary borrowed bridge; no additional AST is proposed.

`source-inputs.json` and the two Issue snapshots record the originals used by
this review. `first-files.json` freezes the initial candidate and those inputs
by hash. Hashes identify bytes, not authorship, approval, proof or compilation.
First executable programs and actual before/after diagnostics are captured by
the parent's separate authoring experiment; this directory invents no results.

No Rust/Lean build or test was executed for this candidate. No interpretation,
guarantee, complete checker, canonical std API or Issue completion is claimed.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
