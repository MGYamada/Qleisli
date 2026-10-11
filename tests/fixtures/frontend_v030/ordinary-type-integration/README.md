# Ordinary type integration checks

`validation.json` summarizes the root agent's observed metadata, documentation,
corpus provenance, and formatting checks. These are not fresh Rust compilation
or full Lean replay results. The separately recorded
[baseline comparison](../ordinary-type-baseline-integration/README.md) reused an
existing CLI for 36 calls: eight emitted artifacts remained byte-identical and
four negative cases rejected.

`format.json` binds the 19 Rust files changed only by `cargo fmt` after the
independent executable observations. Earlier handoff and execution records keep
their original hashes. The current verification inventory was updated for the
formatted source, while all 135 historical corpus/comparison pins retained
their original digest values. Twenty-three now point to preserved before copies
through the explicit VM-22 relocation record.

The first formatting check failed and the first mdBook build reported an
unclosed HTML tag. Formatting and a missing Markdown code span were repaired;
both final checks passed. The reported metadata checks do not establish full
frontend preservation, close the parent type-system issues, or replace the
pending Rust/MSRV/Python bridge and exact-commit CI runs.

No new Cargo/Lean build, large repository snapshot, or historical temporary
directory deletion was performed for these integration checks.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
