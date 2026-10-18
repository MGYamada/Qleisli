# Ordinary primitive CI follow-up: first failures

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

This informed, curated continuation was assembled after the real PR #419 hosted
failures at 47716d0a2a4bc8dcfc6923ed4cf0f3c4c9d8a8b5 and the separately recorded
local BEFORE reproduction. It is not a pre-run archive, blind authoring task or
model benchmark. Earlier ordinary-primitive-test-regressions-v030 observations
are unchanged. Immutable Git path/hash references retain the original Rust
assertions, Lean fixture, producer interfaces, selectors and ordinary std body.
The PR merge checkout ba73a9c92863788db5008764891db6809e5e488f is distinguished
from its requested head; push jobs checked out the head itself.

The six QLI files are separate inputs to existing Rust helpers, not a project
claimed to have been executed together. Qargo declares edition 2026 for storage
only. The two axis files preserve the exact generated first-case source and its
finite closed wrapper. Both finite and selected values are constructed before
the first assertion; the other three loop cases are preserved in the original
Rust driver, without claiming they ran after the first-case panic. The four
mixed inputs are byte-identical selected current fixtures, found through the
existing full-chain selector. Their original historical paths and mappings
remain unchanged. No source or import text has been repaired here.

All four hosted Rust/MSRV leaves fail at axis_routing_boundary.rs:153:13:
the ordinary three-CNOT source has zero Raw Cnot nodes where the old test expects
three. Ordinary cnot is controlled ordinary X (H Z H); actual retained controlled
actions must still be checked against independent full-phase CNOT and SWAP
meanings, with ordered physical wires. Counts alone are not a semantic oracle.
The preceding ownership/source-correspondence partition passed through the
native gate; its individual successful test stdout is not printed. The later
ordinary_types and mixed_booleans targets were not reached in these four jobs.
The shared runner prints only a failed child output tail; a complete provider
job log therefore is not a complete Cargo stdout/stderr capture.

Both hosted Lean leaves first complete Tests.lean, then report five diagnostics
in the live historical refactoring fixture: three old Context helper signatures
no longer match PreparedContext, and old checkAll definitional equality no
longer closes by rfl. This records a consumer/proof-fixture migration need; it
does not claim the current proof obligations are discharged by changing a type
name. No QLI file is executed by these Lean commands. Their immutable original
proof source is referenced rather than duplicated or silently rewritten.

The separate local BEFORE command runs both Rust targets with no-fail-fast:
axis has two passes and one failure; mixed has three passes and four failures.
Two mixed tests still search/count Raw Cnot; two deterministic distribution
checks encounter tiny numerical residues and mass 1.0000000000000004 after
ordinary H Z H. These are local observations, not additional hosted failures.
The exact selected sources, full local streams, compiler/kernel/input stability
and original full-driver hash remain bound. The observed CLI hash is not a fresh
standalone build attestation. No numerical acceptance tolerance is introduced.

Focused hosted transcript projections retain full relevant diagnostics, line
ranges and full external provider/log hashes. Their recorded_utc is assembly
time, never an invented execution start. The local projection retains complete
stdout/stderr and driver metadata except repeated input maps, whose canonical
hashes/counts and complete external driver are bound. Commands are inert
historical evidence and must not be executed from these JSON records.

This packet contains BEFORE observations only. Later repairs and actual AFTER
results must be appended separately without replacing these bytes. It grants
no source-preservation theorem, full CI success, release approval or issue
completion. QS, PR, RS and EXACT obligations remain pending; the two scoped
protected guarantees retain their existing meanings and premises.
