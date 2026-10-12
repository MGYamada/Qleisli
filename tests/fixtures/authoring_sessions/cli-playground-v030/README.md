# Installed CLI playground

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

See [context](context.md) for the prior information and analytical predictions,
[first sources](attempt-01/) for the preserved programs and [session](session.json)
for exact executable identities and command observations. Deliberate ownership
and algorithmic counterexamples are under `counterexamples/`, outside repairs.
The observation files retain original stdout/stderr and parsed JSON. These are
small numerical simulations and diagnostic observations, not a general proof.

All 26 recorded CLI calls completed with their expected success/refusal status.
The ten computed distributions matched the analytical predictions within an
absolute tolerance of 1e-12, without renormalization. Both executable digests
were unchanged after execution. Full machine-readable results are in
[summary.json](summary.json).

| Experiment | Observed samples with seed 42 |
| --- | --- |
| Bell, 128 shots | 00: 60; 11: 68 |
| Independent bits, 128 shots | 00: 27; 01: 33; 10: 30; 11: 38 |
| GHZ, 32 shots | 000: 16; 111: 16 |
| Corrected teleportation, 32 shots | 001: 8; 011: 8; 101: 7; 111: 9 |
| Existing Grover, 16 shots | 11: 16 |
| Existing BV, 16 shots | 10: 16 |
| Existing feedback, 16 shots | 00: 8; 10: 8 |

H H returned 0 with probability 1; H Z H returned 1 with probability 1.
Removing the teleportation Z correction still checked successfully, but the
X readout became wrong on half the probability mass. Double measurement and
implicit quantum destruction both rejected with `ownership` diagnostics.

Validation performed: constitutional record/current-evidence identity,
kernel source policy, the compiled Audit.lean declaration audit (12,138
kernel/transport declarations), authoring-session integrity, documentation
links/metadata, fixture budgets and Git diff whitespace. This exploration
changed only observation/documentation records. Rust tests, fresh native
build, full Lean proof replay and full CI were not run. No trusted continuity
base was supplied; constitutional checking did not use `--base-ref`.
