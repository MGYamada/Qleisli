# Simulation review follow-up

Two bounded review counterexamples are retained as `original-phi.rs` and
`original-sample.rs`. These are local raw-IR studies, not upstream algorithm
translations or stress tests. Both obtain a real native accepted handle before
simulation. The first uses two qubits; the second uses one.

- **Phi copy accounting:** four ensemble components each receive 100 classical
  phi outputs without an arm operation. Before repair, execution succeeded with
  32 work units, and sampling reported only 10 units despite 100 additional
  entries. Both execution paths now charge phi metadata before allocation.
  Quantum phis charge owner entries, including empty owners, wire-list copies
  and rename entries. A separate regression preserves one empty owner and one
  live qubit through the branch and then consumes both.
- **Randomness ordering:** `Init0; MeasureZ` with two work units previously
  requested a random word before discovering that the projection needed another
  unit. A failing RNG masked that limit error. Projection preparation now spends
  the outcome-independent copy budget and returns a borrowed, single-use
  projection. Sampling chooses its outcome only after preparation succeeds.
  The same path handles hidden reset/discard observations, without double charging.

The added tests failed before the implementation change; `logs/before-phi.log`
and `logs/before-rng.log` preserve those real failures. Current regressions are:

- `tests/sim.rs::branch_phi_copies_share_the_ensemble_and_sample_execution_budgets`
- `tests/sim.rs::quantum_phi_copies_charge_empty_owners_and_wire_relabeling`
- `tests/sampling.rs::projection_copy_limits_precede_visible_and_hidden_random_draws`

After repair, 26 simulation/sampling integration tests, eight simulation unit
tests and 15 CLI tests passed. The regressions check both limit rejection and
successful execution at the exact required sample budget; the classical test
also checks both sampled outcomes and the independently expected half/half
distribution. `validation.json` records commands, outcomes, hashes and limits.

Lean acceptance and proof sources were unchanged. These observations establish
bounded host regression coverage, not general Soundness or Resource Safety.
No maximum-size stress tests, full release CI, platform matrix, publication or
GitHub issue closure was performed. Earlier review/replay records remain
historical evidence bound to their own source hashes.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
