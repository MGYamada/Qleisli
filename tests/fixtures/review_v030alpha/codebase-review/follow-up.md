# Follow-up contract review and Python process repair

This continues the historical checkpoint in [README.md](README.md). That
checkpoint and its failed/open observations remain unchanged. GitHub
[#343](https://github.com/MGYamada/Qleisli/issues/343) tracks the process defect;
the original feature count remains 24/111. Final hosted CI is still pending.

## Additional code inspection

- Frontend: operation/special-form judgments in `frontend/check/body`, finite
  operation, primitive, certified-computation and function-contract lowering,
  and the separate sized Raw preservation/access replay. Checked original
  provider identities, exact type trees, effect bounds, closed Meaning requests,
  caller frames, zero-width owners, ordered inverse/control actions, and shared
  depth/work limits. The replay is an untrusted comparison, not a source theorem.
- IR and execution: all codec operation/enum maps, finite-matrix canonical
  coefficients, hierarchy graph/request/instrument bridges and execution.
  Checked original body/request binding, dependency order, explicit field sets,
  independent finite equations, scalar phase, output permutations, reference
  axes, complete instrument outcomes and aggregate execution/sampling bounds.
  Requested meanings do not replace the actual program during execution.
- Lean: native-contract request/success binding, hierarchy transport and shared
  frame limits, actual finite obligations, derivation closure, typed-rule reuse
  and preparation/circuit/readout composition. Success theorems describe their
  actual executable checks. Derivation closure and finite reconstruction do not
  establish the still-pending complete analytic composition or source theorem.
- Contracts: remaining independent function-matrix extraction, including
  protected computation, conditional phase, classical branches and final axis
  order. Original native-accepted bodies remain required.
- Public documentation: checked operations, coherent maps, selected execution,
  ordinary Bits/Unit boundaries and Python usage were compared with the above
  paths and the production-boundary inventory. Concrete restrictions remain
  explicit; source success and numerical simulation confer no acceptance or
  constitutional guarantee. Historical/experimental QFT remains outside work.

Together with the original checkpoint this covers the five planned areas by
their public contracts and acceptance paths. It is not a claim that every
source line or every mathematical derivation has been independently reproved.
No additional confirmed contract defect emerged in this follow-up inspection.
The already documented broader proof and feature obligations remain open.

## #343 repair and bounded regressions

Each Python host invocation now owns a POSIX session. Cleanup discovers and
stops members before killing them, including the Rust native checker's separate
process group. It reaps the direct child and closes pipes on success, failure,
timeout and interruption. Discovery/stopping has a two-second deadline; only
the owned session is selected, with a reaped-leader reuse guard and renewed
session checks before signals. Unavailable inspection fails explicitly.
The Python README records the system `ps` dependency, deliberately escaped
session exclusion, and the existing non-POSIX direct-child limitation.

The new bounded test fails in all four cases on the prior host implementation:
normal exit, unsuccessful exit, timeout, and inherited output pipes. The test
cleans up its own children even when testing that historical failure. An
unrelated sentinel must survive. The corrected host suite passes four tests;
the freshly installed package passes thirteen, including a real Rust CLI
invocation whose fake native checker starts in a distinct process group and
must be gone after timeout. No large input or maximum-size fixture is generated.

VM-22/VM-29 identities were refreshed only for the reviewed Python source;
public boundaries, accepted formats, dependencies and proof status are unchanged.
The regression evidence and source hashes are in `process-lifetime.json`.
Earlier local full Rust/MSRV, native, distribution, Lean and book results retain
their original revisions in `validation.json`; they are not final-commit passes.

## First hosted integration observation

Run [37611436412](https://github.com/MGYamada/Qleisli/actions/runs/37611436412)
for `6bd9d62ec3dbde1c01e62b0a55a975ae1611118d` failed in the `changes`
preflight. The runner unit test mocked HEAD as `a` but inherited the real
`GITHUB_SHA`, so it stopped before the deliberately failing child command.
The tool-mismatch test also failed for the wrong reason without detecting it.
Both tests now set their event identity explicitly; a separate regression
requires a mismatching identity to reject before tool probes or commands.
The production identity check is unchanged. All eight preflight scripts pass
locally with `GITHUB_ACTIONS=true` and an unrelated `GITHUB_SHA` supplied.
The failed hosted run remains failed; it was not retried or counted as success.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
