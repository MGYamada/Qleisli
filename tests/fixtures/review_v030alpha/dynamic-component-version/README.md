# Dynamic component mode version regression

The native CI run `37199880164`, job `111429438285`, failed in the
`hierarchical-preparation` and `sized-instrument` tasks because the shared Python
adapter invoked `--preparation-check` / `--readout-check` without the required
product version. The kernel returned `error/version`; the adapter reported a
malformed component response. This was a caller failure, not an acceptance
bypass.

`instrument_transport.before.py.txt` preserves the adapter at the commit named
in `before.json`. `inputs.json` and the two binary payloads retain independent
one-qubit requests and packets. The local before replay reproduces both failures
against the recorded native binary. It is separate from the hosted CI log.

The fixed adapter reads `package.version` from the authoritative `Cargo.toml`
using the same `tomllib` convention as the other native callers. No fallback or
version inference from the executable was added.

Validation performed:

- `python3 scripts/test_instrument_transport.py --record tests/fixtures/review_v030alpha/dynamic-component-version/after.json`
  passed five tests and ten native process calls: both valid components,
  mismatched requests, truncated frames, and missing/wrong versions. An unknown
  component starts no process. These cases use one physical qubit at most and
  retain an empty Unit owner.
- `client-smoke.json` records all 22 existing preparation case decisions plus
  `test_sized_instrument.components` on the existing QPE source with `n=1,m=1`.
  Both preparation and readout succeeded for that two-qubit source proposal.
  This did not rebuild the Lean coefficient oracle or rerun either whole suite.

The caller audit included dynamic mode construction and forwarding, rather than
only literal mode names. Other maintained direct Python native calls pass their
Cargo-derived product version. The compatibility test forwards all arguments;
source/interop test wrappers forward `sys.argv[1:]`. Rust native and hierarchy
mode selection delegates to `src/interchange/process.rs`, which appends
`CARGO_PKG_VERSION`. Historical fixtures and deliberate missing-version tests
remain unchanged. Legacy file-argument modes such as `--phase-dag` have a
different dispatch contract and were not given native-mode version arguments.

These checks establish component transport and the recorded bounded decisions.
They do not issue whole-instrument receipts, prove source preservation, or
establish a successful rerun of the hosted CI workflow.
