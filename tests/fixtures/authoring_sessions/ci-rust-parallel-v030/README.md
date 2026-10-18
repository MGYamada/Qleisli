# Rust CI scheduling experiment

[The index](index.json) binds the inert [original records](records.json.gz).
The original manifests and three small-system Rust clients come from
`bd2a66b726119463074536b6f60560ded09456f0`. Original hosted logs retain successful
push Rust validation and three later 3,600-second partition timeouts; a timeout
is not an assertion failure or successful execution of the unfinished targets.

The initial same-source development experiment compares the original Cargo selection,
one scheduler worker and two workers, using the existing target directory and
the same audited native executable. All three runs pass the same 34 named tests
with zero conditional native skips: 24.17, 23.03 and 16.68 seconds respectively.
The approximately 31% reduction is a bounded warm-build measurement on macOS,
Rust/Cargo 1.98.1 and Python 3.14; it is not a hosted full-CI benchmark or a proof.

The separate optimization-level-1 experiment retains debug assertions and
overflow checks, but does not improve this measurement enough to adopt it.
CI retains its existing compiler profile. The first direct-executable scheduler
prototype is retained separately; the implementation delegates each harness to
Cargo to preserve its platform runtime environment. Original local preflight
failure and the later repair window remain distinct records.

The archive contains bytes, hashes and observations, never reusable acceptance
decisions. [The retention regression](../../../../scripts/test_run_rust_tests.py)
decodes and hashes these bytes without executing historical commands. Current
latest/MSRV, extracted-source, native, proof and packaging checks remain required
on the final candidate. No case count, work limit, deadline, guarantee or release
status is changed by the experiment.
