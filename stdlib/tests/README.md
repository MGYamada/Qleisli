# Standard-library test root

This is the QLT test root declared by [Qargo.toml](../Qargo.toml). There are
currently no executable `.qlt` tests: QLT implementation remains deferred to
v0.4.0 or later. Qargo must report its unavailable test backend explicitly.

Current library regressions remain in the compiler's Rust test suite, including
[algorithms](../../tests/algorithms.rs), [static operations](../../tests/static_operations.rs),
[order finding](../../tests/order_finding.rs) and
[semantic contracts](../../tests/semantic_contracts.rs). Run them from the
repository top-level directory with `cargo test --all-targets`. Their scopes
and the separate proof obligations remain in the
[contract ledger](../../docs/stdlib-contracts.md). Declaring this qrate test
root does not move, duplicate or replace those checks.
