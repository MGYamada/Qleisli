# Static Nat tables: unfinished attempt

Issue [#63](https://github.com/MGYamada/Qleisli/issues/63) is deferred for
**0.3.0-alpha** by explicit maintainer instruction. It remains open; this
attempt supplies no shipped syntax, completed acceptance criterion or proof.

`attempt-01.patch` preserves the uncommitted frontend experiment against
commit `ae0b2804177aa31f56a3ac21735240d41f1863e5`. The adjacent manifest binds
the patch and the original modified file bytes. Apply with `git apply --check`
and `git apply` only in an isolated checkout of that base for future study.
The production files have been restored to that base.

The experiment adds provisional static Nat arrays, bounded generators and
named lookup to parsing and original-source checking. Concrete selected-source
materialization remains explicitly unsupported; grammar and checking are
incomplete. The existing shipped scalar Nat helpers remain unchanged.

An intermediate `cargo check --locked --all-targets` succeeded. The final
`cargo test --locked --lib frontend::check::static_tables::tests` failed to
compile with E0277 because two test messages formatted `SourceError` using
Display. No new table test ran. There was no completed formatting, clippy,
CLI/native validation, Lean replay or guarantee admission for this patch.

The separately committed first sources, repairs, predictions and 38 actual
pre-implementation CLI observations remain under
`tests/fixtures/authoring_sessions/static-nat-tables-v030/`. They record parser
barriers, not implemented table semantics. The `unused-invalid-body` draft
contains `n-1` under `0 <= i < n`, which can justify nonnegativity in a
nonempty range; its original negative prediction is not a semantic oracle.

This archive is experimental source history, not a second work tracker.
Original Issue acceptance criteria and the stable 0.3.0 milestone are retained;
alpha deferral does not count as completion.
