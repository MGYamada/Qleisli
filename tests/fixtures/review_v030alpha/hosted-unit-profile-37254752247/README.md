# Hosted Unit-profile assertion

GitHub run 37254752247 checks pushed head e01e98a42a00c04892617205307f2db76b5c404e.
Its latest-Rust job failed in the three-test frontend_types target because an
old assertion still required Q<Unit> parsing to fail. The approved and tested
shared Unit projection now accepts that exact type. `rust.excerpt.txt` is the
contiguous actual hosted output for this target and its failed step, not an
inferred reconstruction or the complete workflow result.

`frontend_types.before.rs.txt` preserves the existing test before repair. The
current test includes Q<Unit> among the accepted signatures and uses the still
unsupported Q<(Unit,Unit)> as its separate profile-negative case. The historical
copy under ordinary-type-cutover is unchanged. No production behavior was
relaxed or reverted for this repair.

The current three tests pass on Rust 1.98.1 and actual 1.85.0 as part of the
recorded quantum-unit-maps focused runs. That local repair does not convert the
earlier hosted failure into a success. Other jobs were still running at the
first capture recorded in `metadata.json`; `completed-jobs.json` now records
their final states. The overall run and required aggregate gates failed.

`msrv.excerpt.txt` retains the identical assertion failure from actual job
111589372022. The distribution artifact independently records the same failure
in its extracted source tree. Cargo stopped at that target; later source tests
were not run. Successful Lean, native comparisons, macOS, interop and docs
producer jobs do not make the full CI successful. `repair.patch` records the
test-only repair against the pushed head.
