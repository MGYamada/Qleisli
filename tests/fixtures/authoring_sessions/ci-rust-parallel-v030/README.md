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

The later [rooted-retention failures](coverage-first.json.gz) preserve the actual
hosted refusal and original README/consumer bytes at `8befdc78`. The consumer now
reads this README explicitly; the inspector and its coverage rules are unchanged.

The [first corpus-policy placement failure](workflow-first.json.gz) retains the
actual hosted diagnostic and original test/action sources at `fd17cea8`.
The regression now executes the shared action's actual corpus shell under all
five existing CI event/profile cases. Its 40 tests move into the early preflight,
once per workflow, retaining the quick corpus policy and all prior coverage.

The [native/harness observations](native-first.json.gz) preserve the first hosted
distribution log, the local sandbox `ps` refusal, a later native-protocol failure,
the same simulator test passing alone, and separate two-thread positive runs.
The original bounded hosted stdout preview does not identify the failed target;
its uploaded per-harness payload was not independently downloaded. The scheduler
now prints failed-target identities/reasons last, after other workers finish.
Normal Rust and MSRV each pass 466 tests across nine selected harnesses with two
existing ignores and zero conditional native skips. These bounded macOS runs do
not prove the earlier native-protocol failure's cause or complete Linux CI.

The [computed-source timeout study](computed-timeout-first.json.gz) retains the
actual latest-head Linux failure, both unchanged small-qubit sources, the
original scheduler/checking code and all local per-invocation observations.
Those two sources pass separately on macOS; their slowest native calls take
about 16 seconds. These observations neither identify the Linux cause nor
establish a repair. The full computed-source harness is now scheduled alone
with one test thread, before other harness workers. All cases, exact equations,
fresh native decisions and the 60-second transport deadline remain required.

The [producer-partition first sources](producer-first.json.gz) preserve the nine
original workflow, plan and receipt implementations at `11745e6884cc0775f47cfceb6bcfd2a8cdb4f9a3`.
This informed manual study invokes no external model. The current helper selects
complete commands from the single canonical plan, retaining fresh native
preparation and explicit omitted indices. Actual latest/MSRV Cargo metadata
contains 131 targets, including the same two differential and 121 other
integration targets. This validates partition coverage only; no Rust/native test
or proof was executed by those metadata/CLI-plan observations. Separate hosted
producer jobs, same-run aggregation and release receipt binding were still
pending at that stage.

The [first pair-obligation experiment](producer-obligations-first.json.gz)
retains the proposed implementation contract, original prototype and its actual
synthetic output: two complete dependency records and 38 refusals for missing,
failed, skipped or stale inputs. No artifact bytes or actual hosted jobs were
validated by that experiment. The current dependency helper returns only the
expected receipt hashes; independent artifact validation remains mandatory.

The [first post-wiring refusals](producer-wiring-first.json.gz) retain the
original action/workflow sources and the actual adapter failures while migrating
the old two inline jobs to four delegated workers. The
[first release-payload failure](producer-release-first.json.gz) retains the
old empty-Rust-payload predicate and its actual 41-test failure classification.
That predicate now requires and verifies both child artifacts. The reader keeps
these inert byte records; it never executes historical scripts or commands.

The current implementation verifies the exact child report bytes, selected and
omitted commands, source/run identity, tool/native/compiler bindings and the
unchanged corpus profile. Hosted workers run the two complete selections on
separate runners; stable required checks and scoped release readiness require
both actual artifacts. Synthetic mutation and file-I/O tests do not establish
hosted speedup, real Rust/native case execution or release readiness. The final
candidate still needs complete hosted validation and review.
