# Retired operation spellings

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Issue [#33](https://github.com/MGYamada/Qleisli/issues/33), based on
`0f701cf77308fb2f5d1c2f40c749cf2daabc86ba`. The production parser refuses
`adjoint(U,q)`, `repeat_op(k,U)` and `repeat_static(k,U,q)` at the original
constructor token, suggesting `inverse(U)(q)`, `power(U,k)` and
`power(U,k)(q)`. AST/Core/IR interfaces and native acceptance remain intact.

The [source map](source-map.json) selects 52 individual current files and four
project inventories, preserving every original source and preceding migration
link. Only the three complete operation forms change; independent expectations,
first diagnostics, artifacts and licenses remain in their original locations.
These are current regression inputs, not new corpus algorithms or QFT work.
The existing independent Python proposal parser retains historical syntax for
historical comparison only; it cannot issue production acceptance.

The first focused run found one unmigrated source in the preservation tests and
a sandbox denial of process-status inspection. After the source repair and
execution outside that sandbox, library tests passed, but the operation suites
exposed the direct literal-power migration gap recorded in
[the before-code refinement](https://github.com/MGYamada/Qleisli/issues/33#issuecomment-6057358194).
The canonical AST retains its complete operation/count/input spans. Direct
literal named repetition now shares the existing finite lowering and checks
its original function even at zero count. General operation providers retain
their separate contracts; no primitive provider capability is added.

[source-review.json](source-review.json) records individually reviewed source
pins, unchanged public signatures/capacities and the scoped implementation.
The [runtime-group probe](runtime-group-probe/observations.json) preserves a
second regression found in review: literal repetition accidentally used the
unary checker for an ordinary two-owner function. Before/after CLI observations
retain the initial missing-manifest refusals and the real source-check failure.
The repair keeps the established complete-group judgment and applies the added
sealed-gate path only to a resolved primitive. A small independent Z/H action
test retains phase with external references for powers 0/1/2; repeated owners,
wrong tuple shape, classical inputs and an observing body still reject at zero.
See the [before-code repair record](https://github.com/MGYamada/Qleisli/issues/33#issuecomment-6057741977).

The first failed runs remain failures. Before the group repair, focused tests
passed 68 cases on latest Rust and 150 on MSRV (three existing ignores); both
all-target Clippy checks passed. Shared source-integrity passed 5/5, source
contracts 9/9, source semantics 3/3 (including the unchanged 96-case seed and
independent oracle), and fixed-version Book checks 3/3. After the repair, the
three affected Rust suites passed 45 tests with five existing ignores and the
original CLI source succeeded. Full Rust/MSRV, the unchanged 4,000-case
ownership suite, final semantic checks and exact-commit CI remain pending at
this recording point. No general source-preservation proof, new guarantee or
full #33 closure is claimed.

The subsequent latest all-target run passed the unchanged 4,000 ownership
cases in 377.34 seconds, then found three failures in `quantum_unit_maps`:
its local reader bypassed current source selection and opened the preserved
`controlled-four` source with `repeat_op` directly. One additional derivative
and the common reader repair retain all independent Unit equations, phase,
reference and false-provider checks; the 12-test suite then passed. The failed
full run remains unsuccessful, and final all-target validation is still needed.

Both subsequent declared full Rust runs passed the 4,000 ownership cases
(365.02 / 366.48 seconds), then failed a local-name diagnostic expectation in
`review_v027`. A 34-target diagnostic reached the remaining integration suites:
258 tests passed, one `source_scope` expectation failed and 15 existing tests
were ignored. Both tests expected legacy repetition text after conversion to
canonical `power`. The [unchanged canonical source comparison](local-name-diagnostic.json)
confirms identical before/after error code, text and byte span. Only those two
expectations changed; both repaired suites then passed 10 tests on each actual
toolchain. This does not turn the failed complete runs into successes.

The [bounded migration comparison](migration-comparison.json) checks the
preserved complete two-qubit study on both binaries: fresh source checks pass
and actual proposed artifact bytes agree. Its [first command refusal](migration-comparison-first-refusal.json)
preserves the missing output-option failure. The earlier source checks are
fresh native decisions; emitting a proposal is not acceptance authority or a
general preservation proof.

[validation.json](validation.json) records command counts and exact working
input bindings. Latest/MSRV lint and research groups passed 4/4 and 3/3;
source-integrity passed 5/5 after the diagnostic repairs. The first native
runner invocation refused the dirty checkout and executed neither selected
task. That gate remains intact; a clean local commit is required before those
comparisons. Final declared Rust runs, native client checks and exact-commit
hosted CI remain pending at this recording point. Concurrent ownership timings
are observations, not a controlled speedup claim. Completion is 24/111
(21.62%); no Issue or constitutional obligation is completed by this record.

Hosted run [37771955859](https://github.com/MGYamada/Qleisli/actions/runs/37771955859),
attempt 1 at `2aada2a1`, failed only the `lean-raw` native comparison; the other
65 native tasks and seven other real producer jobs succeeded. Its source
reader bypassed current-project selection and parsed a historical `adjoint`
input. The [repair review](raw-reader-repair.json) retains that failure and the
local reproduction. The repaired reader keeps all original circuit dependency
bodies, independently compares their meanings, and separately native-checks
the complete original QIRF. Ten small adapter regressions cover selection,
dependency substitution, root, phase, axis order and nonterminal readout.
The focused dirty-checkout native comparison passed 121 cases, 104 Rust
comparisons, 85 rational matrices and 180 raw traces. Exact-commit native and
hosted validation remain pending; the failed run has not been rerun or replaced.
Issue #45's newer `adjoint`/capability naming decision also remains to be
integrated before #33 can close. Completion remains 24/111 (21.62%).
