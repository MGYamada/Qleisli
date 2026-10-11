# Independent Unit map tests

The first draft of `tests/quantum_unit_maps.rs` is retained in
`first-test.rs.txt`, with its pre-execution identity in `first-test.json`.
`independent-expectations.json` was written before inspecting any emitted
candidate or running the new tests. Its equations are the independent oracle:
introduction and elimination have coefficient +1, both round trips preserve
all coefficients, a retained eighth phase gives omega, two give i, and a
controlled fourth power gives Z on the control. Exact requested equations and
actual numeric execution are separate checks.

The six sources in `current/` are new, explicit translations or probes. The
scalar sources inline the work from the original `scalar-argument` study to
isolate argument evaluation and permit a small fixed external request. They
are not replacements for the original helper-call source, which remains
independently parsed and elaborated. The middle-owner source tests two physical
owners with an intervening zero-axis owner. The observation source retains its
readout and applies structural Unit maps after it; the original effectful
argument source still exposes the existing dropped-readout limitation. The
two-fresh-owners source distinguishes copying ordinary Unit from duplicating a
linear quantum Unit owner.

The request serializer contains only the specified constructors and exact
coefficients. Initial port labels and call/frame placement were derived by
reading the existing lowering interface, not by importing a candidate's
comparison request. This is a bounded structural request in the existing
native equation profile, not a general equivalence decision procedure. Any
subsequent correction of a transport label must preserve the first draft and
be recorded separately from the mathematical expectation.

Every reference execution uses dimension two and an arbitrary complex joint
vector. The system coordinate is the low-order index; the controlled oracle
changes exactly the odd system labels within each reference block. The largest
case has two system qubits. No separability or normalization assumption is
used. The wrong-scalar cases update both the finite program and its own claimed
meaning, first require actual native acceptance of that changed artifact, then
require rejection by the unchanged independent request.

Grouped first-study negatives stopped at the absent imports in the historical
binary. The new tests isolate all their distinct declarations, including both
wrong quantum bases, all four runtime arities, both static arities, revival,
duplication, loss, wildcard loss, unused invalid code and a zero-iteration body.
Additional same-width ordinary Bits and product cases remain separate.
Successful generic checking is never reported as successful lowering.

The public preparation validator first binds a checked payload to its retained
proposal. The integration test validates actual Unit/Finish source events and
instrument action; it cannot replace the private proposal payload to exercise
a same-payload forged node/event pair. That stronger internal matcher test is
separate. Raw Unit maps and packaged quantum tuple unitors remain explicit
unsupported capabilities. These tests are not a source-preservation theorem,
a new guarantee admission, full QS/PR/RS evidence or a release result.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
