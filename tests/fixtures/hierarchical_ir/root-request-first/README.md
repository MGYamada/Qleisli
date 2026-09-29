# Independent requested-root first sources

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

These are informed implementation/proof records for the
[bounded packet](../root-request-packet.md), not a controlled authoring benchmark.
`Root.lean.txt` and `HierarchicalRoot.lean.txt` retain the initial pure checker
and mathematical proof attempts. The first and second mathematical build logs
record namespace/overload ambiguity, dependent option equalities and simplifier
failures. The third kernel log records an unavailable `not_lt` lemma. Repairs
use explicit namespaces, a reference-free rendering function applied after
constructor matching, and `Nat.le_of_not_gt`. No new axioms, native proof
decisions, assumed whole-graph environment or weakened contract were introduced.

The Rust host, request producer, host tests, `Protocol.lean` and `Main.lean`
snapshots were saved before the first complete native host test run. That run
passed 12 cases and failed the requested-cycle diagnostic assertion: the
proposal producer reported `contract` through a child-arity mismatch before
checking the requested table's cycle. This paragraph records the observed
diagnostic summary, not a full preserved terminal log. The repair validates
the request's dependency schedule before proposing pairs, yielding `invalid_ir`.

The final [native root report](../root-request-native.json),
[fresh host report](../root-request-host.json),
[Rust checks](../root-request-rust-validation.json) and
[rebuilt proofs/audits](../root-request-registry.json) record the corrected run.
Independent handwritten binary mutations bypass the Rust producer, including
bad pair graphs, uncovered requested nodes and aggregate work exhaustion.
