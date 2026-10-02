# Issue regressions at v0.2.7

Curated reproductions of issues #207-#212 and #214, authored with the issue
reports and implementation visible. This is not an uninformed authoring/model
benchmark, a source-preservation proof or a production authority transfer.
The workspace already contained the v0.2.7 corpus, docs and native Lean work.

[Before](before.json) retains real failing test output and the original source
strings, including diagnostic paths. The #207 observation is an isolated replay
with only the old Tuple2 conversion restored after other host fixes; it is not
a clean checkout of the baseline commit. Inputs remain unchanged after repair.
Regression sources are [review_v027.rs](../../review_v027.rs),
[hierarchical_host.rs](../../hierarchical_host.rs), and the policy/corpus/CI tests
under scripts. The #210 tests use synthetic metadata in a temporary corpus copy;
they are not new upstream translations or licensing claims. Positive Pair/Unit/nested-tuple cases use independent identity
matrices, complex/reference inputs and complete QIRF1/2 bytes; wrong equal-width
trees reject. At most three quantum axes are generated in these new cases.

[Validation](validation.json), [native hierarchy](hierarchy-validation.json),
[named-QPE host faults](qpe-host-validation.json), [decoder comparison](decoder-validation.json)
and [rebuilt schema audit](schema-validation.json) are local observations,
not GitHub Actions results. Existing
release/VM-22 comparison artifacts and earlier VM-27 records remain untouched;
the current reviewed source inventory and registry binding are refreshed.
Rust production authority and all external schema gates remain unchanged.
