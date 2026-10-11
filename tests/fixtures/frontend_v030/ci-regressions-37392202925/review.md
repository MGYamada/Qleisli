# Read-only repair review

Scope: the exact working-tree edits to `src/frontend/check/body.rs`, `tests/project.rs` and `tests/unit_patterns.rs`, reviewed after the actual CI failures. No tests, builds, native calls or workflow control were performed by this reviewer. This is ordinary technical review; it adopts no interpretation or guarantee.

No blocking correctness issue was found in these edits. Test success remains to be established by the integrating agent.

The common pattern adapter now emits "empty pattern requires ordinary Unit" only for arity zero. Its nonempty tuple diagnostic, type error category and original span remain unchanged. The shared `Type::pattern_fields` still permits the empty pattern only for ordinary Unit; quantum ownership, equal-width products and Bits<0> are not reclassified. The change restores the specific explanation without altering acceptance.

The existing deep-cycle test still constructs the same 3,000 modules and uses the same 2 MiB loader thread. It now checks successful import-only loading, all local modules, and the final back edge's canonical module/name/local origin and exact UTF-8 use span. This matches the [current source Reference](../../../../docs/src/reference/source-text.md), which permits import-only cycles and rejects checked recursive dependency cycles. The tiny import-only test and independent real call-cycle rejection test remain present. This review does not claim the loader check executes or proves the bodies.

The new Unit-pattern regression reuses four existing counterexamples: Q<Unit>, Bit, (Unit,Unit), and Bits<0>. It checks the common selected and finite paths' diagnostic category, identical message and identical original span. The finite path receives an absent native executable and must return the source type diagnostic, so the test detects a premature child invocation or transport failure. No positive acceptance or native proof is inferred from these rejections.

Reviewed file identities (SHA-256 at this review):

- `src/frontend/check/body.rs`: `35a55058006bc9f9e7750f6f5d12041e6860ff609e77a12123df4c49c71ba3c3`
- `tests/project.rs`: `5c02c887115d0f437e993130eb101417dd8d1610703e2cb686165014c391e4a6`
- `tests/unit_patterns.rs`: `c48703cea7f971dcc35f95239a7ad3f875914a68bd5dd683b2e9b820446fedfd`

These identities bind this small code review, not a release closure or completed gate. Formatting or later edits require the integrator to assess the final diff. Broader QS, PR, RS and EXACT obligations and the admitted scoped guarantees are unchanged.
