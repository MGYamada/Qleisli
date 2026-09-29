# First conditional-derivation sources and repairs

`Conditional.lean.txt` was saved before its first build. The initial theorem
statement needed explicit `Proof` and `Local` types for existential variables;
Lean could not resolve `.Valid`/`.requests` before those annotations. No checker
condition changed. The repaired module builds with its state, request-binding
and conditional-closure proofs.

`harness.py.txt` precedes the initial native run, retained in
`../conditional-native-first.json`. The native build/execution succeeded, but
comparison correctly exposed a too-late expected diagnostic: reversing the
two non-closed stages violates the exact starting owner interface, so typing
returns `invalid_ir` before equation matching. The nonidentity encoding test
initially named the non-closed leaf as its compute provider and was also
rejected structurally; it now names the actual closed enclosing definition,
so its type-correct unsupported encoding is rejected by the finite rule. The
repaired 42-case comparison passes, including zero-repeat retained obligations.

`HierarchicalFiniteEvaluation.lean.txt` precedes the mathematical extension's
first build. The [build output](evaluation-build.txt) records two duplicated
`body` arguments in simplification lists, rejected by warning-as-error policy.
Removing the duplicate arguments preserves that policy. The extended reader
and induction retain actual bytes and explicit leaf equations; they assume no
whole-graph interpretation environment and enable no production schema.
