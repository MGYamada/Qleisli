# Explicit predicate-domain migration

This is a source migration record for [Issue #25](https://github.com/MGYamada/Qleisli/issues/25),
not a new intake or authoring benchmark. It changes six existing finite kernels
to take one explicit domain value in predicates used by `with_computed`.
Their complete two-file projects are retained under `sources/`. The semantic
fault replacing majority by parity remains an intentional fault with the same
new predicate interface; it is checked separately by the semantic runner.

`migration.json` links each file's last historical authoring identity to the
exact migrated source at commit `18f55693e31585dde67eeddeb064e77c138f9a57`.
All original session JSON, snapshots and observations remain unchanged. This
record continues those histories; it does not edit their last attempts.

`initial-validation/` preserves six failed corpus-run attempts. Each stopped
at the original requirement that active sources equal their latest historical
authoring snapshot, before semantic probes ran. The correction introduces an
explicit ordered migration chain, with complete project snapshots and observed
checks bound to their hashes. Missing records, stale predecessors, altered
snapshots, and incomplete or contradictory observations are rejected.

`check-context.json` was saved before checking the six projects with the frozen
compiler and native kernel; `checks.json` retains their actual arguments,
source identities, output and exit status. All six native source checks pass.
These checks establish source acceptance only. The separate semantic replay
uses the existing independent complex oracle, ordinary bounded probes,
rejection cases and the matching intentional fault. It does not add maximum
size inputs, change reference semantics or execute upstream frameworks.

The enclosing corpus manifest supplies edition `2026`. Original notices and
licenses remain in every copied source; no upstream input was changed.

## Validation

The six semantic replays pass 452 probes, four distinct rejection cases and
one type-correct majority/parity fault calibration. Metadata checks cover all
87 finite cases. The initial validator suite passes 55 tests; its final
15-test migration subset includes one additional alias-path regression.
`validation.json` records the commands, scope and independent review.

`semantic-replay/` preserves all first corrected runs. The phase-lock run
completed its 220 probes but correctly rejected a concurrent validator edit
made by the root agent. `validation-source/` retains the exact initial and
final validator bytes. `phase-runtime-omitted/` records a retry that omitted
the required native runtime setting and failed before probing.
`phase-native-retry/` contains the successful final retry with explicit runtime
selection and unchanged input hashes. None of these failed attempts is
relabelled as success. The final validator only adds rejection of duplicate
canonical path aliases; the semantic oracle is unchanged.
