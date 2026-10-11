# Finite static Nat table baseline

This informed first-source study precedes implementation of #63's provisional
static-only `[Nat; length]` result category. The contract is recorded in
[Issue #63 comment 6015308541](https://github.com/MGYamada/Qleisli/issues/63#issuecomment-6015308541).
[Context](context.md), [initial predictions](predictions.json) and the
[session](session.json) preserve original sources, hashes and raw observations.

The first fifteen projects produce thirty actual CLI results: the scalar
control passes selected-source checking and encounters unsupported finite
static-if lowering; fourteen array/generator examples fail parsing on each
route. Parser refusals of counterexamples do not establish their intended
index, staging or cycle rules.

Four complete source repairs precede eight more checks. The scalar control
removes unsupported finite branching and passes both paths. The three quantum
examples replace an invented preparation API with real imported init0, h and
measure_z names; the first parser barrier had not diagnosed those name errors.
These repaired array examples still fail parsing. Both attempts and every raw
result remain unchanged. No native invocation count was instrumented.

The CLI digest is stable before/after each observation, and source hashes are
checked before and after execution. The selected kernel digest identifies an
existing build; these observations do not rebuild/audit/replay Lean. All sources
were frozen before their checks and before production-code changes.

Implementation, independent supported Z/S/T phase/reference checks, generic
index premises, deterministic lookup normalization and aggregate budgets remain
to be verified. Source preservation, wider QS/PR/quantitative RS/EXACT duties,
Issue completion and release approval are separate. Generic QFT delivery remains
outside this goal; no new maximum-size program is generated or checked.
