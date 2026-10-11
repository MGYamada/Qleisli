# Body-derived effects and unsupported external justification

This ordinary implementation follows the before-code decision in Issue #315,
edition 2026, and the subsequent direct maintainer request for the diagnostic.
Annotations are checked upper bounds; they never seed inference or overwrite
the principal body effect. Facts grant neither arbitrary Meaning nor access or
constitutional discharge. The native Lean acceptance boundary is unchanged.

The shared diagnostic explains the actual supported semantic boundary:

```text
body effect `Observe` exceeds asserted `Unitary` effect of `f`.
Semantic error: "externally unitary" is not supported; an external unitarity
claim cannot override the effect inferred from the body
```

It contains no GitHub Issue reference. It does not assert that an independently
specified public channel is mathematically non-unitary. The unsupported part
is replacing ordinary compositional checking with an external certification.

## Sources and migration

- The authoring session `../../authoring_sessions/body-effects-v030/` retains
  twenty complete first projects and actual baseline/follow-up observations.
  The baseline rejected all twenty; unchanged first inputs later had fifteen
  successes through actual native checking and five rejections before native
  startup. Source/binary maps identify those particular observations.
- `stdlib-before/` preserves all four original stdlib files. `stdlib-audit.json`
  accounts for ten ordinary functions and three basis definitions. Only ten
  redundant runtime prefixes were removed; mathematical comments and every
  body byte are preserved. Sealed catalogs remain unchanged.
- `active-clients-before/`, `first-legacy-test/` and `first-profile-test/` retain
  the original tests. Their old annotation-inflation expectations migrate to
  principal effects. Real preparation/observation, owner/type/access, physical
  evidence and unsupported lowering negative checks remain covered. New
  positive checks ensure wide assertions do not artificially inflate callers.
- `inventory-before.json`, `coverage-before.json` and `inventory-review.json`
  record the reviewed untrusted metadata/API change. The new `FnKind.Inferred`
  constructor supplies ordinary syntax, not evidence. Immutable reports render
  their own retained source; the existing source-only documentation mode stays
  explicitly unverified.

## Actual checks and preserved failures

`summary.json` counts the recorded results without combining them into a
same-commit release certificate. The broad current suites passed 253 integration
and 57 frontend tests on each of Rust 1.98.1 and 1.85.0; eight integration and
two frontend tests remained ignored. No new maximum-size quantum case ran.

The first MSRV all-target lint run rejected a nonminimal boolean expression.
`assertion-predicate-review.json` records its equivalent simplification and
the single changed Rust file. Final `latest-fix`/`msrv-fix` maps bind the current
predicate: each reran 77 direct integration consumers and 57 frontend tests,
with three and two existing ignores, plus all-target Clippy. The broad earlier
results remain bound to their original source maps rather than relabeled.

`first-typecheck/`, `first-runtime/`, `first-diagnostic-tests/`,
`first-functional-tests/`, `first-module-test/` and the first validation folders
retain actual failures, including the initial omitted kernel environment and
new-test mistakes. Tool-decoded or summarized output is labeled accordingly;
the validation driver captures original stdout and stderr separately. Frozen
records are not edited to make tests appear to have passed initially.

`final-diagnostics/` retains actual text/JSON diagnostics from both current
profiles, with original source/binary maps and zero native invocations for the
false annotation. `checks/` records constitutional continuity against
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`, inventory/coverage, docs, fixed
mdBook 0.5.4 build and rendered links, formatting and tracked whitespace.

No fresh Lean replay was run: Lean definitions and both admitted QLV1
ownership/scope meanings/evidence were unchanged. Broader QS/PR/RS, EXACT,
source/runtime preservation, all required same-commit release validation and
the other 110-Issue criteria retain their recorded pending scope. There is no
new guarantee admission, publication, tag or externally certified escape hatch.
