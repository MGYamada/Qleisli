# Ordinary function parameter patterns

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

This unit implements the parameter-pattern contract recorded before changes in
[Issue 32](https://github.com/MGYamada/Qleisli/issues/32). One typed source
parameter remains one argument and one whole input tree. The common parser and
finite/sized binders admit exact Unit/product/name/wildcard patterns. Wildcards
discard only unrestricted ordinary values, including in sized let/fold bindings.
Quantum-containing values retain linear ownership, including zero-width owners.

The [first study](../../authoring_sessions/runtime-parameter-pattern-v030/README.md)
retains source bytes, actual earlier CLI diagnostics and three emitted named
controls. It identifies the reused executable and its original build records;
no new checkout or binary copy was made. New source acceptance does not assert
that every earlier desired input was otherwise grammatically valid.

Both profiles keep parameter-list arity, the complete type tree, lexical IDs,
source/provider bindings, argument evaluation order and effects. Sized concrete
definitions retain the original whole input before binding its pattern. The
public derived Debug representation of sized parsed/instantiated programs now
shows a Pattern::Name wrapper around named arguments; it is not byte-identical
to the previous internal Debug view. Public input/type accessors and native
schemas are unchanged.

The production diff received independent review of shape, ownership, static
collisions, input identity and effect ordering. Tests separately inspect public
constructed ASTs, exact scalar interference and a two-dimensional reference
for small swap/provider actions. These tests are bounded evidence, not general
source preservation, universal reference theorems or new guarantee admissions.

## First actual validation and retained repair

The [first run](latest/result.json) compiled the changed code, then found four
failures in the newly authored test target. Some input declarations omitted
`static`; one operation constraint used the wrong Apply punctuation. Two tests
encountered the existing main-entry restriction before reaching their intended
effect/parameter check. Raw failures and the original source-manifest hashes
remain in `latest/`. Corrected inputs are separate derivatives, not replacements
for the first sources or diagnostic history.

Independent review also found an older false positive: a test intended to reject
ordinary parameter patterns still contained CBit. The
[explicit derivative map](current/ergonomics/ordinary_parameter_pattern/source-map.json)
retains both earlier hashes. The active test now checks the retired type error
specifically, and executes a canonical one-argument ordinary pair projection
over all four Boolean inputs. Its preparation-only map is distinct from the
later actual validation record.

## Completed bounded checks

- [Rust 1.98.1](latest-fixed/result.json) and
  [actual Rust/Cargo/Clippy 1.85.0](msrv/result.json) each pass 73 tests across ten
  selected integration targets plus two parameter-pattern library regressions.
  Focused Clippy with warnings denied and the CLI build pass on both. The
  230 selected source hashes are stable and identical between successful runs;
  unchanged additional fixtures remain bound by the recorded base commit.
- [CLI observations](cli-after/result.json) retain 50 actual calls: the 45
  original checks, two explicitly repaired static declarations and three
  emitted controls. All three unchanged controls produce byte-identical IR.
  Original missing-static sources still reject; their separate repaired
  versions reach the intended type/ownership behavior. Sized classical runtime
  and finite static-profile restrictions remain visible rather than counted as
  successful executions.
- [Metadata checks](metadata-validation.json) pass current source inventory,
  production coverage, authoring/edition/constitutional identity, formatting,
  native scheduler and documentation checks. mdBook 0.5.4 builds successfully;
  20 HTML files, 741 links and 266 anchors, including print output, are checked.
  The native schedule now contains 67 groups and 83 commands.

The shared target occupies approximately 552 MiB after both toolchains;
repository target remains about 13 MiB and available disk about 25 GiB.
The original failed run is separate from both successful records. No production
change was needed to correct those test-input failures.

## Scope and resource limits

Validation reuses one fixed `/private/tmp/qleisli-bounded-validation-target`
with incremental compilation and debug information disabled and two build jobs.
The existing native checker is reused; no Lean definitions changed in this unit.
There is no new Lean build/audit/replay, whole-tree source snapshot, maximum-size
quantum case or historical scratch deletion. Named controls compare actual IR
bytes; changed source-bound programs require semantic checks instead of claiming
the same artifact identity.

General Basis support, quantum Unit structural maps, complete checking/profile
convergence and the other 108-Issue requirements remain open. This unit neither
closes its parent Issues nor constitutes full CI or release approval.
