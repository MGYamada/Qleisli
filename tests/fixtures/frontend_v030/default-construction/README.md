# Explicit construction and the 0.3.0 Default boundary

The [ordinary #79 decision](https://github.com/MGYamada/Qleisli/issues/79#issuecomment-6009973288)
excludes Rust-like Default for every live quantum-containing runtime type,
including nested owners, `Q<Unit>` and `Q<Bits<0>>`. Ordinary/static data
construction stays distinct from explicit quantum preparation. The language
admits no trait/impl/associated-Default resolution path; this is an exclusion,
not a claimed implementation of future trait checking. An ordinary checked
function named `default` remains legal and retains its body's actual effects
and ownership obligations.

The source baseline is local `294643d02ad62e4c1ffc58d6ce51c5be838bc815`.
The [before observation](observed-before-01.json) binds original body, Reference
and VM22 inventory bytes before this unit. Production changes exactly one
unresolved-default explanation string, mentioning zero-width/nested owners.
It inspects no arguments and changes no condition, code, original span,
successful path, work limit, primitive or native acceptance rule.

## Original criteria and concrete evidence

All six original #79 conditions remain in force.

| Original condition | Evidence in this unit |
| --- | --- |
| Default status of live Q<T> is explicit | Adopted ordinary exclusion and the [Reference](../../../../docs/src/reference/rust-boundary.md#explicit-construction-instead-of-default). Actual default() source refusals cover ordinary, quantum, empty and nested return types. |
| Classical/static values versus quantum initialization | Literal/ordinary helper positives and explicit Iso preparation controls; no ordinary value implicitly becomes a quantum owner. |
| No silent quantum resources through generic traits | No Default trait facility is admitted. An unused generic Basis body using default() rejects; a resolved generic identity helper retains common checking and selected elaboration. Future traits are not claimed implemented. |
| Explicit clean ancilla effects/resources | Actual init0 preparation retains Iso, including through a caller; false Unitary claims reject. Existing scoped cleanup and general clean/dirty/quantitative obligations stay separate; no hidden Default workspace is introduced. |
| Q<Unit> covered | Explicit unit/finish remain Unitary, coefficient +1, zero physical wires and fresh linear owners. Retained exact native/scalar/reference tests and source owner-loss controls cover this distinction. |
| Diagnostics/docs explain the difference | Conditional compiler explanation, Reference examples, exact-span refusals and the separate public before/after source study. External qlippy is omitted under explicit maintainer permission. |

## First predictions, real failures and correction

The independent [prepared test](prepared-01.rs.txt) and
[plan](prepared-test-plan-01.json) were saved before compilation. Four new
tests contain 16 refused and five common-valid source controls. The first
actual latest/MSRV runs each had three passing tests and one failure: the
generic identity helper was incorrectly expected to pass finite lowering.
The existing finite static-type-argument limitation rejected it at bytes
84–93. Cargo stopped before the other requested test binaries.

The [separate test correction](test-profile-repair-02.json) and its exact
snapshot retain that same source. It now checks common Unitary facts and
selected elaboration, and explicitly asserts the finite unsupported category,
message and original span. No finite capability is added to satisfy the test.
Both original failed streams remain unchanged. A prior incorrect absolute
rustup path never started Cargo; the separate
[launch observation](validation-01/msrv-launch-error-01.json) records the
operator error and original empty streams. It is no compiler/test failure.

## Actual validation and scope

- Latest Rust 1.98.1 and MSRV 1.85.0 each passed 20 tests after correction:
  four new Default tests, twelve retained exact Unit-map/native/reference
  tests and four retained disposal-diagnostic tests. No selected test was
  ignored. The original failed runs remain separate.
- All-target Cargo Clippy with `-D warnings` passed for both toolchains.
  Format and explicit CLI build passed using reused bounded targets and two
  build jobs; this is no full all-target runtime or package validation.
- The [independent informed study](../../authoring_sessions/default-construction-v030/README.md)
  preserves six unchanged complete first projects and 30 actual CLI calls,
  with zero source repairs. Exits, codes, spans, non-message data and three
  successful outputs agree. Only the generic default refusal's two matched
  observations change; the other thirteen pairs retain both streams exactly.
  Its selected default renderer's legacy JSON body is recorded honestly.
  The zero-wire scalar observation retains exp(i*pi/4), producer-consistency
  and `source_meaning_verified: false`; numerical output is supplemental.
- mdBook 0.5.4 and rendered inspection passed: 28 HTML files, 1,156 local
  links and 434 anchors, including print. Authoring integrity passed with
  42 records, 57 snapshots and 983 observations without replaying commands.
- Reviewed VM22 source refresh changes only the body's digest and preserves
  the original inventory. Constructors, capacities, boundaries and public
  surface stay unchanged. Continuity passed against trusted
  `faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`.

The [independent advisory review](independent-review-01.json) distinguishes
root/observer results from its own read-only work. Command argv, actual exits,
timings, environments and raw stream hashes remain in [validation](validation-01/).
Original source/test predictions are not rewritten as successful results.
The fixed after CLI is identified in [its local byte record](after-cli-01.json);
it is not an authenticated complete build closure.

The first VM29 coverage check failed on the current inventory fingerprint.
The [separate reviewed identity correction](production-identity-refresh-01.json)
changes only that fingerprint, preserving every route, gap, authority and proof
status. Its new check passes. The earlier #68 coverage PASS preceded the final
VM22 refresh and did not check that sealed packet; the original PASS and this
unit's first FAIL remain preserved. Neither result is rewritten.

No fresh local Lean build/audit/replay, broader QS/PR/quantitative RS/EXACT
discharge, source-preservation theorem, future trait facility or new clean
capability is claimed. The two admitted ordinary QLV1 guarantees keep their
exact scopes and premises. Generic QFT and maximum-size work remain excluded.
Public full CI still checks f508; its distribution lane failed with redirected
inner logs under investigation. This local unit does not establish full CI,
package/install/bundle readiness, release approval or publication.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
