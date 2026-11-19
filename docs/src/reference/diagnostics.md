# Diagnostics and recovery

A **diagnostic** reports one failed check on a source program, a project or an
artifact. It identifies the failed premise, explains the local rule and, where
one exists, describes a correction that preserves the intended semantics. An
author starts from the rejected expression and its diagnostic, revises the
program, and submits it to the same checker.

A diagnostic describes a failed check. It is not evidence. An accepted handle,
a realization claim or a resource claim requires its own successful check on
the source or artifact that the claim names.

This chapter covers the diagnostics of the `qleisli` CLI for edition 2026: the
two routes that produce them, their JSON form, their codes, and the guidance
that each language boundary gives.

## Routes

The CLI checks source through two routes. Both use the common checker. They
differ in the codes and the locations that they report.

| Route | Commands |
| --- | --- |
| **Project route** | `qleisli check`, `run`, `sample` and `emit-ir` on a source root |
| **Selected-entry route** | `qleisli check`, `run`, `sample` and `emit-proposal` with `--entry=MODULE::FUNCTION` and `--module=NAME=PATH` |

The sections below state each difference where it applies. A consumer that
handles both routes must not assume the fields or the codes of one route on the
other.

## The result envelope

With `--format=json`, a command writes one `qleisli.result` version-1 object:

| Field | Value |
| --- | --- |
| `format` | `"qleisli.result"` |
| `version` | `1` |
| `command` | The command name |
| `outcome` | `"ok"` or `"error"` |
| `diagnostics` | An array of diagnostic records |
| `result` | The command's result, or `null` when `outcome` is `"error"` |

Rules:

- When `outcome` is `"error"`, `diagnostics` holds the one error that stopped
  the command.
- When `outcome` is `"ok"` on the project route, `diagnostics` holds the
  warnings of the run, each with severity `"warning"`. It may be empty.
- On the project route, the process exits with status 2 for the code `usage`
  and with status 1 for every other error.

## The diagnostic record

A diagnostic record has these fields:

| Field | Value |
| --- | --- |
| `code` | A stable category. [Codes](#codes) lists them. |
| `severity` | `"error"` or `"warning"` |
| `message` | Explanatory text for the author |
| `primary` | The [location](#locations) of the failure, or `null` |
| `related` | An array of related notes |

A record may also carry `counterexample`, `ownership_boundary` or
`control_flow_boundary`, as [Refinements](#refinements) describes.

Use `code` and the structured fields for automation. Render `message` for the
author. The text output and the JSON output of a command describe the same
failed rule.

Rules:

- A source diagnostic of the project route has an empty `related` array.
- An artifact diagnostic, such as one from `verify-ir`, has `primary` equal to
  `null`. Its `related` array holds one note whose `message` is
  `json_pointer: ` followed by the pointer into the artifact, and whose
  `location` is `null`.
- A selected-entry diagnostic has an empty `related` array, or one such
  pointer note.

## Locations

A location names the original source bytes of the failure. Its fields depend on
the route.

| Field | Project route | Selected-entry route |
| --- | --- | --- |
| `path` | The file, relative to the source root, with `/` separators | The file, or `null` |
| `module` | Absent | The module name, or `null` |
| `start`, `end` | The half-open byte span in the original source | The same |
| `line`, `column` | One-based coordinates of `start` | Absent |

Rules:

- `line` and `column` count Unicode scalar values. A CRLF pair counts as one
  line break.
- On the project route, a file of the bundled standard library has a `path`
  that begins with `std://`.
- On the project route, a location whose file has no label relative to the
  source root is not reported. The record then has `primary` equal to `null`
  and the code `project`.
- On the selected-entry route, `path` comes from the `--module` binding of the
  module where the failure does not name a file itself. It is `null` when
  neither names one.

> **Implementation note.** The selected-entry loader reports the original byte
> span of a failure and no line or column. The CLI does not reread the file to
> compute them.

## Codes

The common checker classifies each source failure. The project route maps that
class to its closed version-1 vocabulary. The selected-entry route reports the
class with three spellings merged.

| Common checker class | Project route `code` | Selected-entry route `code` |
| --- | --- | --- |
| `name` | `unknown_name` | `name` |
| `binding` | `ownership` | `name` |
| `shadow` | `type_mismatch` | `name` |
| `cycle` | `recursive_call` | `cycle` |
| `arity` | `arity` | `arity` |
| `static-arity` | `arity` | `static` |
| `type` | `type_mismatch` | `type` |
| `size` | `type_mismatch` | `size` |
| `static` | `type_mismatch` | `static` |
| `ownership` | `ownership` | `ownership` |
| `effect` | `effect` | `effect` |
| `access` | `capability` | `access` |
| `contract` | `contract` | `contract` |
| `unsupported` | `unsupported` | `unsupported` |
| `limit` | `limit` | `limit` |
| Any other class | `project` | The class, unchanged |

The project route also reports these codes outside the common checker:

| Code | Failure |
| --- | --- |
| `parse` | The source does not match the grammar |
| `project` | A missing or incompatible manifest, edition or source file |
| `invalid_entry` | A missing or unsuitable entry function |
| `invalid_ir` | IR that fails a structural check, or that the native checker rejects |
| `simulation` | The reference simulator refuses the program, for example because it is not closed |
| `usage` | An invalid command line |

Rules:

- The project route reports a native setup or transport failure, such as a
  missing checker executable, with the code `project`.
- The selected-entry route applies no such mapping. A missing checker
  executable there has the code `io`.
- Target operations may report `unsupported` and `limit`. The command and the
  reported profile identify the target restriction.

> **Implementation note.** `source_error` in `src/frontend/compile/mod.rs`
> holds the project-route mapping, and `v1_code` in `src/bin/qleisli/json.rs`
> maps setup failures. The conversion from the common checker's error in
> `src/frontend/specialize.rs` merges the three spellings of the
> selected-entry route.

## Refinements

Three optional fields refine a record where the checker identifies the source
rule or a concrete witness.

| Field | Content | Routes |
| --- | --- | --- |
| `counterexample` | `input_column` and `output_row`, the coordinates of one entry where an exact equation fails | Project route and artifact diagnostics |
| `ownership_boundary` | `boundary` is `"affine_to_linear"`; `reason` and `applies_to` are as below | Both |
| `control_flow_boundary` | `boundary` is `"classical_quantum_control"`; `reason` is as below | Both |

The `message` of a record with a `counterexample` gives the basis labels and
the exact coefficients.

| Field | `reason` values |
| --- | --- |
| `ownership_boundary` | `unresolved_disposal`, `implicit_quantum_disposal`, `clean_workspace_return`, `dirty_workspace_return`, `computed_workspace_return` |
| `control_flow_boundary` | `if_condition`, `qif_control`, `match_selector`, `qmatch_selector`, `for_carry`, `qfor_carry` |

In an `ownership_boundary`, `applies_to` is `"if_live_quantum_owner"` for the
reason `unresolved_disposal`, because the checker inferred no argument type. It
is `"live_quantum_owner"` for every other reason.

## Guidance by boundary

The code, the command, the location and the message together identify a
failure. The guidance describes the corrections that are available. The
table gives the project-route code first, and the selected-entry code where it
differs.

| Boundary and codes | Guidance |
| --- | --- |
| Source form (`parse`) | Show the recognizable local grammar and the original byte span. Invented statements such as `qlet` and `qreturn` can point to ordinary `let` and the block's tail expression. A rewritten example undergoes the name, type, effect and ownership checks like any other source. |
| Project and names (`project`, `unknown_name` or `name`, `invalid_entry`) | State the missing or incompatible manifest, edition, entry or binding. Resolve the declared source identity and use the canonical primitive or checked library path. A derived operation is defined in checked `.qli`. |
| Interface and calls (`type_mismatch` or `type`, `arity`, `recursive_call` or `cycle`) | Identify the required and the supplied interface where available. Regroup a quantum product only when its leaf types and order agree, and thread existing owners through the corrected call or carry. Calls must meet the applicable finite termination rules. |
| Ownership and access (`ownership`, `capability` or `access`) | Identify the live or consumed owner, or the access obligation. Use the owner returned by the consuming operation, or supply the documented access mode after checking its premise. Preserve linear accounting even for a zero-width owner. An unresolved disposal spelling gets conditional guidance about a live quantum owner. |
| Workspace return (`ownership`, `contract`) | Explain the missing return role or the checked restoration equation. Return the clean scratch at zero, restore dirty scratch including its relationship with the reference, or return the owners that `with_computed` requires for checked uncomputation. |
| Effects and observation (`effect`, `type_mismatch` or `type`) | State the body or callee effect and the assertion that it exceeds. For ordinary control on a measurement result, use explicit observation in an `observe` context. For coherent control, retain the quantum selector, the checked arms and the phase. |
| Exact equations (`contract`, `invalid_ir`) | Identify the rejected equation. Where the check yields a concrete witness, show exact coefficients and label input and output in the declared basis order. Investigate phase, axis order and the dependencies of the checked artifact. |
| Realization eligibility (`unsupported`, `limit`) | Name the requested target and the failed premise where known. Retain the closed instance and the available source origin. An unsupported synthesis profile or an insufficient target width describes a restriction on realization. |
| Work and resources (`limit`) | Identify the bound, for example source capacity, exact checking work, or a gate or workspace budget for a target artifact. Use the command and the profile to distinguish these scopes. A checked resource count applies to the artifact that was counted. |

An outer construct may add guidance to a diagnostic. It keeps the original
cause and location.

See [parser and control guidance](source-text.md#parser-guidance-for-surface-syntax),
[effect assertions](source-text.md#ordinary-function-effects-and-assertions),
[ownership and workspace examples](rust-boundary.md#conditional-teaching-diagnostics)
and [realization diagnostics](realization.md#current-production-status-and-diagnostics).
The [primitive boundary](primitive-boundary.md) and
[qrate contracts](packages-and-artifacts.md) give the corresponding source and
compatibility rules.

## Conformance cases

The index in `tests/fixtures/authoring_sessions/README.md` points to the
preserved first sources and their diagnostics. Regression tests exercise the
sources and their corrected variants. The suite checks codes and positions in
addition to the wording.

| Retained case or obligation | Conformance checks |
| --- | --- |
| Invented quantum statements and malformed `qif`, `qmatch` or `qfor` headers | `tests/parser.rs` and `tests/cli_json.rs` check the recognized local grammar and the original locations. |
| Ordinary and coherent conditions, selectors and carries | `tests/cli_json.rs` checks boundary reasons and rechecks legitimate corrections with explicit observation or returned owners. |
| Moved or duplicate owners, unresolved disposal and missing workspace return | `tests/authoring_ergonomics.rs`, `tests/exclusive_access.rs`, `tests/rust_boundary_diagnostics.rs` and `tests/cli_json.rs` verify linear ownership, disposal conditions, and clean, dirty and computed return roles. |
| False effect assertions, ordinary inspection of owners and wrong register shape | `tests/body_effects.rs`, `tests/repair_diagnostics.rs` and `tests/cli_json.rs` check the effect cause, the ordered types and the source location. |
| Phase or permutation counterexample and numerical residue | `tests/cli_json.rs` checks exact labels and coordinates. With `tests/sim.rs`, it checks bounded exact-zero annotations and preservation of numeric outcomes. |
| Source limits, target resource capacity and unsupported realizations | `tests/repair_diagnostics.rs`, `tests/interop.rs` and `tests/cli_json.rs` check source and target limits and locate refusals in the original specialization. |
| Primitive paths and qrate edition | `tests/repair_diagnostics.rs` rechecks canonical replacements, and `tests/editions.rs` checks explicit manifest selection and refusal of unsupported editions. |
| Selected-entry locations and setup failures | `tests/selected_source_cli.rs` and `tests/checked_operations.rs` check the selected-entry location fields and the `io` code. |

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
