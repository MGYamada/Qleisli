# Diagnostics and recovery

These rules cover the current `0.3.0-beta` source and CLI diagnostics for
edition 2026. Diagnostics are part of the Qleisli language harness. At a
recognizable language boundary, a rejection identifies the failed premise,
explains the local rule, and describes an available correction that preserves
the intended semantics. Authors can start with the rejected expression and its
diagnostic, then submit a revised program to the same checker. Keep the original
cause and location when an outer construct supplies additional guidance.

## Source categories and guidance

The version-1 CLI uses these categories for source checking. The category,
command, location, and explanation together identify the failure. Guidance
describes the correction space for that failure.

| Boundary and codes | Guidance |
| --- | --- |
| Source form (`parse`) | Show the recognizable local grammar and original byte span. Invented statements such as `qlet` and `qreturn` can point to ordinary `let` and the block's tail expression. A rewritten example still undergoes name, type, effect, and ownership checks. |
| Project and names (`project`, `unknown_name`, `name`, `invalid_entry`) | State the missing or incompatible manifest, edition, entry, or binding. Resolve the declared source identity and use the canonical primitive or checked library path. In particular, a derived operation is defined in checked `.qli`. |
| Interface and calls (`type_mismatch`, `type`, `arity`, `recursive_call`) | Identify the required and actual interface where available. Regroup a quantum product only when its leaf types and order agree, and thread existing owners through the corrected call or carry. Calls must meet the applicable finite termination rules. |
| Ownership and access (`ownership`, `capability`) | Identify the live or consumed owner, or the access obligation. Use the owner returned by the consuming operation or supply the documented access mode after checking its premise. Preserve linear accounting even for a zero-width owner. An unresolved disposal spelling gets conditional guidance about a live quantum owner. |
| Workspace return (`ownership`, `contract`) | Explain the missing return role or checked restoration equation. Return the clean scratch at exact zero, restore dirty scratch including its relationship with the reference, or return the owners required by `with_computed` for checked uncomputation. |
| Effects and observation (`effect`, `type_mismatch`, `type`) | State the body or callee effect and the assertion it exceeds. For ordinary control on a measurement result, use explicit observation in an `observe` context. For coherent control, retain the quantum selector, checked arms, and phase. |
| Exact equations (`contract`, `invalid_ir`) | Identify the rejected equation. When exact equation checking yields a concrete witness, show exact coefficients and label input and output in the declared basis order. Investigate phase, axis order, and dependencies of the actual checked artifact. |
| Realization eligibility (`unsupported`, `limit`) | Name the requested target and failed premise where known. Retain the closed instance and available source origin. An unsupported synthesis profile or insufficient target width describes a restriction on realization. |
| Work and resources (`limit`) | Identify the bound being checked, for example source capacity, exact checking work, or a gate or workspace budget for a target artifact. Use the command and profile to distinguish these scopes. A checked resource count applies to the artifact that was counted. |

See [parser and control guidance](source-text.md#parser-guidance-for-surface-syntax),
[effect assertions](source-text.md#ordinary-function-effects-and-assertions),
[ownership and workspace examples](rust-boundary.md#conditional-teaching-diagnostics),
and [realization diagnostics](realization.md#current-production-status-and-diagnostics).
The [primitive boundary](primitive-boundary.md) and [qrate contracts](packages-and-artifacts.md)
give the corresponding source and compatibility rules.

## Machine-readable output

For source-checking commands with `--format=json`, the `qleisli.result` version-1
envelope includes `command`, `outcome`, `diagnostics`, and `result`. A source
diagnostic includes a stable snake-case `code`, a `severity`, an explanatory
`message`, a `primary` location or `null`, and `related` locations. A primary
location gives the file `path`, the original half-open byte span `start` and
`end`, and one-based `line` and `column`. Use the code and structured fields
for automation and render the message for the author. Text and JSON present
the same source rule and original location. The CLI reports native setup and
transport failures under `project` in JSON. The project route uses
`unknown_name` and `type_mismatch`. The selected-entry route can report `name`
and `type` at the same kinds of source boundaries.

`control_flow_boundary` and `ownership_boundary` refine the category when
the checker identifies the corresponding source rule. A concrete exact
`counterexample` includes numeric `input_column` and `output_row`, and its
message includes the basis labels and exact coefficients. Target operations
can use `unsupported` and `limit` as well. Use the command and reported profile
to identify the target restriction. A diagnostic describes the failed check.
An accepted handle or a realization/resource claim requires its own successful
check on the actual source or artifact.

## Conformance cases

The index in `tests/fixtures/authoring_sessions/README.md` points to the
preserved first sources and actual diagnostics. Current regression tests
exercise the sources and corrected variants under the supported grammar.
The suite checks categories and positions in addition to diagnostic wording.

| Retained case or obligation | Current conformance checks |
| --- | --- |
| Invented quantum statements and malformed `qif`, `qmatch`, or `qfor` headers | `tests/parser.rs` and `tests/cli_json.rs` check recognized local grammar and original locations. |
| Ordinary and coherent conditions, selectors, and carries | `tests/cli_json.rs` checks boundary reasons and rechecks legitimate corrections with explicit observation or returned owners. |
| Moved or duplicate owners, unresolved disposal, and missing workspace return | `tests/authoring_ergonomics.rs`, `tests/exclusive_access.rs`, `tests/rust_boundary_diagnostics.rs`, and `tests/cli_json.rs` verify linear ownership, disposal conditions, and clean, dirty, and computed return roles. |
| False effect assertions, ordinary inspection of owners, and wrong register shape | `tests/body_effects.rs`, `tests/repair_diagnostics.rs`, and `tests/cli_json.rs` check the effect cause, exact ordered types, and source location. |
| Phase or permutation counterexample and numerical residue | `tests/cli_json.rs` checks exact labels and coordinates, and `tests/cli_json.rs` with `tests/sim.rs` checks bounded exact-zero annotations and preservation of numeric outcomes. |
| Source limits, target resource capacity, and unsupported realizations | `tests/repair_diagnostics.rs`, `tests/interop.rs`, and `tests/cli_json.rs` check source and target limits and locate refusals in the original specialization. |
| Primitive paths and qrate edition | `tests/repair_diagnostics.rs` rechecks canonical replacements, and `tests/editions.rs` checks explicit manifest selection and refusal of unsupported editions. |

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
