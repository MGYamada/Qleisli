# v0.2.9 GitHub bug repair record

Bounded regressions recorded on 2026-10-04 JST in the unpublished v0.2.9
workspace. These repairs do not change Lean acceptance rules or establish
source preservation, full Soundness, a completed release, or stress recovery.

## Reproductions and disposition

| Issue | Repair and regression | Disposition |
| --- | --- | --- |
| [#257](https://github.com/MGYamada/Qleisli/issues/257) | Projection charges copied classical values, token maps, wire lists and axes before cloning; applies to run, sample, reset, discard and certified cleanup. Numerical tolerance excludes copy work. `tests/sim.rs::classical_projection_copies_share_the_execution_budget` uses 256 classical constants and four one-qubit observations. | Implemented; pending integration |
| [#258](https://github.com/MGYamada/Qleisli/issues/258) | Each active component receives only capacity left after retaining pending and completed siblings. Nested arms and multi-wire discard share this accounting. | Implemented; pending integration |
| [#259](https://github.com/MGYamada/Qleisli/issues/259) | One manifest parse per discovered directory with its own manifest; inherited editions reuse the checked parent. Bounded discovery allows `max(64, project_bytes / 1024)` entries, separately from byte limits. Unit instrumentation observes one local parse plus the bundled manifest. Iterative traversal holds only the active ancestor chain. | Implemented; pending integration |
| [#260](https://github.com/MGYamada/Qleisli/issues/260) | ASCII case-insensitive `target` rejection in every selected path component; mixed-case regressions do not depend on filesystem case sensitivity. | Implemented; pending integration |
| [#261](https://github.com/MGYamada/Qleisli/issues/261) | All text success paths use fallible stdout writes. A closed Unix socket verifies exit 1 with a diagnostic for check, run, sample, doc, emit-ir, verify-ir and sized emission. | Implemented; pending integration |
| [#262](https://github.com/MGYamada/Qleisli/issues/262) | Host runtime/setup failures map to `project` in the closed v1 JSON transport; internal library `io`/`kernel` codes do not extend it. All five source/artifact commands are covered. | Implemented; pending integration |
| [#263](https://github.com/MGYamada/Qleisli/issues/263) | Each item's comments render as isolated fenced text. Unterminated backtick/tilde fences, HTML comments and script tags cannot hide later signatures. | Implemented; pending integration |
| [#264](https://github.com/MGYamada/Qleisli/issues/264) | Impossible controls, axes and table dimensions return `InvalidCircuit`; actual step limits remain `Limit`. The original malformed raw CertifiedCompute scenario returns native `invalid_ir`. | Implemented; pending integration |
| [#266](https://github.com/MGYamada/Qleisli/issues/266) | Unix discovery, manifest reads and source opens use the selected directory handle. A deterministic swap between the two pathname checks rejects the replacement; a descriptor-relative read still retrieves the original bytes. Existing persistent/symlink cases pass. | Implemented for the documented Unix identity guarantee; pending integration |
| [#267](https://github.com/MGYamada/Qleisli/issues/267) | The earlier Lean-only migration already restored library-only checking. New text/JSON regressions cover an explicit checker and invalid unused declarations. | Confirmed repaired; pending integration |
| [#268](https://github.com/MGYamada/Qleisli/issues/268) | Finite and hierarchical transports share Unix process-group cleanup and nonblocking pipes, with no reader/writer threads. Long-lived descendants inheriting pipes are terminated after both parent exit and stall. | Unix repaired; Windows Job Object containment remains open |
| [#271](https://github.com/MGYamada/Qleisli/issues/271) | Function equation/type failures use `contract`; malformed/unbound IR retains `invalid_ir` and capacity retains `limit`. Text and JSON agree. | Implemented; pending integration |

All issues remain open until integration; no local repair is represented as
pushed, merged or published. #94 remains the broader typed-capacity refactor;
the inventory now records discovery and retained simulation/copy limits, but
does not claim every capacity has been typed. #275 and #278 retain their
explicit v0.3.1 TODO target. No maximum-size stress cases were newly generated
or executed. Non-Unix filesystem loading retains its existing trust assumption.
Unix process groups do not contain executables that deliberately escape them.

## Original bounded inputs

- `contract_mismatch/main.qli` is an executable negative study: the actual H
  operation differs from the specified identity. The saved JSON diagnostic
  identifies the exact column/row mismatch and original source span.
- `nested_ensemble/main.qli` is an executable positive study with independently
  expected classical result `true` at probability one. At the deepest branch,
  four active amplitude cells plus two retained outside components require six
  cells. A four-cell limit rejects; six cells and three components succeed.
  These are reduced reproductions, not upstream corpus translations or benchmarks.

## Validation

`validation.json` records command outcomes, source/binary hashes, artifacts and
limitations. Logs preserve intermediate failures as well as completed runs.

- A relevant Rust run covered 16 targets: **200 passed, 22 ignored**, with the
  process-tree test excluded because sandboxed `ps` was denied. The process-tree
  test passed separately with permission to inspect its own child processes.
- Five explicitly selected native-handle/path tests passed. The hierarchy test
  found an obsolete 67-unit Rust-verifier expectation; it now compares the budget
  with an independently invoked native finite leaf, and passed. Original
  shared-DAG, exact-byte and negative-phase assertions remain.
- Focused reruns cover the final source traversal, malformed raw circuit,
  sampling/copy accounting and simulation changes. `sim::` filters apply only to
  the library; integration suites were also run separately without that filter.
- Clippy passed for all targets with warnings denied. Python policy tests ran
  196 tests with eight skipped. Four source-boundary tests passed. The public
  native-path runner passed 241 process checks and 84 corpus clients of at most
  four qubits.
- Native replay of the immutable 799 original pairs retained **263 accepted,
  536 rejected and zero acceptance differences** (including one pre-native empty
  proposal rejection). `replay-complete/results.json` binds the final Rust/Lean
  sources and binaries; earlier replay records are intermediate observations.
- Inventory, source-only schema registry, editions and documentation checks pass.
  Lean source/proofs were unchanged, so no new Lean proof compilation is claimed.
  Full clean release CI, Linux/MSRV/Windows validation, package publication and
  v0.3.1 stress/classification work were not performed.

The `.qli` files inherit edition 2026 from this directory's Qargo manifest.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
