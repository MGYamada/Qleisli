# Conservative transparent-provider permission study

This is an informed, implementation-aware regression study. These ten FIRST
projects were written after reviewing the common checker and the exact recorded
[ordinary clarification](../../frontend_v030/common-original-ast-design/provider-access-clarification-01.md)
(SHA-256 `04669bfc1fd1bbd92942dd27bf3b180e772bda03d094c485bf4c346e9598d720`).
They precede their first parsing/checking run; this is not a pre-code baseline
or a blind model benchmark. No test, parser, CLI, native process or build has
been executed by this packet's author. Expectations below are predictions and
regression requirements, not observations. Actual future results must be
recorded separately without repairing `attempt-01` in place.

The author reviewed the core but wrote only its resolution, lexical-index and
linear-accounting support helpers. The core's capability-mask implementation
was written by another agent. The author has extensive prior repository and
specification context; exact deployed model/sampling metadata is unavailable.

| FIRST project | Independent source requirement |
| --- | --- |
| `apply-only-forward` | Applying a forward wrapper requires only its valid forward source path. |
| `apply-only-inverse` | Apply on the underlying operation cannot supply the wrapper's inverse. |
| `apply-only-controlled` | Apply on the underlying operation cannot supply coherent control. |
| `adjoint-only-backwards-forward` | A wrapper that applies U's adjoint can be invoked forward when Adjoint(U) is available. |
| `adjoint-only-backwards-inverse` | Reversing that wrapper computes U; the missing Apply(U) must reject. A mask checking only Adjoint(U) is insufficient. |
| `all-paths-inverse` | Explicitly available underlying paths provide the inverse positive control. |
| `all-paths-controlled` | Explicitly available underlying paths provide the control positive control. |
| `unused-op-inverse` | An unused actual Op still constrains the recorded conservative inverse rule. |
| `unused-op-controlled` | An unused actual Op lacking Controlled still constrains the conservative control rule. |
| `closed-provider-controlled` | A closed transparent identity provider retains its conditional source control path. |

Every own callable contains at most two physical qubits, no observation,
preparation, execution loop or simulation. The loader's four existing bundled
sources remain unchanged; checking them is not a new maximum-size experiment.
The distinction between `V`, its forward wrapper and its adjoint wrapper is the
oracle. The tests do not calculate an expected capability mask from production
flags or generate a second circuit as the expected result.

[The integration target](../../../common_source_provider_access.rs) calls
`ParsedProgram::parse` for the selected public path and
`check_project_with_kernel` for the finite public path. Each project includes
the same valid private opaque-Basis `eligibility_barrier`. Five source-positive
cases must yield selected source facts and the explicit finite opaque-Basis
eligibility refusal. The other five must report the missing source capability
before that barrier. No finite specialization success is claimed.

The finite client uses a deliberately absent kernel path inside its owned small
temporary project. A spurious advance to native checking therefore cannot
execute a child. Selected preparation stops before instantiation, projection
eligibility, emission or native acceptance. All twenty source-path assertions
remain unexecuted until root validation. The absent path does not manufacture
native rejection evidence.

Root's actual all-target compile in `latest-attempt-03` found four Rust test
format strings requiring `Diagnostic`'s Debug formatting. The original test
bytes and the retained raw failure log's hash are recorded in
`test-authoring-attempt-01/`. The repair changes only those four format strings;
no FIRST source or manifest was changed, and no source test ran in that failed
compile. The packet's author performed no compilation or execution.

`provenance.json` records preparation status and contract identity.
`first-files.json` binds the original sources/manifests, this explanation,
provenance and the authored Rust test; its map is intentionally not a complete
production source closure. No constitutional act, certificate, source-family
proof, native decision, release readiness or Issue completion is recorded.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
