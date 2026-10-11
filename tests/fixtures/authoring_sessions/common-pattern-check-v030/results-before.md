# Common declaration/pattern checks: preserved first observations

**Status: bounded informed first-source evidence, not a common checker
implementation or proof.** Eight complete sources and their edition-2026
manifests were frozen before the first command. There was one source snapshot,
no source repair, no production edit, and no run/sample command. The original
[context](context.md), [prerequisites](prerequisites.md),
[source inventory](session.before.json) and [first-file hashes](first-files.json)
retain that starting point; [session](session.json) appends only the real
observations.

The fixed authored driver completed 40 commands: sixteen finite project checks,
sixteen selected-module checks, and eight selected `emit-proposal` calls. Each
check has text and JSON presentations. Eight checks succeeded and twenty-four
checks rejected. Two untrusted proposals were emitted; six emissions rejected.
All raw streams, exact argument lists, native invocation logs and proposal bytes
are linked through the [summary](before/summary.json) and frozen by
[completed-file hashes](files-before.json). These results are not predictions
copied from the case intentions.

| Original case | Finite check result | Selected auto-profile result |
| --- | --- | --- |
| Exact nested runtime parameter `((a, ()), b)` | Pass; 20 native calls per presentation, including existing bundled bodies. | Pass; one selected native call per presentation; hierarchy proposal emitted without native checking. |
| Duplicate runtime parameter `q, q` | `ownership`: `duplicate parameter name`. | `name`: `duplicate runtime parameter`; no proposal. |
| Legal `let q = h(q)` | Pass; 20 native calls per presentation. | Pass; one selected native call per presentation; untrusted hierarchy proposal emitted. |
| Hide an existing live owner with `let q = p` | `ownership`: `binding would hide unconsumed quantum ownership`. | `ownership`: `binding q would drop a live quantum owner`; no proposal. |
| `join(q, q)` | `ownership`: second use of `q` is already consumed. | `ownership`: `unbound or consumed value q`; no proposal. |
| Wildcard `Q<Unit>` parameter | `ownership`: `wildcard would discard quantum ownership`. | Same code/message; no proposal. |
| Wildcard `Q<Bits<0>>` parameter | `unsupported`: `register types are outside the finite lowering profile`. | `ownership`: `wildcard would discard quantum ownership`; no proposal. |
| Never-called invalid private sibling returning `(q, q)` | `ownership`: second use already consumed; one earlier native call per presentation. | `ownership`: `unbound or consumed value q`; no native call and no proposal. |

Every rejection had exit 1 and every success exit 0. Both presentations retain
the same result and native count for each profile. The exact original error
spans and path conventions are in the raw JSON/text records. Finite parameter
uniqueness is currently an ownership diagnostic; selected parameter uniqueness
is a name diagnostic. The finite register-profile error occurs before the
zero-width wildcard ownership check, so it supplies no evidence that this
later ownership condition was reached. Finite checking of the invalid sibling
made one native call before rejecting the complete project; that earlier call
does not accept the invalid declaration or the project. Selected checking
rejected the unused body before any native call. In total the logger observed
86 native invocations; no invocation was made by `emit-proposal`.

The selected successes explicitly report `sized-unitary`, hierarchy IR,
`producer-consistency`, `request_origin: producer`, and
`source_meaning_verified: false`. Their source scope is
`all-supplied-module-declarations`; native scope is `selected-specialization`.
The emission result explicitly reports `untrusted-proposal` and native scope
`none`. The finite success field `verified: true` is retained verbatim, with
its public finite/native path and existing bundle scope; it is not generalized
into a source-preservation theorem. No independent functional, phase or
arbitrary-reference oracle was run in this check/emit-only study.

[Before identity](identity-before.json) and
[final identity](before/identity-final.json) contain the same 234 current
Rust/native-source, library/manifest, Cargo, constitutional and Reference input
hashes. The CLI hash stayed
`3ba4bff2b98644f56d82d02800a784dc9c49a25bb6e66cdb784eb6b2401345f1`;
the selected native binary stayed
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
Those identities were checked before and after each command. The baseline
commit `b544cd2d96dcc94e0ef29b28e6b08979bca5d9b1` and prior MSRV build are
parent-reported provenance, distinct from this observed byte identity. This
study built neither executable and does not attest compiler/native correctness.

The [constitutional continuity result](record-check/constitution.json) records
a fresh successful source guard against reviewed base
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. QS-2026-01, PR-2026-01,
RS-2026-01 and EXACT-2026-01 retain pending broader duties. Both scoped ordinary
QLV1 guarantees keep their admitted decoded-root meanings and exclusions.
There is no new interpretation, guarantee admission, Lean replay, primitive,
capacity increase, library exposure or issue completion. A future shared
declaration/pattern helper must preserve complete declaration coverage and the
observed profile-specific ordering; this baseline alone does not implement it.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
