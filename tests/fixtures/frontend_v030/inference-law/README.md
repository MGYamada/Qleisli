# Inference-law and explicit-binding validation — Issue #100

The adopted 2026-10-02 Issue distinguishes the 0.3.0 law from #197's existing
0.4.0 convenience catalogue. This packet completes the law in the current
conservative profile; it introduces no general inference engine, trait search,
implicit coherence or physics. Original acceptance criteria are unchanged.
General Basis, future access syntax and the remaining common-profile migration
retain their own Issues. Edition, native acceptance, obligations and scoped
guarantees are unchanged; this is no human interpretation or guarantee admission.

## Before and after

The [informed first-source study](../../authoring_sessions/inference-law-v030/README.md)
freezes nine complete projects and 24 probes before repair. The baseline and
after-repair records preserve all raw output, source/CLI/kernel identities and
transparent native invocation logs. All 18 negatives reject before invoking
native checking in each batch. All six successful JSON outputs remain identical;
negative codes, original modules/spans, statuses and other fields remain unchanged.
Only the messages change. `text-checks/` additionally records 24 actual text-mode
checks with the same statuses, diagnostic messages/spans and native counts.

`check.rs.before.txt`, `type-model.md.before.txt`, `inventory.before.json`,
`coverage.before.json` and
`diagnostic-repair.patch` retain the production/reference/inventory delta.
Review of the helper confirms the set comparison is equivalent to the original:
equal cardinalities and all expected keys present. Duplicate declarations still
reject earlier. Missing/unexpected keys use BTree order; all supplied values
remain explicit. Natural errors still precede Op errors. Provider scope checks
retain their original spans and module mapping. No native request, lowering rule,
proof or authority surface changes. Only the reviewed source's current inventory
hash and the dependent current coverage binding change; historical identities
and protected evidence are not regenerated. Public markers, coverage rules,
proof gates, authority and fixture obligations stay byte-equivalent.

## Criterion-level review

| Original criterion | Normative contract and executable evidence |
| --- | --- |
| Uniqueness/no-physics law | `docs/src/reference/type-model.md`, Inference and generic responsibilities, alongside exact equality categories. |
| Ambiguous substitutions reject | Missing/extra/unused Nat/Op and call-arity probes; distinct explicit identity/X and same-named qualified providers remain distinct. No candidate ranking. |
| T and Q<T> do not interconvert | `expected_types_do_not_choose_physics_or_manufacture_access_and_effects`; existing frontend type tests reject ordinary/quantum and exact shape mismatches. |
| Physical maps stay explicit | Exact type-tree comparison rejects Bit/Bits<1>, product association and width-only substitution; `tuple_shapes` and `operation_parameters` retain explicit maps, axes and phase. |
| Three equality categories constrain inference | Type model Equality categories and admitted explicit maps; #84's classification remains unchanged. No implicit map is added. |
| Trait/capability cannot manufacture authority | Declared Apply/Adjoint/Controlled and Meaning are checked, not searched; operation-parameter negatives reject missing access, wrong meaning and circular source dependencies. General trait search is not implemented and is not implied by this law. |
| Callable ambiguity rejects | Common resolution checks declaration identity/category before checking; shared-resolution duplicate-declaration, shadowing and qualified-provider cases plus sized local-call/category failures. Unsupported callable classes do not become candidates. |
| Effects cannot downgrade | New Observe/Unitary negative plus existing operation/body and sized effect checks. |
| Deterministic, bounded, explainable | BTree missing/extra order and reversed insertion tests; same fixed-input CLI observations; existing preparation/type/storage/work/recursion capacity negatives. Capacity rejection does not prove impossibility. |
| #197 boundary remains explicit | Reference and original Issue keep the existing later convenience catalogue; no acceptance condition or scope is reduced. |

`tests/inference_law.rs` adds six tests. Its independent one-qubit identity/X
expectations act on two blocks of complex coefficients carrying an external
reference; native inspection and bounded execution are distinct from an open
source check. These comparisons prove no source-preservation theorem or broad
QS/PR/RS obligation. Existing retained tests supply shape, phase, capability,
effect, ambiguity and finite static-limit negatives.

## Actual validation and the retained failure

`latest-first/` records Rust 1.98.1: 91 passing focused tests, one ignored historical
function stress test and five filtered sized comparison tests; all-target Clippy
and formatting pass. `msrv-first/` records Rust 1.85.0: the same six integration
targets pass (55 tests), then the driver mistakenly requested the historical
ignored maximum-depth/expanded-work stress lane. That request violated the
approved no-new-maximum-run policy and failed in the native bounded profile.
The original failure and driver are retained. Its generated scope sentence
claiming no maximum run is incorrect; this paragraph records the correction.
No checker limit, ignored test or assertion was weakened to obtain a pass.

The corrected driver never selects that ignored lane. `msrv-completion/` runs
the remaining 36 bounded sized tests, Clippy and formatting successfully without
repeating the already passing 55. The successful latest/MSRV checks bind identical
production/test inputs (127 files), and their before/after maps agree. Five sized
comparisons involving broader backend/capacity work were deliberately filtered;
their names remain in the actual command logs. No new local Lean build/audit/replay
was needed because its executable definitions and evidence remain unchanged.
This packet is focused validation, not full CI or release readiness.

`policy-checks/` and `policy-completion/` preserve the failed coverage checks
before updating its dependent source binding. An import-path error in the first
update command left that binding unchanged for the second check. `policy-final/`
records the final inventory/coverage, authoring integrity and constitutional
identity checks. Documentation checks are in the companion architecture-254
packet. `files.json` freezes this
packet and the reviewed inputs; it is evidence, not a second work backlog.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
