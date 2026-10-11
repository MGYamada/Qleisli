# Architecture documentation validation — Issue #254

`docs/src/reference/architecture.md` publishes the adopted Issue's architecture
principle. README states it at the top; SUMMARY, Language Reference authority
and the contributor build guide link it prominently. The chapter is subordinate
to the actual ratified Constitution and recorded human interpretations. It
does not create predicates, admission rules, interpretations or guarantees.

## Original criteria and their final locations

| Criterion | Chapter location |
| --- | --- |
| Publish the triad | Opening statement, README and book navigation. |
| Policy becomes formal obligation | Policy as Theorem, first three paragraphs. |
| Constitution preserves guarantees | Constitution as Harness, scope/premises, continuity and checked transport. |
| Ecosystem is executable surface | Compiler as Executor, first paragraph and boundary table. |
| Executor and boundary enforcement | Compiler as Executor, native production boundary and table. |
| Explicit compiler policy sentence | Bold opening of Compiler as Executor. |
| Human/proof/execution separation | Policy as Theorem and required future review. |
| Fail closed | Compiler as Executor, rejection/recovery paragraph. |
| Pedagogy and recovery | Diagnostics and inspectable recovery. |
| Recursive checked stdlib | Signature → ordinary source → specified primitive recovery. |
| Subordinate QLT/QDB/QCP/tools | Diagnostics and inspectable recovery, tool paragraph; future implementation status explicit. |
| Three permanent obligations | Policy as Theorem, distinct duties and actual acceptance/artifact links. |
| No Rust compiler correctness claim | Policy as Theorem, explicit separate correspondence obligations. |
| Nine required Issue links | Related decisions paragraph. |
| Future design review required | Required review of future designs and contributor build guide. |

Review checks the current two narrow QLV1 guarantees against broader pending
QS/PR/quantitative RS and EXACT duties. It does not present future workspace,
access, realization, tooling or full stdlib migration as implemented. Agent
guidance, compilation and CI cannot replace human adequacy judgment or proof.

`validation/` retains the exact source inputs and actual pinned mdBook 0.5.4
build, HTML/print link checks, source-doc checks and constitutional identity
check. These are documentation checks; no fresh Rust/Lean verification or full
release readiness is claimed. The admission originals and dependency versions
remain unchanged. `files.json` freezes the packet and reviewed documentation.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
