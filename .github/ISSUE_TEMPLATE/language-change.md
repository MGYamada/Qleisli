---
name: Language or acceptance change
about: Specify a language, library-contract, verification, or normative change before implementation
labels: enhancement
---

## Target, problem and desired source

State the target release, prerequisite issues, the concrete problem and desired
`.qli` examples. Preserve first source attempts and actual diagnostics under
`tests/fixtures/authoring_sessions/` when performing an authoring experiment.

## Proposed contract and alternatives

Specify syntax/API, types, static and runtime effects, owner transitions,
evaluation and failure rules, exact phase/axis/reference semantics, and lowering.
Give accepted and rejected examples, alternatives and a distinguishing
counterexample. Identify the normative Reference section to add or change.

## Constitutional impact

Complete each row with the applicable interpretation, affected scope and reason.
Tests, formal proof and human specification review are separate evidence.

| Obligation | Preserves / strengthens / affects / not applicable | Scope, evidence and remaining duties |
| --- | --- | --- |
| QS (`QS-2026-01`) | | |
| PR (`PR-2026-01`) | | |
| Quantitative RS (`RS-2026-01`) | | |

- **Normative definitions and trusted assumptions:** identify changes or explain none.
- **Production boundary:** exact accepted representation, actual checker and artifacts consumed by execution/export; explain source-to-IR preservation separately.
- **Ledger:** affected guarantee IDs, protected premises/meaning, and current proof/evidence binding.
- **Semantic transport:** existing correspondence, new proof obligation, or why representations and meanings are unchanged.
- **Proof status:** established scope, new obligations, and provisional/unproved claims.
- **Edition:** same constitutional regime or the specific constitutional question; distinguish release compatibility from edition.
- **Human interpretation:** applicable existing ruling, or the concrete new constitutional case requiring Guardian judgment. Covered implementation work does not require a new ruling.

New sealed semantics must also justify why ordinary checked source, desugaring,
a verified transformation or target lowering is insufficient. A new assumption
cannot be introduced merely to make a failed proof succeed.

## Migration and acceptance criteria

List old-to-new source/API/artifact behavior, compatibility and affected
stdlib/examples/corpus. Give mechanically assessable implementation, positive
and negative validation, required proof and documentation completion criteria.
Separate deliberately later scope from the work this issue must complete.
