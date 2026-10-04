# Ratification and initial Guardian appointment

**Status: ratified and effective on 2026-10-04 (Asia/Tokyo).** Masahiko G.
Yamada, acting as the natural-human project maintainer, affirmatively ratified
the identified edition-2026 Constitution, adopted the identified governance
candidate and accepted appointment as the initial sole human holder of the
Constitution Guardian Office.

The adopting answer was:

> 両候補を批准・採択し、初代Guardianに任命する

The question identified both exact hashes, edition, appointing act and effective
date. The answer is preserved verbatim with that question and its conversation
provenance in repository file `governance/ratification-2026.json`. An assistant
transcribed the actual human answer; it did not infer adoption from the plan,
silence or CI. The transcript is reviewable provenance, not a cryptographic
signature. Its clock observation is explicitly not a timestamp of the human
message, which supplied no timestamp.

## Exact adopted texts

The sole constitutional editing source is repository-root `CONSTITUTION.md`.
Its entire approved text is protected.

The [ratified text](https://github.com/MGYamada/Qleisli/blob/10553a9f94f6fd6a4555961244e0e9be41154f8f/CONSTITUTION.md)
and [authority hierarchy](../reference/authority.md) can be read from this
companion chapter. These navigation links are outside the protected text;
they neither amend it nor create a second constitutional editing source.

The following identities bind the act:

| Object | SHA-256 |
| --- | --- |
| Constitution | `40777370ec860891991bc89ef283f01a5db9a6be5480143f2e09e6014407452b` |
| Reviewed governance candidate | `60e8e6640ccbaccb08ecaca7507956e89458846dc532d5e50084e0e8ca079721` |
| Recorded human adoption event | `3363bf5b25da3efe7094959972f25f7c9737ec3e0444f953ff0f0ee86155af3a` |

`GOVERNANCE.md` records the current holder and arrangements outside the entrenched
Constitution. The approved candidate bytes remain in
`tests/fixtures/constitution_v030/governance-candidate.txt`; changing the active
file's pending status after adoption does not rewrite those reviewed bytes.
Neither this chapter nor that evidence snapshot is a second constitutional
editing source.

The human act establishes the constitutional regime and appointment. It does
not itself adopt a mathematical interpretation, discharge a theorem, approve a
release or authorize publication. The Guardian subsequently adopted the
[initial QS/PR/RS interpretations](initial-interpretations.md) through a separate
explicit answer; that event is recorded in
`governance/interpretations/initial-2026-adoption.json`.

## Preserved pre-ratification evidence

`tests/fixtures/constitution_v030/` retains:

- `issue-129.json`: retrieved Draft 5 before the final candidate;
- `candidate.patch`: the complete title and Article VIII changes;
- `packet.json`: the exact candidate hashes and historical pending status;
- `baseline.json`: published 0.2.9 identity and pre-existing alpha source changes;
- `validation.json`: checks performed before human adoption.

The null event and pending status in the frozen candidate packet describe that
historical artifact. Current status comes from the subsequent actual adoption
record. The locally retained baseline archive is recovery evidence, not a new
source commit, release-validation result or published artifact.

## Changes from Draft 5

The adopted text retains the Preamble and Articles I–IX from
[Draft 5](https://github.com/MGYamada/Qleisli/issues/129). Issue explanatory notes,
task lists and development history were excluded. Two textual changes were
presented before ratification:

1. The title became `Qleisli 2026 Constitution`, without a draft number.
2. Article VIII permits the natural-human project maintainer to ratify exact
   text through an explicit event before completion and publication of 0.3.0.
   The eventual release verifies the adopted identity and applicable release
   conditions; it does not repeat ratification.

These were pre-adoption draft changes, not Article IX rectifications. No
mathematical QS, PR or RS definition was entrenched in the Constitution.

## Subsequent authority and edition

The [authority hierarchy](../reference/authority.md) orders further work:
Constitution; binding Guardian interpretations and discharged guarantee ledger;
current formal obligations and checked evidence; Language Reference; then
implementation, conformance tests and examples.

The human Guardian determines what must be proved and whether a formalization
adequately expresses the obligation. Lean or the designated independent checker
establishes the proposition under its stated assumptions. Existing proofs and
Issue proposals do not automatically become ledger guarantees.
`governance/guarantees.json` now records the three explicitly adopted initial
interpretations as binding pending broader obligations. A later human judgment
admitted [two scoped QLV1 guarantees](initial-guarantees.md), for ownership and
classical scope, with their checked evidence. The earlier bootstrap and pending
ledger states remain historical evidence.
The subsequent [exactness interpretation](../reference/authority.md#exact-constitutional-obligations)
applies across those three jurisdictions and retains separate pending proof
and enforcement duties. Its adoption does not discharge a new guarantee.

An edition identifies a **constitutional regime**, not syntax. The 0.3.0
language migration remains in edition 2026. Source trees explicitly select
schema-2 `[qrate].edition = "2026"`; propagation to every native acceptance
artifact remains an implementation obligation in Issue #255.

## Identity checks and their limits

Run from the repository root:

```sh
python3 scripts/test_check_ratification_packet.py
python3 scripts/check_ratification_packet.py
python3 scripts/test_check_constitution.py
python3 scripts/check_constitution.py
python3 scripts/check_docs.py
mdbook build docs
```

The candidate checker validates archived review objects; its
`--require-ratified` option still rejects that historical candidate format.
The constitutional checker verifies the fixed adopted text, recorded event,
reviewed governance snapshot, adopted interpretation event/text, scoped
admission and current ledger. With `--base-ref COMMIT`,
it also checks continuity with existing records in that Git base. CI checks the
available PR/push base; changes to enforcement code and workflow policy still
require review. These checks cannot independently authenticate the human
transcript or decide whether a mathematical obligation is adequate.

`check_constitution.py --require-release-ready` delegates to the scoped release
gate. It requires a caller-reviewed exact requirements base, complete acceptance
evidence and successful same-run validation receipts for the actual candidate
and artifacts. Source identity checks cannot stand in for live Lean replay.
The current incomplete acceptance evidence still prevents a ready result;
truthfully disclosed broader pending obligations alone are not a pre-v1 ban.
The remaining [constitutional CI work](https://github.com/MGYamada/Qleisli/issues/141)
must connect binding interpretations, formal obligations, checked proofs and
current production/artifact identity. Hash checks alone do not complete it.
The [release umbrella](https://github.com/MGYamada/Qleisli/issues/142) tracks all
108 selected issues and the separate implementation, proof and publication gates.
