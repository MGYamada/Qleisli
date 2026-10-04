# Constitutional records

- [Ratification](ratification-2026.json) transcribes the actual human adoption
  of the exact edition-2026 constitutional text and governance candidate and
  initial Guardian appointment, effective 2026-10-04 (Asia/Tokyo).
- [Initial interpretation adoption](interpretations/initial-2026-adoption.json)
  records the appointed Guardian's subsequent explicit adoption of QS-2026-01,
  PR-2026-01 and RS-2026-01. The [reviewed text](interpretations/initial-2026-reviewed.txt)
  preserves the exact approved packet, including its historical candidate status.
- [Guarantee ledger](guarantees.json) records those three interpretations as
  binding pending broader obligations and two discharged scoped QS guarantees.
  Existing proofs are not automatically admitted as constitutional discharges.
- [Initial scoped QS admission](guarantees/initial-2026-admission.json) records
  the subsequent human adequacy judgment for the exact
  [reviewed proposal](proposals/initial-guarantees.json): ordinary QLV1 ownership
  and classical scope. Its historical candidate text stays unchanged. The
  [Book explanation](../docs/src/design/initial-guarantees.md) states the exact
  limits. The three broader obligations remain pending.

The [Constitution](../CONSTITUTION.md) is the sole entrenched text.
[Governance](../GOVERNANCE.md) records the current human holder and arrangements.
The [authority Reference](../docs/src/reference/authority.md) explains the hierarchy;
[initial interpretations](../docs/src/design/initial-interpretations.md) render the
adopted requirements with updated status. GitHub Issues remain the work tracker;
these files record acts, interpreted obligations and evidence.

The human transcripts are provenance, not cryptographic signatures. Their clock
fields are subsequent observations, not timestamps of the human messages. A
hash binds bytes; it cannot establish who authored them.

Run `python3 scripts/check_constitution.py` to validate the adopted identities
and current ledger. `--base-ref COMMIT` additionally protects existing
records against the selected base. The earlier bootstrap ledger remains at
`tests/fixtures/constitution_v030/bootstrap-ledger.json`; the explicit new human
interpretation event authorizes that transition, not a proof discharge. The
later admission has its own event, and preserves the preceding pending ledger
at `tests/fixtures/constitution_v030/pending-ledger.json`.

`--require-release-ready` rejects the current incomplete proof-enforcement
state. Current evidence is separate from the historical admission. It must bind
the reviewed properties and formalization to current acceptance and artifacts,
with continuity for the protected meanings. A change in semantic representations
requires checked transport support; a source hash or review marker alone cannot
establish it.

Changes to the checker or workflow remain subject to review. This implementation
does not complete constitutional CI, prove a Fundamental Theorem, or implement
an automated Article IX correction path. A valid human rectification would need
its concrete record and reviewed enforcement support; editing a hash cannot
authorize it.
