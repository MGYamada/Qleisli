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
- [Exactness adoption](interpretations/exactness-2026-adoption.json) records
  the Guardian's adoption of EXACT-2026-01 on 2026-10-05. The
  [reviewed supplement](proposals/exactness-2026.md) retains its historical
  candidate status and exact approved bytes. It applies across QS, PR and RS;
  it creates no fourth jurisdiction or discharged guarantee. Ledger schema v5
  retains the three broader obligations, adds the pending supplement, and
  preserves both admitted guarantees and their current evidence bindings.
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

## Agent startup and handoff

Before development starts or resumes after a model change, new session or
context reset, reconstruct constitutional state from repository originals.
This is a working procedure under the adopted governance, not a new binding
interpretation or a change to the Constitution.

1. Read the [Constitution](../CONSTITUTION.md), [governance](../GOVERNANCE.md),
   [authority hierarchy](../docs/src/reference/authority.md) and
   [ratification](ratification-2026.json). Read the current
   [ledger](guarantees.json), its referenced adopted interpretation texts and
   human adoption records, and the admitted guarantee proposals, admission
   records and current evidence relevant to the work. Conversation summaries,
   prior model conclusions and historical candidate labels do not replace
   those originals or the subsequent actual adoption records.
2. Run `python3 scripts/check_constitution.py` from the repository root.
   Also use `--base-ref` with the exact previously reviewed commit supplied by
   the task or review process to check continuity. Record that commit; an
   unchecked current HEAD or a newly edited expected hash is not an independent
   trusted base. If no trusted base is available, report that continuity was
   not checked against one rather than inventing a baseline.
3. Before dependent changes, report the applicable adopted interpretations,
   protected guarantees, remaining pending obligations, and the check result
   and base used. Preserve each recorded scope and premise. Source/evidence
   identity checks are not a fresh Lean replay, a human adequacy judgment,
   full QS/PR/RS discharge or release approval.
4. If required records are missing, conflicting or fail verification, report
   the concrete problem and stop changes that depend on that unresolved state.
   Do not invent approval, weaken a guarantee, change proof status or rewrite
   protected text, records or expected hashes merely to make a check pass.
   Constitutional judgments remain with the human Guardian; ordinary technical
   repairs within adopted requirements remain ordinary maintenance.

A model or agent change does not require re-ratification or re-adoption of
valid existing decisions. It also does not resume paused development or widen
the user's authorization. Ordinary implementation covered by existing
interpretations requires no fresh Guardian ruling merely because the model
changed. New binding interpretations and guarantee admissions still require
the responsible human's explicit judgment on the concrete reviewed proposal;
admission also requires the applicable checked proof or evidence. AI output,
silence, general permission to develop and passing CI cannot supply that act.

## Ledger admission scope

The ledger is not a catalogue of Lean declarations or development milestones.
Record only guarantees concerning the constitutional QS, PR or RS obligations,
with their defined scope, premises, checked evidence and explicit human admission.
Ordinary helper lemmas, transport proofs and implementation checks stay in proof
sources and validation records. Supporting a ledgered guarantee updates its
current evidence when necessary; it does not automatically create another entry.
The two already admitted scoped QS guarantees retain their protection.
This operational clarification follows Article VI; it adopts no interpretation
or new guarantee.

## Integrity checks and limits

Run `python3 scripts/check_constitution.py` to validate the adopted identities
and current ledger. `--base-ref COMMIT` additionally protects existing
records against the selected base. The earlier bootstrap ledger remains at
`tests/fixtures/constitution_v030/bootstrap-ledger.json`; the explicit new human
interpretation event authorizes that transition, not a proof discharge. The
later admission has its own event, and preserves the preceding pending ledger
at `tests/fixtures/constitution_v030/pending-ledger.json`.
The exactness transition accepts a genuine schema-v4 Git base and separately
protects the new text and adoption event. It rejects removal, rollback,
fabricated discharge and changed bytes during evidence checking. Scoped release
disclosures must retain all four pending interpretation IDs, including EXACT.
The verifier returns the digest of the ledger bytes it actually checked.
Receipt production and release consumption bind that digest to their captured
ledger before reporting readiness; equal counts cannot substitute for identity.

`--require-release-ready` rejects the current incomplete proof-enforcement
state. Current evidence is separate from the historical admission. It must bind
the reviewed properties and formalization to current acceptance and artifacts,
with continuity for the protected meanings. A change in semantic representations
requires checked transport support; a source hash or review marker alone cannot
establish it.

The explicit atomic-Bits extension uses a fixed checked representation
transport in `lean/Qleisli/FiniteBasisTransport.lean`, with its fixed type review
in `tests/fixtures/constitution_v030/initial-guarantees-continuity/BasisTransportReview.lean`.
Its current-evidence profile preserves the historical baseline, independent
ownership/scope meanings and original-byte/root binding templates. The live
check recompiles the review and compares fresh extraction; a recorded source
hash alone is not a fresh proof check. The legacy full-expression identity
profile remains available for unchanged representations. This is technical
preservation of the two existing scopes, not a new guarantee admission.

Changes to the checker or workflow remain subject to review. This implementation
does not complete constitutional CI, prove a Fundamental Theorem, or implement
an automated Article IX correction path. A valid human rectification would need
its concrete record and reviewed enforcement support; editing a hash cannot
authorize it.
