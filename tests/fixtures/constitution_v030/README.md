# Constitution adoption evidence

The edition-2026 Constitution and governance candidate were explicitly adopted
by Masahiko G. Yamada, with appointment as the initial sole human Guardian,
effective **2026-10-04 (Asia/Tokyo)**. The actual
[human adoption record](../../../governance/ratification-2026.json) preserves the
question, exact approved hashes, answer and provenance. The
[review guide](../../../docs/src/design/ratification.md) explains current status
and the remaining, separate interpretation and proof decisions.

- [Constitution](../../../CONSTITUTION.md) is the sole ratified constitutional text.
- [Governance](../../../GOVERNANCE.md) records current status and the holder.
- [Reviewed governance candidate](governance-candidate.txt) preserves the exact
  adopted candidate bytes before its pending status was updated.
- [Source issue](issue-129.json) preserves the retrieved Draft 5 and its identity.
- [Candidate diff](candidate.patch) is the complete title/Article VIII change.
- [Candidate packet](packet.json) is frozen historical pre-adoption evidence;
  its null human event does not describe the subsequent adoption record.
- [Pre-adoption validation](validation.json) records checks before ratification.
- [Baseline](baseline.json) distinguishes published 0.2.9 source from the
  pre-existing uncommitted alpha work. Its local archive is a recovery snapshot,
  not a published artifact or validation claim.

The candidate checker validates historical candidate integrity. Its
`--require-ratified` mode rejects that candidate format even after a separate
adoption event exists. The constitutional checker validates the actual adopted
identities and live ledger, without independently authenticating a human
or conferring interpretation, proof or release authority.

The initial QS/PR/RS adoption and subsequent two scoped QS admissions have
separate human records under `governance/`. The archived `bootstrap-ledger.json`
and `pending-ledger.json` preserve their respective earlier states.
`initial-guarantees/` retains the original reviewed Lean declarations and output,
validation, registry and complete source-closure archive. The admission record
binds those immutable historical objects; current proof/source evidence is
maintained separately in `governance/guarantees/current-evidence.json`.

The source archive is inert review material. It does not replace the current
acceptance code or permit an old proof to certify changed artifacts. The
ownership rename comparison, exact patch and build/audit records document #287
without turning ownership into quantitative Resource Safety.

`native-contract-bridge/` records additional actual native-contract theorems and
their limited scope; these have not been admitted as new ledger guarantees.
`witness-weakening/` preserves a compiled counterexample to the first v3 evidence
enforcer and the repaired checker's rejection. The original admitted meanings
and theorem claims are unchanged.
