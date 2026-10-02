# Documentation map

English production rules/contracts/names/comments/examples are authoritative;
Japanese discussion and dated records support them. Separate proposals/adoption,
implementation/tests/proofs and version/tag/upload/publication.

| Read for | Current references |
| --- | --- |
| First source | [Quick reference](qli-quick-reference.md), [frontend](frontend-v0.md) |
| Language | [Rules](language-spec.md), [types](type-system.md), [grammar](syntax-v0.md), [modules](standard-library.md), [static forms](static-operations.md) |
| Meaning | [SC/FC](finite-contracts.md), [stdlib ledger](stdlib-contracts.md), [trust](../TRUST_BOUNDARY.md) |
| Implementation/proofs | [IR](ir-prototype.md), [machine formats](machine-interface-spec.md), [hierarchy](hierarchical-ir-spec.md), [formal scope](formal-core.md), [Lean](../lean/README.md)/[kernel](../lean-kernel/README.md) |
| Current work | [Status](current-status.md), [inventory](rule-inventory.md), [continuation](v0.2.2-plan.md), [VM plan](verification-migration-v0.2.md) |
| Future | [Milestones](v0x-roadmap.md), [theorem gates](release-milestones.md), [draft index](imaginary-v1/README.md), [Issues](https://github.com/MGYamada/Qleisli/issues) |
| Contributions/releases | [STDLIB.md](../STDLIB.md), [versioning](versioning.md), [release procedure](crates-io-release.md), [0.2.6 record](releases/v0.2.6.md) |

Cargo selects version; edit project-status.json and regenerate both views using
python3 scripts/check_docs.py --write-status. [#48](https://github.com/MGYamada/Qleisli/issues/48)
tracks aggressive retirement: keep active v0.2.x goals/migration usable, historical
lookup through Git/tags, no archival/redirect stubs. At v0.3 discard remaining legacy
docs and write from adopted rules/code/proofs/examples. Preserve outside-docs source,
attempts, failures, evidence/proofs/notices. No duplicated backlog; Issues track work.
