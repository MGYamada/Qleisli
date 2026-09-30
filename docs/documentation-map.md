# Documentation map

## docs/ cleanup boundary at v0.3.0

Retain active v0.2.x goals and migration plans. Delete obsolete documentation
actively; all remaining pre-v0.3.0 files expire at v0.3.0, when the documentation
will be written from scratch. Do not archive or transplant the legacy tree.
Git history supplies historical lookup; executable evidence and required notices
outside `docs/` remain. See the [cleanup plan](v0x-roadmap.md#documentation-discipline-for-v030).

## Temporary v0.2.x navigation

English is authoritative for production specifications and public library names,
contracts, comments and examples. Supporting Japanese discussions and dated
records remain historical material. A proposed design does not override current
rules; adoption, implementation, testing and proof are separate states.

| Read for | Documents |
| --- | --- |
| First use | [README](../README.md#try-it), [copyable source reference](qli-quick-reference.md), [frontend guide](frontend-v0.md) |
| Current language | [Language v0](language-spec.md), [types](type-system.md), [grammar](syntax-v0.md), [standard modules](standard-library.md), [static operations](static-operations.md) |
| Meaning and evidence | [Semantic contracts](semantic-contracts-v0.1.md), [function contracts](function-contracts-v0.1.md), [library ledger](stdlib-contracts.md), [trust boundary](../TRUST_BOUNDARY.md) |
| Formal rules | [Formal core](formal-core.md), [typing](source-typing-rules.md), [resources](source-resource-rules.md), [source semantics](source-semantics.md), [soundness](source-soundness.md), [IR correspondence](source-ir-correspondence.md) |
| Implementation/proof scope | [Architecture](implementation-architecture.md), [Lean ledger](lean-resource-proof.md), [finite IR](ir-prototype.md), [machine interfaces](machine-interface-spec.md), [experimental hierarchy](hierarchical-ir-spec.md) |
| Current state | [Short status](current-status.md), [rule inventory](rule-inventory.md), [0.2.2 plan](v0.2.2-plan.md), [verification packets](verification-migration-v0.2.md) |
| Future work | [Milestones](v0x-roadmap.md), [Lean migration policy](lean-kernel-migration.md), [imaginary source drafts](imaginary-v1/README.md), [Issues](https://github.com/MGYamada/Qleisli/issues) |
| Library contributions | [STDLIB.md](../STDLIB.md), [contract template](stdlib-contract-template.md), [library direction](stdlib-roadmap.md), [corpus policy](../corpus/POLICY.md) |
| Compatibility and releases | [Versioning](versioning.md), [acceptance gates](release-milestones.md), [release procedure](crates-io-release.md), [release records](releases/v0.2.2.md) |

`Cargo.toml` selects the current version. Edit `project-status.json` and regenerate
its two temporary views with `python3 scripts/check_docs.py --write-status`.
Historical narratives and the backlog are retired; use Issues for active work
and keep actual validation beside its fixtures. Current contracts remain usable
during v0.2.x; they have no exemption from the v0.3.0 cleanup boundary.
[Issue #48](https://github.com/MGYamada/Qleisli/issues/48) tracks the later Reference.
