# Release scope proposal: v0.3.0-alpha

Status: proposed. The maintainer's request to publish an alpha authorizes release
preparation and eventual publication after validation. This concrete change to
the existing release-readiness criteria awaits explicit human review; its
presence, a hash or a successful test does not record approval.

## Scope and compatibility

Publish only the `qleisli` crate at `0.3.0-alpha` and the matching GitHub
prerelease `v0.3.0-alpha`, from one exact checked commit. This is a development
snapshot of the implemented language, not completion of the v0.3.0 feature
goal. Do not close remaining Issues, resume paused feature development or claim
that all planned v0.3.0 requirements are implemented. Source and public API
compatibility with 0.2.9 is not promised by this MINOR prerelease.

The separate tools are independent projects and are not included in this
publication authorization. Dependency library versions must remain unchanged.
QFT development, deferred features and general arrow types remain outside the
current work. Existing fixed examples and their required regression checks
remain intact.

## Required verification

Before publication, require all eight existing validation producers and their
required contexts to succeed on the candidate commit, with the full validation
profile and full proof lane, in one GitHub Actions run attempt. Re-running only
failed jobs cannot combine evidence from different attempts. Retain the existing
MSRV, Rust, Python, native acceptance, independent oracle, Lean build/audit and
fresh replay, distribution, fresh installation and fixed mdBook checks.

Use the existing representative `--quick` corpus policy, with retained
`quick-representative-v1` reporting; exhaustive corpus execution remains retired.
Retain source identity, constitutional continuity, PR and fixture size gates,
both native platform bundle identities and full replay, original artifact
binding and the existing same-run receipt verification. Do not raise budgets.

The alpha release gate must reuse those checks and receipts. Its only change
in release criteria is that this expressly approved development snapshot does
not require completion evidence for every planned v0.3.0 feature Issue. Bind
the alpha scope and the affirmative human approval to a separately reviewed
Git base. The exception applies only to product version `0.3.0-alpha`; it must
not enable stable, beta, rc or other alpha releases. The existing complete
feature-requirements gate remains in force for those releases until separately
reviewed. Missing approval, scope, evidence or a failed required check rejects.

## Constitutional status and truthful claims

Preserve edition 2026, the ratified Constitution, all adopted interpretations
and the two admitted guarantees: `QS-QLV1-OWNERSHIP-2026-01` and
`QS-QLV1-SCOPE-2026-01`, with their recorded premises, original decoded-root
scope and current checked evidence. This proposal admits no new guarantee and
makes no constitutional interpretation.

QS-2026-01, PR-2026-01 and RS-2026-01 retain their broader pending obligations;
EXACT-2026-01 retains its pending proof and enforcement duties across those
jurisdictions. No production-wide QS, PR, quantitative RS, complete source or
runtime preservation, or full constitutional conformance is claimed. All
accepted capabilities remain subject to the applicable obligations; labeling
this release experimental does not create an exemption.

## Publication and readback

After the required checks pass, publish the verified crate bytes to crates.io
and create the GitHub release with `prerelease = true`. Bind the tag to the
same checked commit; do not move an existing tag or replace a published crate.
Read back the peeled tag, crate checksum and retained release assets and verify
their identities against the checked artifacts. Preserve Apache-2.0 licensing,
historical and third-party notices, and the approved current project attribution.

Release notes must disclose the snapshot scope, remaining feature and proof
obligations, incompatible source/API changes, and experimental OpenQASM 3 / QIR
adapters unsuitable for and not recommended on real hardware. State that macOS
distribution is under consideration without providing installation instructions.

## Decision requested

Approve these alpha-specific criteria as an ordinary maintainer release-scope
decision, or request changes. Approval does not declare a failed check successful,
complete the feature goal, discharge a constitutional obligation, merge PR #307
or authorize publishing any different version.
