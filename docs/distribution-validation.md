# Reproducing the distribution gate

[Checker](../scripts/check_distribution.py) binds clean Git HEAD to its actual .crate
and complete source archive. Version selection/helper tests do not satisfy the gate.

```sh
python3 scripts/test_check_distribution.py
python3 scripts/check_distribution.py --report /tmp/qleisli-distribution.json
```

Use a new external report/artifact path; optional --target-dir is external. Cargo is
offline, with no dependency installation/publication. Dirty/staged/untracked candidates
reject, ignored builds excluded. Never overwrite reports; retain failures/logs.

Inventory every tracked regular file's Git bytes/mode, reject symlinks/submodules.
Git tar must match complete inventory, with no unsafe/extra/missing/changed entries;
extract only validated regular files. Include research/Lean/tests/upstream/docs.
Replay corpus metadata from extraction, bind upstream/final manifests/hashes and
licenses/notices. Cargo package/build verification and listing compare actual tracked
source, with explicit normalized manifest/generated lock/VCS exceptions; Cargo.toml.orig
is exact, VCS matches clean commit/root. Extract .crate and check offline locked metadata
(identity/license/dependencies/features/targets/lock), generated ordinary modes.
Record Cargo exclusions: nested research is outside production .crate but inside full
source; both retain required corpus originals/translations/notices. Run production/
research all-target tests from complete archive, then recheck clean commit/tree/bytes.

Report includes file hashes/modes, artifacts/SHA256, exclusions, tool versions,
commands/exits/logs and outcome. No cross-host compiler reproducibility promise.
This gate does not rerun MSRV/Lean/full release checks or tag/push/publish; record those
separately on the same candidate. Package builds and archived-source tests are distinct.
Helper mutations cover dirty identity, bytes/modes/notices, manifest inventory/VCS,
exclusions, unsafe/duplicate tar entries and links/special files, without fabricated
release results. [Versioning](versioning.md) governs release evidence.
