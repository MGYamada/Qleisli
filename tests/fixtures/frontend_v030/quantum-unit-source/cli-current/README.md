# Current quantum Unit CLI observations

This informed post-implementation replay preserves the exact 14 projects and
28 command arrays from the [original study](../../../authoring_sessions/quantum-unit-v030/README.md).
It changes no original source, manifest, module/provider binding or baseline
observation. The original diagnostics remain the pre-implementation record.

The actual command was:

```sh
python3 tests/fixtures/frontend_v030/quantum-unit-source/cli-current/replay.py --output tests/fixtures/frontend_v030/quantum-unit-source/cli-current
```

It exited 0. `observations/` retains complete actual JSON stdout, stderr, exit
code, argv, explicit kernel environment, elapsed time and baseline observation
hash for every call. `summary.json` classifies the results:

- Selected source: 8 accepted, 6 rejected as intended. The six new successes
  cover identity, helper movement, ordered Unit/Bit owners, scalar phase and
  apply/control providers. The two unchanged controls cover ordinary Unit and
  the distinct empty Bits owner.
- The selected negatives now reach exact type checking (Unit versus Bits0 in
  both directions) or ownership checking (duplicate, lost, wildcard-discarded
  and invalid zero-fold owners), instead of stopping at the old Unit projection
  restriction.
- Finite project: 6 accepted and 8 rejected. All 14 exit codes and complete
  stdout/stderr strings are byte-identical to their original observations.

The reused CLI SHA-256 is
`25ee7a6e03d7c7b4e2c6b67754c5ad62dd40cc98aaf93a7bba09b77a5d23f280`;
the unchanged kernel is
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
`identity-before.json` binds the actual executable paths and the successful
[final build record](../latest-final/result.json). All 366 entries in its
[source manifest](../latest-final/sources.json), both executables and the entire
original study manifest match before and after replay, as recorded in
`identity-after.json`. HEAD identifies the checkout base; source hashes also
bind its uncommitted implementation. This driver performs no build.

These are bounded CLI checking observations. Finite checks retain the original
empty-main convention and do not observe open f's scalar action. Selected
native hierarchy checks are not independent full source-preservation proofs;
exact scalar/control/reference oracles are covered separately by the integration
tests. No new Lean build, audit, release-readiness decision or guarantee admission
is claimed here.

The driver refuses to overwrite `observations/`. To replay later, supply a new
output directory after building and verifying the recorded inputs; a later
toolchain's executable will have its own identity. `files.json` hashes this
packet excluding itself.
