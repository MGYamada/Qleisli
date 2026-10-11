# Real constitution wrapper in a simulated local CI context

This is a **local integration test with real Lean replay and simulated GitHub
environment variables**. It is not genuine hosted CI, a release candidate,
completion of the 108 issue criteria, a new guarantee admission, or permission
to tag or publish. It is separate from the synthetic proof-service tests in
`../release-readiness/`.

The test started from clean source commit
`b6f0fa0720851dc1acb626b4aa32487a0e7d71a6` plus only the six frozen release-gate
files listed by exact hash in `integration.json`. Other concurrent working-tree
changes were excluded. A disposable local Git repository supplied exact clean
identity without modifying global Git configuration:

- Synthetic commit: `8fa86770179775212d3c253b82840cb94ae18587`.
- Synthetic tree: `d3b0fc30d1fe3bc897c2d8c3e1b8e7708c8b2165`.
- All 6,358 tracked files remained byte-identical after replay; the live owned
  sources and recorded proof/evidence files also remained unchanged.

In that isolated checkout, the actual command was:

```text
/opt/homebrew/opt/python@3.14/bin/python3.14 scripts/check_release_ready.py --record-constitution --output /private/tmp/qleisli-real-release-wrapper-33v6v5j2/constitution-receipt.json
```

It exited **0 in 42.828 seconds**, with empty stdout and stderr. Its real
`current-Lean-replay` receipt records **two already admitted scoped guarantees
and three pending obligations**. `lake env lean --version` independently exited
0 and reported Lean 4.30.0. The wrapper ran the real current Lean verifier, using
APFS copy-on-write copies of the existing build environments. This was not a
fresh Lean build or axiom audit. The pre-wrapper build/audit/replay at the recorded
base is separate evidence; no claim of a new full build is made here.

`commands.json` preserves actual argv, cwd, status and timing; `integration.json`
preserves the explicitly simulated environment and source/evidence hashes.
`constitution-receipt.json` is the actual output. `tracked-before.json` and the
NUL-delimited `command-10.stdout` preserve source identity. All named stdout and
stderr files are raw bytes. The Git source archive was temporary and is explicitly
marked as not retained in the original command record.

`preservation.json` maps original locations to byte-identical files retained
here. Only about 1.4 MB of regular logs/metadata outside the original `source/`
directory were copied. No source tree, `.lake`, `.git`, source archive or build
directory was copied into this fixture, and the original temporary directory was
not deleted. `historical-driver.py.txt` records how the already-completed test
was run; it is not a routine reproduction command and was not rerun during the
disk-pressure correction. Its large temporary build-cache copies motivated
explicit retention management; their apparent `du` sizes include shared APFS
blocks and are not an estimate of reclaimable space.

Full real distribution validation and trusted release-readiness evidence remain
required for the actual final candidate. This integration test supplies neither
a reviewed requirements index nor a real acceptance/publication record.
