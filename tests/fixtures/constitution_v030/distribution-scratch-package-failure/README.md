# Package-failure evidence preservation delta

This is a small synthetic follow-up to `../distribution-scratch/`. The earlier
fixture is unchanged. The review found that a package command could create a
crate and then fail its verification: immediate command failure skipped the
durable copy, and the new owned-work cleanup removed the only archive.

`before-observation.json`, `before-report.json` and `before-command.*` retain
the actual first reproduction. A tiny synthetic package command created the
expected archive and returned exit 23. The validator returned failure and removed
owned work; neither the generated crate nor a durable crate remained. The exact
validator under review is `before-check_distribution.py.txt`, bound by SHA-256.
The command result was simulated; this does not claim a real Cargo failure was
run. Git, archive writing, validator control flow, log writing and cleanup were
real. The fixture harness removed its own tiny temporary repository afterwards.

The correction preserves any crate observed at the expected target after a
failed package command, recording it as `unverified_crate` with failed Cargo
verification and an explicitly unverified candidate binding. A caller-owned
target may contain old bytes; preservation does not prove they were generated
by this run or validate them for release. The original command error remains
the primary failure and the normal successful-package checks are unchanged.

Copies first write a `.crate.partial` file and rename it only after a complete
write and close. If copying fails, no partial file is recorded as complete crate
evidence. `artifact_preservation_error` records the additional failure and
`unretained_crate_path` identifies the original bytes. If the target is internally
owned, work is retained with reason `artifact-preservation-failed` so cleanup
does not destroy the sole archive. Caller-owned targets remain caller-owned;
their archive survives while the separate owned work can still be removed.
No copy failure can make validation pass or mask the original package failure.

`after/observations.json` records four executions, including original candidate
bytes encoded as base64 and compared directly with the synthetic command's
archive bytes before cleanup:

| Case | Result | Work | Candidate bytes |
| --- | --- | --- | --- |
| Package fails after creating crate | failed, exit 23 retained | removed | exact durable unverified copy |
| Package succeeds but durable copy fails after seven bytes | failed | retained with explicit reason | original preserved; partial not accepted |
| Package and durable copy both fail | failed, exit 23 retained | retained with explicit reason | original preserved; partial not accepted |
| Package and durable copy fail with caller target | failed, exit 23 retained | removed | original and caller sentinel preserved externally |

The report paths describe temporary test locations. The harness removes those
locations only after recording and checking the outcomes; this is separate from
the validator's cleanup decision. All archived bytes here are small synthetic
fixtures, not Qleisli distribution or native evidence.

Reproduce from the repository root with an unused output directory:

```sh
python3 -m unittest discover -s scripts -p test_check_distribution.py -v
python3 tests/fixtures/constitution_v030/distribution-scratch-package-failure/record.py --output /private/tmp/qleisli-package-failure-observation-new
```

`validation.json` records actual commands, interpreter identity, source hashes
and raw stdout/stderr: **32 distribution tests passed**, including three new
regressions. No real Cargo/Rust/Lean build, installation, large copy, historical
temporary-directory removal or release was performed. Full distribution
validation remains required for the final integrated release candidate.
