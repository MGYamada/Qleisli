# Distribution scratch lifecycle experiment

This informed synthetic experiment implements the resource-management contract
recorded in [Issue #142](https://github.com/MGYamada/Qleisli/issues/142),
“Distribution scratch lifecycle correction — 2026-10-05”. It is not a package,
source, native-checker or release-readiness validation of Qleisli.

The command driver in `scripts/test_check_distribution.py` simulates Rust,
Cargo and installation/source-check clients. It writes tiny build markers,
an installation marker and a small valid archive. The validator itself, its
command log writer, byte/mode checks, extraction, cleanup and a local disposable
Git repository are real. No Cargo, Rust compiler, installer or Lean process ran.

## First observation and corrected behavior

`before.json`, `before-success/` and `before-failure/` preserve the actual first
observations made before editing the validator. Both extracted trees and the
installation survived `validate`; all five build targets survived success and
four survived the injected failure. `before-check_distribution.py.txt` is the
exact original validator, recovered from HEAD and matched to the pre-edit hash.
These old report paths refer to the experiment's temporary repositories, which
the test harness removed only after observing the validator's behavior.

`after/observations.json` and its case directories record eight corrected runs:

| Case | Validation result | Owned work | Caller targets |
| --- | --- | --- | --- |
| Success | passed | removed | none |
| Command failure | failed, original exit 23 retained | removed | none |
| Success with `--keep-work` | passed | retained | none |
| Failure with `--keep-work` | failed | retained | none |
| Success with external target | passed | removed | sentinel and outputs retained |
| Failure with external target | failed | removed | sentinel and outputs retained |
| Cleanup failure after successful checks | failed | cleanup-failed | none |
| Command and cleanup failure | failed, both errors retained | cleanup-failed | none |

Every run verifies that the report, all command logs, the exact crate and the
source archive survive validator cleanup. The fixture retains reports and logs;
the small synthetic archives are checked and hashed during the experiment,
then removed by the harness. This harness cleanup is independent of the
validator cleanup under test. No historical user scratch directory was removed.

The report adds `work.path`, `work.status`, `work.keep_requested` and explicit
`cargo_target.ownership`. An early candidate rejection reports `not-created`.
`removed`, `retained` and `cleanup-failed` distinguish completed cleanup,
intentional retention and an error; cleanup failure cannot return a passing
report. Existing archive, licensing, package, installation and source checks
remain on the same validation path.

## Bounded reproduction and validation

From the repository root:

```sh
python3 -m unittest discover -s scripts -p test_check_distribution.py -v
python3 tests/fixtures/constitution_v030/distribution-scratch/record.py --output /private/tmp/qleisli-scratch-observation-new
python3 tests/fixtures/constitution_v030/distribution-scratch/record.py --baseline tests/fixtures/constitution_v030/distribution-scratch/before-check_distribution.py.txt --output /private/tmp/qleisli-scratch-baseline-new
```

Choose unused output directories. Reproduction creates only small disposable
repositories and files. Exact performed commands, Python identity, source hashes,
raw output and exit codes are in `validation.json` and `unit-tests.*`: **29 tests
passed**, including the existing distribution tests and seven lifecycle tests.
The additional CLI tests exercise argument plumbing and nonzero failure status
through the real `main` function with synthetic subprocess execution.

A real full distribution run on the final integrated candidate was not performed
for this change and remains a release requirement. The pre-existing real Lean
wrapper test is separately recorded in `../release-wrapper-integration/`.
