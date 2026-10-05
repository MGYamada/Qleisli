# Quantum Unit documentation and scheduling checks

These are actual local documentation, authoring-record integrity and Python
scheduler checks for the quantum Unit source unit. No Rust or Lean build, native
comparison, or recorded authoring command was executed by this record.

`initial/commands.json` retains exact argument lists, working directory,
environment overrides, UTC start times, durations, exit codes and separate
stdout/stderr hashes for eight commands:

- The first scheduler test run failed two assertions: the expected command count
  was still 87 and the required-command list omitted `quantum_unit_source`.
- `check_docs.py` passed: 1,741 local links, 15 Markdown anchors and 206 Lean root
  modules were checked.
- The pinned binary identified itself as mdBook 0.5.4 and built `docs`.
  `check_book.py` then passed: 20 HTML files, 753 local links and 277 anchors.
- `check_authoring_sessions.py` passed for all 23 records, 33 snapshots and 114
  observations, including the original quantum Unit study.
- `run_native_ci.py --help` documents that this runner has no `--check` option.
  Its normal execution prepares a native build, so it was not invoked. The
  separately saved `check_manifest.py` calls only the actual `load_tasks`
  validator. It validated 67 groups and 88 commands, including the new target.

The authorized scheduler-test correction changes only 87 to 88 and adds the
new target to the exact expected command list. The intermediate
`scheduler-fixed/` attempt added that expectation at the wrong position and
failed one assertion; its actual output is retained. `scheduler-final/` places
the command in the manifest's existing order and passes all 15 tests. The
pre-correction and intermediate test texts are retained beside the records and
their hashes match the inputs recorded for those attempts. The original
coverage digest and all other expected commands remain unchanged.

Each attempt binds 127 selected inputs before and after execution; none changed
during an attempt. These are selected documentation/checker/CI inputs, all
session manifests, the quantum Unit test and the complete original quantum Unit
study, not a full repository snapshot. `summary.json` separately records the
original study and translation inventory checks. The current recorder adds the
final attempt name; `recorder-initial.py.txt` retains the earlier recorder whose
hash appears in the first two attempts.

These checks validate documentation links, stored-record integrity and scheduler
policy. They do not establish source preservation, discharge a guarantee, run
hosted CI, or report the parent task's separate Rust validation as local evidence.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
