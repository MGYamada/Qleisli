# Review repairs for 0.3.0-alpha

The 2026-10-04 review identified five defects and reproduced the classical
history timeout tracked under #278. This packet records their repairs; the
product remains an unpublished `0.3.0-alpha`.

- Function evidence borrows untrusted trees until iterative transport/type
  limits have been checked, avoiding recursive clones before validation.
  Subprocess regressions cover implementation, specification and signature.
- CLI JSON uses the parsed command, including the first positional argument
  in usage errors with leading options.
- Sized-source compaction treats an empty tensor as the empty identity while
  retaining zero-width quantum owners and phase.
- Release maintenance and archives share stable/alpha/beta/rc version forms
  whose Python normalization preserves SemVer ordering.
- Changes to either Lean audit select the full CI lane.
- `Raw.Observation.historySubset_eq` proves that the prefix fast path equals
  the previous membership test for all lawful equality instances. `history_eq`
  lifts this to the actual state check. Acceptance and work accounting remain
  unchanged; append-only classical histories improve from cubic to quadratic
  total time. Other capacity problems under #278 remain open.

[validation.json](validation.json) records source identities, performed checks,
timings and exclusions. [kernel-equivalence.json.gz](kernel-equivalence.json.gz)
contains observations from the same retained 799 inputs before and after the
history repair: all exit codes, stdout and stderr match, including work counts
(263 accepted). [history-differential.json.gz](history-differential.json.gz)
records another 164 comparisons (128 accepted), including small
observation programs and 0–2000 classical constants. The 6000-constant,
zero-qubit reproducer is retained as
[classical-6000.qirf.gz](classical-6000.qirf.gz).

Both Lean packages build and pass declaration audits, and both native roots
pass fresh replay. Existing theorem types, disabled external schemas, public
Rust signatures, constructors, capacities and trust obligations are retained.
The reviewed source and current harness pins were refreshed; historical
comparison inputs were not regenerated. These checks do not complete full
Soundness, source preservation, hosted release CI or publication.
