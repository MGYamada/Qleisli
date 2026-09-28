# Reproducing the distribution gate

The [distribution checker](../scripts/check_distribution.py) validates an
actual clean Git `HEAD`, its production `.crate`, and a complete repository
source archive. It supports [B019-6](v0x-roadmap.md#v019-acceptance-boundary)
and the [release policy](versioning.md#release-records-and-validation).
Running helper tests or selecting a package version does not satisfy this gate.

Run from the candidate checkout with installed primary Rust, Git and Python:

```sh
python3 scripts/test_check_distribution.py
python3 scripts/check_distribution.py --report /tmp/qleisli-distribution.json
```

Choose a new report path for every run. The report and its companion artifact
directory must be outside the checkout. Optional `--target-dir` selects an
external build directory; otherwise build outputs stay with the artifacts.
All Cargo commands are offline; this script neither installs dependencies nor
publishes anything. Tracked changes and untracked files reject the candidate;
ignored build outputs do not enter the archive. The script refuses to overwrite
an old report and retains failure logs as well as successful results.

The checker performs these concrete checks:

1. Bind the candidate to its commit and tree, then inventory every tracked
   regular file's Git blob bytes and executable mode. Tracked symlinks or
   submodules currently reject this distribution profile.
2. Generate a tar source archive with Git, compare every file and mode with
   that inventory, reject missing/extra/changed files and unsafe tar entries,
   and extract only validated regular files. No tracked file is intentionally
   excluded. This includes the nested research package, Lean sources/toolchain
   records, tests, original upstream files and documentation.
3. Replay the corpus metadata checker from the extracted tree. Derive upstream
   and final translation inventories from the frozen manifest, retain their
   hashes, and require project/corpus licenses, notices and attribution files.
4. Run Cargo's ordinary package creation and build verification on the clean
   candidate. Compare the archive with Cargo's listing and the tracked source.
   Cargo's normalized manifest, generated lockfile and VCS record are explicit
   generated exceptions; `Cargo.toml.orig` must preserve the original manifest.
   The VCS record must identify the same clean candidate commit and root.
   Extract the exact package and use offline `cargo metadata --locked` to
   validate its normalized package identity, license, dependencies, features,
   build targets and lockfile;
   generated metadata has ordinary non-executable file modes.
5. Record the exact tracked files Cargo excludes. The non-published nested
   research package is excluded from the production `.crate`; it is retained
   in the complete source archive. Both products retain the required corpus
   originals, translations, licenses and notices.
6. Build and run all-target production and research Rust tests from the
   extracted source archive. Recheck that the original candidate is still the
   same clean commit/tree and that no archived tracked file changed during
   the builds.

The external JSON report records the candidate, tracked hashes/modes, artifact
paths and SHA-256 hashes, Cargo exclusions, tool versions, each build/check
command and exit status, log paths, and overall result. Archive identity is
recorded for that run; byte-for-byte reproducible compiler outputs across
different hosts are not promised.

This is a focused distribution check. It does not rerun the MSRV matrix, Lean
build/axiom audit or the full release checks, and it does not create a tag, push,
or publish. Those remain separately recorded evidence on the same candidate.
Successful Cargo verification establishes that the production package builds;
the all-target suites run against the complete source archive, where the nested
research and proof sources are present.

The [helper tests](../scripts/test_check_distribution.py) exercise dirty/staged/
untracked candidates, exact bytes and executable modes, missing or corrupted
notices and source, manifest-driven inventories, wrong VCS identity, package
exclusions, unsafe paths, duplicate entries, links and special files. These use
temporary local repositories and fixtures, not an invented release result.
