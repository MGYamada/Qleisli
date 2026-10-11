# Cancelled-producer observation, run 37364395462

This is a bounded, read-only partial observation of
[run 37364395462, attempt 1](https://github.com/MGYamada/Qleisli/actions/runs/37364395462).
At the recorded API observation, the run and Rust producer were still in progress.
It is not a terminal full-CI or release-readiness record.

The published head is `73aca78e13bc65125c4e533da48dd1318cf1cc51`, on
`codex/v0.3.0-foundation`. The actual changes checkout, HEAD log and selection
record identify tested merge `f7707f2aa4506ca354e93f46c702b63014f2ef44`, with
ordered parents `ba83c5c97a9c67bf3904423745b3e9c019a083cb` and that published
head. Selection requested `profile = full` and `proof_lane = full`; selecting
these lanes does not establish their completion. This is not evidence for the
later local original-AST implementation.

## Cancellation evidence and unavailable cause

| Producer | Job ID | Completion UTC | Runner / recorded steps | Conclusion |
| --- | --- | --- | --- | --- |
| Rust MSRV | 111949519787 | 2026-10-05 20:00:59 | ID 0, empty name / 0 | cancelled |
| Distribution | 111949519998 | 2026-10-05 20:01:01 | ID 0, empty name / 0 | cancelled |

Both records have `created_at` and `started_at` 19:45:56 UTC and
`ubuntu-latest` labels. Purpose-built step queries and full jobs metadata record
no steps. Purpose-built log retrieval returned actual `404 BlobNotFound` for
each job. Four check-run annotations exist for each, but their text could not
be retrieved through the connector allowlist. The unsuccessful annotation,
job-page and log requests are preserved in `access-failures.json`.

The actual cancellation cause is **not established**. These records do not
justify calling it a compiler/package failure, timeout, manual cancellation,
concurrency supersession, billing or runner-provisioning failure. The API's
`started_at` does not attest that a runner executed. Empty steps establish no
passed, failed or explicitly skipped MSRV/distribution test scope. The exact
tested workflow contains no explicit `timeout-minutes`; that absence does not
identify a platform cancellation reason.

At this snapshot, the eight producers comprise **five successes, two
cancellations and one live Rust job**. The separately successful changes job
is the sixth successful job overall, not a sixth successful producer. Other
successes are API conclusion context; their full logs were not independently
audited for this packet.

Rust job `111949519846` records steps 1 through 23 as successful. Step 24,
`check_input_corpus.py ... --exhaustive`, remains in progress, since 20:26:42
UTC. Its later Clippy, research, receipt and post-job steps are pending in this
snapshot. They are not recorded as failed, skipped or completed.

## Separate summary-size defect

The changes log at original line 13533 reports that `$GITHUB_STEP_SUMMARY`
upload was aborted: the 1024k limit was exceeded by actual 1322k content.
Changes still concludes success, and the separate selection artifact upload
succeeds (artifact ID `11367259323`, 70,382 bytes in the log).

A justified small CI presentation repair is to bound the human-readable
summary while retaining the complete selection artifact. This does not weaken
the selected checks. **No evidence connects this presentation failure to the
two cancelled producers.** Their missing successful producer results remain
CI blockers; a cancellation-specific repair needs the actual annotation or
platform reason first.

## Retained evidence and performed work

`run.json`, `jobs.json`, `check-runs.json` and `merge-commit.json` retain decoded
API JSON; `tested-workflow.yml` is the exact merge's workflow source. Provenance
and unsuccessful accesses are recorded separately. Two deterministic gzip
excerpts retain exact contiguous changes-log lines 1–205 and 13520–13576,
covering checkout/selection and the summary/artifact tail. Only 6,017 compressed
log bytes are retained. `log-excerpts.json` binds their compressed and decoded
bytes and the retrieved complete decoded log's digest. The full 1,758,700-byte
decoded changes log was hashed and then discarded; this packet does not
pretend to retain all logs or the 13,000-line changed-file list.

A fixed local metadata-only audit verified the raw run/jobs/commit source
bindings, counts, zero runner/step records, live step, workflow timeout absence
and excerpt hashes. It passed. The startup constitutional continuity guard
also returned exit 0 against reviewed base
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`; this is an identity/continuity check,
not a Lean replay or proof discharge. Applicable QS/PR/RS/EXACT duties and the
two scoped ordinary QLV1 guarantees retain their existing status and limits.

No log or fixture command was executed. No build/test/CLI/native execution,
build-archive download, restart, cancellation, configuration change or Git/GitHub
mutation was performed. Files here are additive evidence, not an adopted
interpretation, guarantee, release approval or issue-completion claim.
