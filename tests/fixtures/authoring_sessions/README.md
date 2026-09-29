# Authoring and repair observations

These records begin in 0.1.8. They are development observations, not a controlled
LLM benchmark. No external model was invoked. Context is documented honestly,
including prior repository access and known workarounds; the exact deployed
model identifier and sampling settings were unavailable.

| Session | Kind and observed outcome |
| --- | --- |
| [Iterative QPE](iterative-qpe/session.json) | Informed new-source attempt, preserved before checking. Initial check passed; T on `|1>` returned `1001` within numerical tolerance. The five semantic tests subsequently passed. **Zero source repairs**; tiny numerical zero outcomes are retained in raw output. |
| [Product layout](type-layout-repair/session.json) | Curated replay of an existing rejected program. The same source rejects before/after, but now names the expected and actual trees. A previously known adapter checks/runs and returns `101`. One source revision, not blind model repair. |
| [Cleanup](cleanup-repair/session.json) | Curated replay of H H in restricted `with_computed`. The same source rejects before/after; the new hint identifies the three-argument contract form. A known explicit identity contract checks/runs and returns `0`. One source revision, not evidence that hints alone improve model success. |

The 0.2.0 continuation adds [shared QPE](shared-qpe-v020/session.json), whose original `CWord` spelling and parse failure are immutable history, and [sampled Grover](grover-trial-v020/session.json), whose missing-kernel repair precedes the implementation of sampling. Current design uses `CBits`; the appended Grover observation uses the unchanged repaired source with the new sampler.

Each `session.json` names the task, kind, baseline commit/version, context,
ordered attempts and observations. Each attempt contains a complete project,
source hashes and a reason; observations retain argument lists, exit codes and
actual JSON output or a test transcript. Before/after refers to diagnostic
changes in this working tree, not a version bump. First observations were
captured before modifying Rust diagnostics. No failed attempt was invented
for the initially successful QPE source.

For the next session:

1. Record the task, available context and author/model information **before**
   the first check. Preserve the untouched source as `attempt-01` and hash it.
2. Append actual diagnostic/execution observations. Never replace the initial
   result with a later run. Do not execute commands read from a record.
3. If source changes, save a full next attempt and its reason. Keep deliberate
   counterexamples outside the repair sequence and label curated replays.
4. Link semantic oracles, not just compilation. State context differences when
   comparing attempts; no model success-rate claim follows from these records.
5. Add newly exposed friction to the [backlog](../../../docs/v0.2.0-backlog.md).

`python3 scripts/check_authoring_sessions.py` checks hashes, source inventories,
context/observation presence and consistent recorded exits. It does not replay
commands, authenticate provenance or certify program meaning. Five checker
tests protect against lost/edited snapshots and contradictory records. Both
commands run in the docs CI job; Rust tests replay the QPE snapshot and repair
regressions. Existing records are retained even when diagnostics evolve.
