# Issue #317 selected-scope accounting

The user's direct request adds #317 to the existing 0.3.0 plan, producing
**111 selected Issues**: the original 108 plus #311, #315 and #317. The exact
[original Issue body](issue-317.md) and [request transcription](request.json)
were saved before implementation. All 20 original #317 criteria remain
required; this accounting change completes none of them. GitHub remains the
work ledger.

The release checker now requires #317 in G10 and all 13 groups/111 IDs. The
synthetic regression retains the earlier omitted-#311 and omitted-#315 cases
and adds omitted-#317 coverage. Historical candidates have their true counts:
108 omits #311/#315/#317, 109 omits #315/#317, and 110 omits #317. Each candidate
is rejected at all three relevant stages: outdated groups, absent reviewed
Issue criteria, and absent candidate acceptance evidence. Criterion, evidence,
same-run provenance, proof-status and artifact gates retain their existing rules.

[capture.py](capture.py) runs only fixed, bounded local Python/check commands;
it does not execute commands from JSON records or Issue text. The recorded
interpreter is Python 3.14. The command records and separate stdout/stderr are
under [before/](before/commands.json) and [after/](after/commands.json).

| Performed local check | Before | After |
| --- | --- | --- |
| Constitutional identity/continuity with trusted base `faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2` | Passed | Passed |
| Synthetic release readiness regression | 30 tests, passed | 31 tests, passed |
| CI profile regression | 6 tests, passed | 6 tests, passed |
| Documentation integrity | Not rerun for baseline | 1,798 local links, 19 Markdown anchors, 206 Lean root modules, passed |
| `git diff --check` for the four assigned live files | Not rerun for baseline | Passed |

The [after audit](after/metadata-audit.json) verifies that exactly the assigned
four live files changed among the 20 captured inputs. The protected original
texts, adoption/admission records, ledger, current evidence, CI selection code
and #317 body/request hashes are unchanged. Within each phase the captured
inputs remained identical before and after the checks. The source-map digest
is SHA-256 of the UTF-8 JSON path/content-hash map, sorted keys, indentation 2
and one final newline; these maps identify this bounded input set, not the
entire source tree.

The actual local CI classification is `full` suites and `full` proof lane.
That selection is recorded in [scope.json](after/scope.json); hosted CI was
not run here. Synthetic release receipts model provenance adversarially in
temporary repositories and are not real successful build/proof/release
receipts. No Cargo or Lean command was run for this accounting unit. Source
identity checks do not supply fresh proof replay, human adoption, guarantee
discharge or release approval. All three broader obligations and EXACT remain
pending, and both admitted ordinary QLV1 ownership/scope guarantees retain
their recorded scopes and premises.
