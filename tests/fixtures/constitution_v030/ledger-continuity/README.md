# Append-only guarantee ledger policy

This fixture records the schema-v4 mechanical ledger migration. It makes no new
human admission, interpretation, proof or release-readiness claim. The live
ledger retains the same two scoped QLV1 guarantees and three broader pending
obligations. No source-language or executable Lean definition changes here.

`governance/guarantees/initial-v3-ledger.json` is the exact
`fae0e6a:governance/guarantees.json` Git blob, SHA-256
`cd80e99f85da974b10af763af96f595c44acee88fc07fb34b406c093b9f8225e`.
Its old evidence binding is historical; it does not select today's checker.
Existing approved text, events and elaborated continuity baselines stay frozen.

## Identity and dispatch

A guarantee's canonical identity is SHA-256 of UTF-8 JSON containing `edition`
(`2026`) and its six typed fields: `id`, `jurisdiction`, `interpretation`,
`admission`, `reviewed_proposal`, and `proposal_entry`. JSON keys are sorted,
separators are `,` and `:`, and strings are emitted without ASCII escaping.
There is no Unicode normalization. Object key ordering and JSON whitespace do
not change identity; any admitted value does. The exact proposal digest and
entry selector retain its reviewed scope, premises, property and meaning.
Unknown fields, duplicate JSON keys and wrong types are rejected.

Current evidence is deliberately outside that immutable identity. Each
`current_bindings` row has exact guarantee IDs, a registered fixed verifier
profile, and a file/digest reference. Profiles bind the **canonical identities**
they can verify, not just names. The current QLV1 profile cannot verify another
property by relabelling its existing proof result. No candidate JSON controls a
Python import, command line, module path or registration.

Human-record registration and evidence-verifier registration are separate
reviewed code. The production table contains only the existing actual admission
and the existing QLV1 verifier. Future registrations must refer to an actual
reviewed human event and its exact proposal; constructing Python registration
objects or passing tests does not confer authority. This unit does not add
automatic admissions or a general semantic-transport mechanism.

`check_constitution.py --base-ref REF` preserves every old v3/v4 entry and its
admission/proposal files. Historical v4 may contain a strict subset of today's
registered entries, allowing append-only migration. The active ledger must
contain the entire registered set, with matching current verifier coverage.
Unknown historical entries fail closed instead of being discarded. The fixed
v3 archive alone does not stand in for checking the caller's actual trusted
base. This remains a caller-selected trusted-base check; candidate-controlled
records cannot independently authenticate human decisions or protect jointly
replaced checker code without a trusted review/base.

`--verify-lean` dispatches fixed verifiers, then repeats source-only checks after
all commands. The dispatcher captures ledger, frozen artifacts, admission
records, proposals and current evidence, and rejects changes during verification.
The QLV1 verifier retains its own source/artifact snapshot checks and actual
Lean extraction comparison. Default mode only checks recorded source/evidence
identity. It does not claim a fresh Lean run.

## Regression scope

`scripts/test_check_constitution.py` uses temporary repositories and the immutable
reviewed-source fixture. Its synthetic third guarantee, event and verifier are
explicit **test-only** injections into Python policy functions; they are never
written to the live ledger or available through the CLI/environment. Tests cover
v3-to-v4 migration, v4 append, deletion/weakening/rollback, unknown prior entries,
canonical identity, profile substitution, missing evidence, symlinks/duplicate
fields and simultaneous ledger/evidence changes. Dispatcher mocks verify policy
and routing; they are not additional Lean proof evidence.

The release-readiness option remains the pre-existing fail-closed placeholder.
This unit does not decide prerelease claim policy or equate all pending duties
with a blanket prohibition of pre-v1 releases. Full constitutional enforcement
and release conditions remain separate work.

## Recorded validation and independent counterexample

The root-level `validation.json` records the initial 49-test policy run and
source-only CLI check. Both passed, but this was **before** the independent
snapshot-race finding; it is retained as development evidence, not final
acceptance. `final/validation.json` records the final 54-test run and 33 initial-guarantee tests and source-only
CLI/base verification after repair. The original and repaired checker/helper
bytes and the original test source are preserved under `snapshot-race/`.

The independent probe changes only temporary-file read timing. It starts and
ends with an invalid Constitution snapshot, exposes the genuine Constitution
only to both real hash-checked intermediate reads, and invokes the actual
source-only QLV1 verifier. The initial dispatcher accepted this inconsistent
snapshot. The repaired dispatcher rejects it with `frozen artifact snapshot:
SHA-256 mismatch: CONSTITUTION.md`. This is a Python enforcer race, not a defect
in the ratified Constitution, an admission, or a Lean theorem.

`frozen-identities.json` now fixes the exact identities of all 35 previously
protected files. Its own digest is fixed in checker code and it is protected as
the 36th historical artifact. The checker directly authenticates the captured
bytes, checks the complete path set, and requires those same bytes after all
verification. Valid intermediate rereads cannot authenticate an invalid
initial/final snapshot. Future mutable evidence remains outside this frozen
manifest and is authenticated by its captured ledger digest and fixed profile.

`snapshot-race-storage.json` maps preserved diagnostic/source files to their
original paths and exact hashes. The saved commands retain their actual local
paths; the historical observations are not represented as fresh CI executions.
No maximum-size quantum cases or new human admissions are involved. Live Lean
replay is recorded separately by the integrating task.


The independent mutable-evidence probe under `evidence-substitution/` addresses
a separate dispatcher connection. It leaves invalid evidence selected by the
ledger, while only the fixed profile's actual `read_file` sees a temporary valid
record. Comparing initial/final file bytes alone formerly accepted this. The
profile now returns the SHA-256 of the exact `current_bytes` it validated. Every
dispatch call, including the final source-only pass, must return the same digest
as the captured ledger reference. The identical timing probe now rejects the
mismatch. `evidence-substitution-storage.json` binds its preserved before/after
checker sources, commands and outputs. The initial checker change adds only this
returned input identity; its proof checks and CLI output are unchanged.
