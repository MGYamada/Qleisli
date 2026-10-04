#!/usr/bin/env python3
"""Check ratification and interpretation identities and their pending ledger.

Hashes cannot independently authenticate a human transcript. This limited check
does not implement full constitutional CI (#141), prove a guarantee, approve a
release, or authorize a constitutional interpretation. A caller-supplied trusted
Git base additionally prevents replacement of already recorded identities.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import argparse
from pathlib import Path
import re
import subprocess
import sys

from check_ratification_packet import (
    GOVERNANCE_SNAPSHOT, PACKET_PATH, ROOT, SHA256, PacketError, check_packet,
    checked_file, exact_keys, json_object, read_file,
)


EVENT_PATH = "governance/ratification-2026.json"
LEDGER_PATH = "governance/guarantees.json"
EVENT_SHA256 = "3363bf5b25da3efe7094959972f25f7c9737ec3e0444f953ff0f0ee86155af3a"
CONSTITUTION_SHA256 = "40777370ec860891991bc89ef283f01a5db9a6be5480143f2e09e6014407452b"
GOVERNANCE_SHA256 = "60e8e6640ccbaccb08ecaca7507956e89458846dc532d5e50084e0e8ca079721"
PACKET_SHA256 = "d8acc219ba992c8833141543b3f68fe5a1c0e165403881a5c8b5ee15107af885"
ADOPTION_PATH = "governance/interpretations/initial-2026-adoption.json"
REVIEWED_PATH = "governance/interpretations/initial-2026-reviewed.txt"
BOOTSTRAP_PATH = "tests/fixtures/constitution_v030/bootstrap-ledger.json"
ADOPTION_SHA256 = "bb9e4b68024b4153515d3a2652feb3b64d16907522bf9575fd18e3a9e61a7c9e"
REVIEWED_SHA256 = "7a79a18ad66e4b7cdaa87865eff1bf87ce933da758461cb45cc13a87fb1555b3"
BOOTSTRAP_SHA256 = "44c504cfd5b34e01126504d18e278a6991b9dac2d3de13582ff4c3c22eda62d6"
ADMISSION_PATH = "governance/guarantees/initial-2026-admission.json"
ADMISSION_SHA256 = "9f20661fd98ec56c58286b70f4e9d9f49c76570313b5ddc90ae4685d4e251dd2"
PENDING_PATH = "tests/fixtures/constitution_v030/pending-ledger.json"
PENDING_SHA256 = "248e25655a89becea9c0ca008102f50db8ea096248b2c2624b671445866d9481"
PROPOSAL_PATH = "governance/proposals/initial-guarantees.json"
PROPOSAL_SHA256 = "bf9eb89d9ebadd41f16f40c5896b824b0e04fe1655264e102fb179948fa06c02"
CURRENT_PATH = "governance/guarantees/current-evidence.json"
GUARANTEE_IDS = ("QS-QLV1-OWNERSHIP-2026-01", "QS-QLV1-SCOPE-2026-01")
RATIFICATION_PATHS = (
    EVENT_PATH, "CONSTITUTION.md", GOVERNANCE_SNAPSHOT, PACKET_PATH,
    "tests/fixtures/constitution_v030/issue-129.json",
    "tests/fixtures/constitution_v030/baseline.json",
)
INTERPRETATION_PATHS = (ADOPTION_PATH, REVIEWED_PATH, BOOTSTRAP_PATH)
GUARANTEE_PATHS = (
    ADMISSION_PATH, PENDING_PATH, PROPOSAL_PATH,
    "governance/guarantees/initial-2026-semantic-sources.json",
    "tests/fixtures/constitution_v030/initial-guarantees/validation.json",
    "tests/fixtures/constitution_v030/initial-guarantees/reviewed-source.tar.gz",
    "tests/fixtures/constitution_v030/initial-guarantees/reviewed-registry.json",
    "tests/fixtures/constitution_v030/initial-guarantees/CurrentBinding.lean",
    "tests/fixtures/constitution_v030/initial-guarantees/current-binding.stdout.txt",
    "tests/fixtures/constitution_v030/initial-guarantees/current-binding.stderr.txt",
    "tests/fixtures/constitution_v030/initial-guarantees/Review.lean",
    "tests/fixtures/constitution_v030/initial-guarantees/review-types.stdout.txt",
    "tests/fixtures/constitution_v030/initial-guarantees/review-types.stderr.txt",
    "tests/fixtures/constitution_v030/initial-guarantees/native-main-replay.stdout.txt",
    "tests/fixtures/constitution_v030/initial-guarantees/native-main-replay.stderr.txt",
    "tests/fixtures/constitution_v030/ownership-rename-registry.json",
)
CONTINUITY_ROOT = "tests/fixtures/constitution_v030/initial-guarantees-continuity"
CONTINUITY_BASELINE = f"{CONTINUITY_ROOT}/baseline.json"
CONTINUITY_PATHS = tuple(f"{CONTINUITY_ROOT}/{name}" for name in (
    "baseline.json", "Extract.lean", "reviewed-expressions.json.gz",
    "historical-setup.json", "historical-build-command.json",
    "historical-build.stdout.txt", "historical-build.stderr.txt",
    "historical-extraction-command.json", "empty.stderr.txt",
))
FROZEN_PATHS = RATIFICATION_PATHS + INTERPRETATION_PATHS + GUARANTEE_PATHS + CONTINUITY_PATHS
INTERPRETATIONS = {
    "QS-2026-01": ("QS", "1. Candidate QS-2026-01 — Meaning of accepted programs"),
    "PR-2026-01": ("PR", "2. Candidate PR-2026-01 — Accepted target realizations"),
    "RS-2026-01": ("RS", "3. Candidate RS-2026-01 — Quantitative resource accountability"),
}
LEDGER_LISTS = ("binding_interpretations", "pending_obligations", "discharged_guarantees")
BOOTSTRAP_SCOPE = (
    "No formal guarantee has yet been admitted to this constitutional ledger. "
    "Existing proofs and the open QS/PR/RS duties retain their recorded status "
    "outside this bootstrap inventory. Empty lists neither discharge nor waive those duties."
)
LEDGER_SCOPE = (
    "QS-2026-01, PR-2026-01 and RS-2026-01 are binding pending obligations under "
    "their exact adopted text. Existing proofs retain their scoped status but "
    "have not been admitted as constitutional discharges. No production-wide "
    "QS, PR or quantitative RS discharge is claimed."
)
ADMITTED_SCOPE = (
    "Three binding interpretations retain their broader pending obligations. "
    "Two scoped ordinary QLV1 guarantees have been formally discharged and admitted "
    "under the recorded human adequacy judgment. No production-wide QS, PR or "
    "quantitative RS discharge is claimed."
)


def require_fields(value, expected, label):
    exact_keys(value, expected, label)
    # Python's bool/int equality must not let true stand in for version 1.
    for key, wanted in expected.items():
        if type(value[key]) is not type(wanted) or value[key] != wanted:
            raise PacketError(f"{label}: unexpected {key}")


def validate_event(event):
    exact_keys(event, {"format", "version", "edition", "effective_date", "effective_timezone",
                       "adopter", "constitution", "governance_adoption", "guardian_appointment",
                       "provenance", "recording", "scope"}, "ratification event")
    require_fields({key: event[key] for key in ("format", "version", "edition", "effective_date", "effective_timezone")},
                   dict(format="qleisli.human-ratification", version=1, edition="2026",
                        effective_date="2026-10-04", effective_timezone="Asia/Tokyo"), "ratification event")
    require_fields(event["adopter"], dict(name="Masahiko G. Yamada", capacity="natural-human project maintainer"), "adopter")
    require_fields(event["constitution"], dict(path="CONSTITUTION.md", sha256=CONSTITUTION_SHA256), "constitution binding")
    require_fields(event["governance_adoption"], dict(reviewed_path="GOVERNANCE.md", snapshot_path=GOVERNANCE_SNAPSHOT,
                                                    sha256=GOVERNANCE_SHA256), "governance adoption")
    require_fields(event["guardian_appointment"], dict(office="Constitution Guardian Office", holder="Masahiko G. Yamada",
                                                     form="sole natural-human holder"), "guardian appointment")
    for field, keys in (("provenance", {"kind", "conversation_id", "question_item_id", "question", "answer",
                                       "first_clock_observation_after_reply_utc", "timestamp_note"}),
                        ("recording", {"transcriber", "authority", "authentication_limit"})):
        exact_keys(event[field], keys, field)
        if any(type(value) is not str or not value.strip() for value in event[field].values()):
            raise PacketError(f"{field}: expected nonempty recorded strings")
    if event["provenance"]["kind"] != "direct-user-message":
        raise PacketError("provenance: expected the recorded direct human message")
    if type(event["scope"]) is not str or not event["scope"].strip():
        raise PacketError("ratification event: missing scope")
    # The fixed complete event digest, not the presence of a name or an answer
    # string, binds these fields to the event reviewed at introduction.


def validate_adoption(event):
    exact_keys(event, {"format", "version", "edition", "adopted_on", "timezone", "guardian",
                       "interpretation_ids", "reviewed_packet", "provenance", "recording", "status", "scope"},
               "interpretation adoption")
    require_fields({key: event[key] for key in ("format", "version", "edition", "adopted_on", "timezone", "status")},
                   dict(format="qleisli.human-interpretation-adoption", version=1, edition="2026",
                        adopted_on="2026-10-04", timezone="Asia/Tokyo", status="binding-pending-discharge"),
                   "interpretation adoption")
    exact_keys(event["guardian"], {"name", "capacity", "appointment_record"}, "adopting guardian")
    require_fields({key: event["guardian"][key] for key in ("name", "capacity")},
                   dict(name="Masahiko G. Yamada", capacity="sole natural-human holder of the Constitution Guardian Office"),
                   "adopting guardian")
    require_fields(event["guardian"]["appointment_record"], dict(path=EVENT_PATH, sha256=EVENT_SHA256),
                   "guardian appointment binding")
    if type(event["interpretation_ids"]) is not list or event["interpretation_ids"] != list(INTERPRETATIONS):
        raise PacketError("interpretation adoption: require exactly the three adopted QS/PR/RS identifiers")
    require_fields(event["reviewed_packet"], dict(reviewed_path="docs/src/design/initial-interpretations.md",
                                                snapshot_path=REVIEWED_PATH, sha256=REVIEWED_SHA256),
                   "reviewed interpretation binding")
    for field, keys in (("provenance", {"kind", "conversation_id", "question_item_id", "question", "answer",
                                       "first_clock_observation_after_reply_utc", "timestamp_note"}),
                        ("recording", {"transcriber", "authority", "authentication_limit"})):
        exact_keys(event[field], keys, f"interpretation {field}")
        if any(type(value) is not str or not value.strip() for value in event[field].values()):
            raise PacketError(f"interpretation {field}: expected nonempty recorded strings")
    if event["provenance"]["kind"] != "direct-user-message":
        raise PacketError("interpretation provenance: expected the recorded direct human message")
    if type(event["scope"]) is not str or not event["scope"].strip():
        raise PacketError("interpretation adoption: missing scope")
    # As for ratification, the full pinned event digest binds the transcript;
    # these strings alone cannot authenticate or create a human decision.


def validate_reviewed_sections(data):
    try:
        text = data.decode("utf-8")
    except UnicodeError as error:
        raise PacketError("reviewed interpretation snapshot: expected UTF-8") from error
    headings = [line[3:] for line in text.splitlines() if line.startswith("## ")]
    for _, section in INTERPRETATIONS.values():
        if headings.count(section) != 1:
            raise PacketError(f"reviewed interpretation snapshot: missing or duplicated section {section}")


def validate_admission(event):
    exact_keys(event, {"format", "version", "edition", "admitted_on", "timezone", "status", "guardian", "guarantee_ids",
                       "reviewed_proposal", "evidence_at_admission", "previous_ledger", "provenance", "recording", "scope"}, "scoped guarantee admission")
    require_fields({key: event[key] for key in ("format", "version", "edition", "admitted_on", "timezone", "status", "guarantee_ids")},
                   dict(format="qleisli.human-guarantee-admission", version=1, edition="2026", admitted_on="2026-10-04", timezone="Asia/Tokyo",
                        status="scoped-guarantees-admitted", guarantee_ids=list(GUARANTEE_IDS)), "scoped guarantee admission")
    require_fields(event["guardian"], dict(name="Masahiko G. Yamada", capacity="sole natural-human holder of the Constitution Guardian Office",
                                        appointment_record=dict(path=EVENT_PATH, sha256=EVENT_SHA256)), "admitting guardian")
    require_fields(event["reviewed_proposal"], dict(path=PROPOSAL_PATH, sha256=PROPOSAL_SHA256), "admitted proposal")
    require_fields(event["previous_ledger"], dict(path=PENDING_PATH, sha256=PENDING_SHA256), "prior pending ledger")
    require_fields(event["evidence_at_admission"], dict(
        validation=dict(path="tests/fixtures/constitution_v030/initial-guarantees/validation.json", sha256="0afcb38ce713a998cb8025d4e6b4406a9e1ac023cd04cf273eaae67a58508720"),
        reviewed_source_archive=dict(path="tests/fixtures/constitution_v030/initial-guarantees/reviewed-source.tar.gz", sha256="8cdfc71a2ca583a3c41a46717b847e6ba904ccffdbb57a768b360d0c88c9e6f3"),
        reviewed_registry=dict(path="tests/fixtures/constitution_v030/initial-guarantees/reviewed-registry.json", sha256="ac39211f5a94a0b6b14a794d4bbedc614940cb2b82e4850983df7fc8830759ee")), "admission evidence")
    for field, keys in (("provenance", {"kind", "conversation_id", "question_item_id", "question", "answer",
                                      "first_clock_observation_after_reply_utc", "timestamp_note"}),
                        ("recording", {"transcriber", "authority", "authentication_limit"})):
        exact_keys(event[field], keys, f"admission {field}")
        if any(type(value) is not str or not value.strip() for value in event[field].values()):
            raise PacketError(f"admission {field}: expected nonempty recorded strings")
    if event["provenance"]["kind"] != "direct-user-message" or type(event["scope"]) is not str or not event["scope"].strip():
        raise PacketError("admission: missing recorded human provenance/scope")


def validate_ledger(ledger, *, label="guarantee ledger", allow_bootstrap=False):
    version = ledger.get("version") if type(ledger) is dict else None
    if type(version) is not int or version not in {1, 2, 3}:
        raise PacketError(f"{label}: unsupported ledger schema; cannot discard obligations from another schema")
    exact_keys(ledger, {"format", "version", "edition", "status", "ratification", "scope", *LEDGER_LISTS}
               | ({"current_evidence"} if version == 3 else set()), label)
    if version < 3 and not allow_bootstrap:
        raise PacketError(f"{label}: active ledger must be v3; scoped guarantees cannot roll back to pending or bootstrap")
    require_fields({key: ledger[key] for key in ("format", "version", "edition", "status", "scope")},
                   dict(format="qleisli.guarantee-ledger", version=version, edition="2026",
                        status={1: "bootstrap-awaiting-initial-interpretations", 2: "active-pending-discharge", 3: "active-scoped-guarantees"}[version],
                        scope={1: BOOTSTRAP_SCOPE, 2: LEDGER_SCOPE, 3: ADMITTED_SCOPE}[version]), label)
    require_fields(ledger["ratification"], dict(path=EVENT_PATH, sha256=EVENT_SHA256), f"{label} ratification")
    for field in LEDGER_LISTS if version == 1 else (("discharged_guarantees",) if version == 2 else ()):
        if type(ledger[field]) is not list or ledger[field]:
            raise PacketError(f"{label}: {field} must be empty in this schema; formal discharge needs a separately audited admission schema, not rollback or fabricated evidence")
    if version == 1:
        return version
    if version == 3:
        entries = ledger["discharged_guarantees"]
        if type(entries) is not list or len(entries) != len(GUARANTEE_IDS):
            raise PacketError(f"{label}: both admitted scoped guarantees must be retained")
        seen = set()
        for entry in entries:
            exact_keys(entry, {"id", "jurisdiction", "interpretation", "admission", "reviewed_proposal", "proposal_entry"}, f"{label} discharged guarantee")
            identifier = entry["id"]
            if type(identifier) is not str or identifier not in GUARANTEE_IDS or identifier in seen:
                raise PacketError(f"{label}: unknown or duplicate admitted guarantee")
            seen.add(identifier)
            require_fields(entry, dict(id=identifier, jurisdiction="QS", interpretation="QS-2026-01", proposal_entry=identifier,
                                      admission=dict(path=ADMISSION_PATH, sha256=ADMISSION_SHA256),
                                      reviewed_proposal=dict(path=PROPOSAL_PATH, sha256=PROPOSAL_SHA256)), f"{label} discharged guarantee")
        exact_keys(ledger["current_evidence"], {"path", "sha256"}, f"{label} current evidence")
        if (ledger["current_evidence"]["path"] != CURRENT_PATH or type(ledger["current_evidence"]["sha256"]) is not str
                or SHA256.fullmatch(ledger["current_evidence"]["sha256"]) is None):
            raise PacketError(f"{label}: invalid current evidence binding")

    for field, id_field, keys in (
        ("binding_interpretations", "id", {"id", "jurisdiction", "adoption", "reviewed_text", "section"}),
        ("pending_obligations", "interpretation", {"interpretation", "formalization_status", "proof_status", "evidence_bindings"}),
    ):
        rows = ledger[field]
        if type(rows) is not list or len(rows) != len(INTERPRETATIONS):
            raise PacketError(f"{label}: {field} must retain all three adopted obligations")
        seen = set()
        for row in rows:
            exact_keys(row, keys, f"{label} {field}")
            identifier = row[id_field]
            if type(identifier) is not str or identifier not in INTERPRETATIONS or identifier in seen:
                raise PacketError(f"{label}: unknown or duplicate {field} identifier")
            seen.add(identifier)
            jurisdiction, section = INTERPRETATIONS[identifier]
            if field == "binding_interpretations":
                require_fields(row, dict(id=identifier, jurisdiction=jurisdiction, section=section,
                                        adoption=dict(path=ADOPTION_PATH, sha256=ADOPTION_SHA256),
                                        reviewed_text=dict(path=REVIEWED_PATH, sha256=REVIEWED_SHA256)),
                               f"{label} interpretation {identifier}")
            else:
                require_fields(row, dict(interpretation=identifier, formalization_status="pending-coverage-and-adequacy-review",
                                        proof_status="not-discharged", evidence_bindings=[]),
                               f"{label} pending obligation {identifier}")
    return version


def git(root, *args):
    try:
        result = subprocess.run(["git", "-C", str(root), *args], capture_output=True, check=False)
    except OSError as error:
        raise PacketError("cannot execute Git for trusted-base verification") from error
    if result.returncode:
        raise PacketError("Git trusted-base verification failed; the base must be an available commit")
    return result.stdout


def base_file(root, commit, name):
    listing = git(root, "ls-tree", "-z", commit, "--", name)
    if not listing:
        return None
    records = listing.rstrip(b"\0").split(b"\0")
    if len(records) != 1:
        raise PacketError(f"trusted base: ambiguous artifact {name}")
    try:
        metadata, found = records[0].split(b"\t", 1)
        mode, kind, object_id = metadata.split()
    except ValueError as error:
        raise PacketError("trusted base: malformed tree metadata") from error
    if found != name.encode() or mode not in {b"100644", b"100755"} or kind != b"blob":
        raise PacketError(f"trusted base: {name} must be a regular file")
    return git(root, "cat-file", "blob", object_id.decode("ascii"))


def check_base(root, base_ref):
    if type(base_ref) is not str or not base_ref or any(ord(ch) < 32 for ch in base_ref):
        raise PacketError("trusted base must be a nonempty Git ref")
    raw = git(root, "rev-parse", "--verify", "--end-of-options", base_ref + "^{commit}")
    commit = raw.decode("ascii").strip()
    if re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", commit) is None:
        raise PacketError("trusted base did not resolve to one commit")
    previous = {name: base_file(root, commit, name) for name in (*FROZEN_PATHS, LEDGER_PATH)}
    # Each stage protects its own recorded artifacts. In particular, the first
    # continuity baseline postdates admission; an admitted base without that
    # later evidence is a valid migration source, not an incomplete admission.
    for anchor, names in ((EVENT_PATH, RATIFICATION_PATHS), (ADOPTION_PATH, INTERPRETATION_PATHS),
                          (ADMISSION_PATH, GUARANTEE_PATHS), (CONTINUITY_BASELINE, CONTINUITY_PATHS)):
        already_recorded = previous[anchor] is not None
        for name in names:
            before = previous[name]
            if before is None:
                if already_recorded:
                    raise PacketError(f"trusted base: recorded stage is missing {name}; cannot treat it as a new introduction")
                continue
            if read_file(root, name) != before:
                raise PacketError(f"trusted base: protected artifact changed: {name}")
    before_ledger = previous[LEDGER_PATH]
    if before_ledger is None:
        if any(previous[path] is not None for path in (EVENT_PATH, ADOPTION_PATH, ADMISSION_PATH)):
            raise PacketError("trusted base: recorded ratification has no ledger; cannot silently bootstrap it")
    else:
        if previous[EVENT_PATH] is None:
            raise PacketError("trusted base: a recorded ledger is missing its ratification event")
        version = validate_ledger(json_object(before_ledger, "trusted-base ledger"),
                                  label="trusted-base ledger", allow_bootstrap=True)
        if version == 1:
            if previous[ADOPTION_PATH] is not None or previous[ADMISSION_PATH] is not None:
                raise PacketError("trusted base: an adopted interpretation event cannot retain a bootstrap ledger")
            if read_file(root, BOOTSTRAP_PATH) != before_ledger:
                raise PacketError("trusted base: archived bootstrap must preserve the previous ledger bytes")
        elif previous[ADOPTION_PATH] is None:
            raise PacketError("trusted base: active v2 ledger is missing its interpretation adoption event")
        elif version == 2:
            if previous[ADMISSION_PATH] is not None:
                raise PacketError("trusted base: admitted scoped guarantees cannot retain a pending-only ledger")
            if read_file(root, PENDING_PATH) != before_ledger:
                raise PacketError("trusted base: archived pending ledger must preserve the previous ledger bytes")
        elif previous[ADMISSION_PATH] is None:
            raise PacketError("trusted base: active v3 ledger is missing its scoped guarantee admission event")


def check_constitution(root=ROOT, *, base_ref=None, require_release_ready=False):
    root = Path(root)
    if base_ref is not None:
        check_base(root, base_ref)
    event = json_object(checked_file(root, EVENT_PATH, EVENT_SHA256), EVENT_PATH)
    validate_event(event)
    checked_file(root, "CONSTITUTION.md", CONSTITUTION_SHA256)
    checked_file(root, GOVERNANCE_SNAPSHOT, GOVERNANCE_SHA256)
    checked_file(root, PACKET_PATH, PACKET_SHA256)
    check_packet(root)
    bootstrap = json_object(checked_file(root, BOOTSTRAP_PATH, BOOTSTRAP_SHA256), "archived bootstrap ledger")
    if validate_ledger(bootstrap, label="archived bootstrap ledger", allow_bootstrap=True) != 1:
        raise PacketError("archived bootstrap ledger must retain schema v1")
    adoption = json_object(checked_file(root, ADOPTION_PATH, ADOPTION_SHA256), ADOPTION_PATH)
    validate_adoption(adoption)
    validate_reviewed_sections(checked_file(root, REVIEWED_PATH, REVIEWED_SHA256))
    admission = json_object(checked_file(root, ADMISSION_PATH, ADMISSION_SHA256), ADMISSION_PATH)
    validate_admission(admission)
    pending = json_object(checked_file(root, PENDING_PATH, PENDING_SHA256), "archived pending ledger")
    if validate_ledger(pending, label="archived pending ledger", allow_bootstrap=True) != 2:
        raise PacketError("archived pending ledger must retain schema v2")
    ledger = json_object(read_file(root, LEDGER_PATH), LEDGER_PATH)
    validate_ledger(ledger)
    checked_file(root, CURRENT_PATH, ledger["current_evidence"]["sha256"])
    # The initial proposal/meaning remains historical; separate mutable evidence
    # must bind the admitted scopes to today's source and recorded proof checks.
    from check_initial_guarantees import check as check_guarantee_evidence
    check_guarantee_evidence(root)
    if require_release_ready:
        raise PacketError("release readiness is not established: two scoped QLV1 guarantees are admitted, but the three broader binding interpretations remain pending; full constitutional enforcement and release readiness are incomplete, and admission is not release approval")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--base-ref", help="caller-selected trusted Git commit/ref for non-rollback checks")
    parser.add_argument("--require-release-ready", action="store_true")
    args = parser.parse_args(argv)
    try:
        check_constitution(args.root, base_ref=args.base_ref, require_release_ready=args.require_release_ready)
    except (PacketError, OSError) as error:
        print(f"constitutional record integrity: {error}", file=sys.stderr)
        return 1
    print("Recorded edition 2026 ratification, appointment, interpretation adoption and two scoped guarantee admissions verified. "
          "Human transcript authenticity is not independently established by hashes. "
          "Three broader binding interpretations remain pending; current source/evidence identity is checked, not a fresh Lean replay. "
          "full constitutional CI and release approval remain separate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
