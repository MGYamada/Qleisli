#!/usr/bin/env python3
"""Typed append-only guarantee identities and fixed current-evidence dispatch.

Registration is reviewed checker code, not authority supplied by a candidate
ledger. Hashes bind recorded human decisions; they do not authenticate humans.
This module executes no command, module, or verifier named by record contents.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

from dataclasses import dataclass
import hashlib
import json
from pathlib import PurePosixPath
import re
from typing import Callable

from check_ratification_packet import PacketError, SHA256, checked_file, exact_keys, json_object, read_file


IDENTITY_FIELDS = frozenset({"id", "jurisdiction", "interpretation", "admission",
                             "reviewed_proposal", "proposal_entry"})
IDENTIFIER = re.compile(r"[A-Z][A-Z0-9-]*")
PROFILE = "qlv1-structural-identity-v1"
V3_PATH = "governance/guarantees/initial-v3-ledger.json"
V3_SHA256 = "cd80e99f85da974b10af763af96f595c44acee88fc07fb34b406c093b9f8225e"
V4_SCOPE = (
    "Registered scoped guarantees retain their admitted meanings and current evidence bindings. "
    "The three binding interpretations retain their broader pending obligations. "
    "No production-wide QS, PR or quantitative RS discharge is claimed."
)


@dataclass(frozen=True)
class AdmissionRegistration:
    """Immutable identities from an explicitly reviewed human admission record.

    Future registrations require reviewing the real event, its exact proposal,
    and the selected identities. Constructing this object is not an admission.
    Tests may explicitly inject synthetic registrations into policy functions;
    the production CLI never loads a registration from data or the environment.
    """

    entries: tuple[dict, ...]


@dataclass(frozen=True)
class VerifierProfile:
    name: str
    identities: tuple[tuple[str, str], ...]
    evidence_path: str
    verify: Callable


def validate_ref(value, label):
    exact_keys(value, {"path", "sha256"}, label)
    path = value["path"]
    if (type(path) is not str or not path or "\\" in path
            or any(ord(ch) < 32 for ch in path)
            or PurePosixPath(path).is_absolute()
            or any(part in {"", ".", ".."} for part in path.split("/"))):
        raise PacketError(f"{label}: require a confined repository path")
    if type(value["sha256"]) is not str or SHA256.fullmatch(value["sha256"]) is None:
        raise PacketError(f"{label}: require a SHA-256 digest")


def immutable_entry(entry, *, hashed, label="guarantee ledger entry"):
    exact_keys(entry, IDENTITY_FIELDS | ({"identity_sha256"} if hashed else set()), label)
    for field in ("id", "interpretation", "proposal_entry"):
        if type(entry[field]) is not str or IDENTIFIER.fullmatch(entry[field]) is None:
            raise PacketError(f"{label}: invalid {field}")
    if type(entry["jurisdiction"]) is not str or entry["jurisdiction"] not in {"QS", "PR", "RS"}:
        raise PacketError(f"{label}: invalid jurisdiction")
    for field in ("admission", "reviewed_proposal"):
        validate_ref(entry[field], f"{label} {field}")
    # All admitted values now have explicit types: no bool/int equality, floats,
    # unknown fields or embedded serialized JSON can enter the identity.
    result = {key: entry[key] for key in IDENTITY_FIELDS}
    if hashed and entry["identity_sha256"] != identity_sha256(result):
        raise PacketError(f"{label}: canonical identity SHA-256 mismatch")
    return result


def identity_sha256(entry):
    value = immutable_entry(entry, hashed=False)
    canonical = json.dumps({"edition": "2026", **value}, ensure_ascii=False,
                           sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()


def registered_entries(registrations):
    expected = {}
    for registration in registrations:
        if type(registration) is not AdmissionRegistration or not registration.entries:
            raise PacketError("invalid checker admission registration")
        for row in registration.entries:
            value = immutable_entry(row, hashed=False, label="registered guarantee")
            identifier = value["id"]
            if identifier in expected:
                raise PacketError("duplicate checker admission registration")
            expected[identifier] = value
    return expected


def validate_entries(entries, registrations, *, hashed, require_all=True, label="guarantee ledger"):
    expected = registered_entries(registrations)
    if type(entries) is not list:
        raise PacketError(f"{label}: discharged guarantees must be a list")
    actual = {}
    for entry in entries:
        value = immutable_entry(entry, hashed=hashed, label=f"{label} discharged guarantee")
        identifier = value["id"]
        if identifier in actual or identifier not in expected:
            raise PacketError(f"{label}: unknown or duplicate admitted guarantee")
        if value != expected[identifier]:
            raise PacketError(f"{label}: admitted guarantee identity changed: {identifier}")
        actual[identifier] = value
    if require_all and actual.keys() != expected.keys():
        raise PacketError(f"{label}: all registered admitted scoped guarantees must be retained")
    return actual


def initial_verifier(root, *, verify_lean):
    # A fixed Python import and a fixed API; no record-selected module or argv.
    from check_initial_guarantees import check
    return check(root, verify_lean=verify_lean)


def validate_bindings(bindings, entries, profiles, *, label="guarantee ledger"):
    if type(bindings) is not list or not bindings:
        raise PacketError(f"{label}: require current evidence bindings")
    by_name = {}
    for profile in profiles:
        if type(profile) is not VerifierProfile or profile.name in by_name:
            raise PacketError("invalid or duplicate checker verifier profile")
        by_name[profile.name] = profile
    covered = set()
    selected = []
    seen_profiles = set()
    for binding in bindings:
        exact_keys(binding, {"guarantee_ids", "verifier_profile", "evidence"}, f"{label} current binding")
        name = binding["verifier_profile"]
        if type(name) is not str or name not in by_name or name in seen_profiles:
            raise PacketError(f"{label}: unknown or duplicate fixed verifier profile")
        profile = by_name[name]
        supported = dict(profile.identities)
        if len(supported) != len(profile.identities) or not supported:
            raise PacketError("invalid checker verifier identity coverage")
        ids = binding["guarantee_ids"]
        if (type(ids) is not list or any(type(item) is not str for item in ids)
                or sorted(ids) != sorted(supported) or len(set(ids)) != len(ids)):
            raise PacketError(f"{label}: verifier coverage differs from its registered scope")
        if any(identifier not in entries or identifier in covered for identifier in ids):
            raise PacketError(f"{label}: unadmitted or multiply bound guarantee")
        if any(identity_sha256(entries[identifier]) != supported[identifier] for identifier in ids):
            raise PacketError(f"{label}: verifier does not cover the admitted immutable identity")
        validate_ref(binding["evidence"], f"{label} current evidence")
        if binding["evidence"]["path"] != profile.evidence_path:
            raise PacketError(f"{label}: evidence path differs from fixed verifier profile")
        covered.update(ids)
        seen_profiles.add(name)
        selected.append((profile, binding["evidence"]))
    if covered != entries.keys():
        raise PacketError(f"{label}: every admitted guarantee needs current evidence")
    return selected


def preserve_entries(before, after, *, before_hashed):
    """Compare every historical entry, not just the currently familiar IDs."""
    current = {row["id"]: immutable_entry(row, hashed=True) for row in after}
    for row in before:
        prior = immutable_entry(row, hashed=before_hashed, label="trusted-base ledger entry")
        if current.get(prior["id"]) != prior:
            raise PacketError(f"trusted base: admitted guarantee removed or changed: {prior['id']}")


def validate_frozen_snapshots(snapshots, manifest_path, manifest_sha256):
    """Authenticate the captured bytes themselves, not a subsequent reread.

    A timed writer must not substitute invalid initial/final bytes while making
    only the intermediate checked_file reads see genuine historical content.
    """
    data = snapshots[manifest_path]
    if hashlib.sha256(data).hexdigest() != manifest_sha256:
        raise PacketError("frozen identity manifest: SHA-256 mismatch")
    manifest = json_object(data, "frozen identity manifest")
    exact_keys(manifest, {"format", "version", "files"}, "frozen identity manifest")
    if (manifest["format"] != "qleisli.ledger-frozen-identities"
            or type(manifest["version"]) is not int or manifest["version"] != 1):
        raise PacketError("invalid frozen identity manifest")
    if type(manifest["files"]) is not dict or manifest["files"].keys() != snapshots.keys() - {manifest_path}:
        raise PacketError("frozen identity manifest must cover every protected snapshot")
    for name, expected in manifest["files"].items():
        if hashlib.sha256(snapshots[name]).hexdigest() != expected:
            raise PacketError(f"frozen artifact snapshot: SHA-256 mismatch: {name}")


def dispatch(root, ledger_path, ledger_bytes, entries, selected, *, verify_lean, protected_snapshots):
    """Verify one captured live snapshot with the fixed registered profiles.

    Both ledger and evidence snapshots must survive the whole dispatch. Each
    profile also verifies its source/artifact snapshot; this outer guard closes
    concurrent ledger rebinding across multiple profile invocations.
    """
    snapshots = dict(protected_snapshots)
    for entry in entries.values():
        for field in ("admission", "reviewed_proposal"):
            ref = entry[field]
            data = checked_file(root, ref["path"], ref["sha256"])
            if ref["path"] in snapshots and snapshots[ref["path"]] != data:
                raise PacketError("conflicting registered admission/proposal snapshots")
            snapshots[ref["path"]] = data
    for _, ref in selected:
        data = checked_file(root, ref["path"], ref["sha256"])
        if ref["path"] in snapshots and snapshots[ref["path"]] != data:
            raise PacketError("conflicting frozen artifact/evidence snapshots")
        snapshots[ref["path"]] = data

    def unchanged():
        if read_file(root, ledger_path) != ledger_bytes:
            raise PacketError("guarantee ledger changed during evidence verification")
        for name, data in snapshots.items():
            if read_file(root, name) != data:
                raise PacketError(f"guarantee ledger evidence changed during verification: {name}")

    unchanged()
    def verify_bound(profile, ref, *, replay):
        result = profile.verify(root, verify_lean=replay)
        unchanged()
        # Start/end equality is insufficient if a writer supplies different
        # bytes only to the profile's intermediate reads. Require the digest of
        # the captured input actually validated by the fixed verifier itself.
        if type(result) is not dict or result.get("current_evidence_sha256") != ref["sha256"]:
            raise PacketError(f"fixed verifier validated different evidence than the ledger binding: {profile.name}")
        return result

    results = [verify_bound(profile, ref, replay=verify_lean) for profile, ref in selected]
    # A later profile must not leave an earlier profile bound to a changed
    # source tree. After all commands, repeat the fixed source-only validators.
    if verify_lean:
        for profile, ref in selected:
            verify_bound(profile, ref, replay=False)
    unchanged()
    return results
