"""Select explicitly migrated source fixtures without rewriting historical inputs.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

ROOT = Path(__file__).resolve().parents[1]
MAP = ROOT / "tests/fixtures/frontend_v030/ordinary-type-client-integration/source-map.json"
# Relative to ROOT at selection time, including isolated unit-test roots.
NAMESPACE_MAP = "tests/fixtures/frontend_v030/stdlib-semantic-namespaces/namespace-source-map.json"


def _read_map(path):
    def unique_fields(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate source migration JSON field: {key}")
            result[key] = value
        return result
    data = json.loads(path.read_text(), object_pairs_hook=unique_fields)
    if not isinstance(data, dict) or not isinstance(data.get("projects"), list):
        raise ValueError("invalid source migration projects")
    return data


def _local(base, relative):
    if not isinstance(relative, str) or not relative:
        raise ValueError("invalid source migration path")
    path = PurePosixPath(relative)
    if (path.is_absolute() or path.as_posix() != relative or
            any(part in (".", "..") for part in path.parts) or relative == "."):
        raise ValueError(f"escaping or noncanonical source migration path: {relative}")
    result = base / relative
    if not result.resolve().is_relative_to(base.resolve()):
        raise ValueError(f"escaping source migration path: {relative}")
    return result


def _projects(data, before_field, label):
    projects = {}
    destinations = set()
    for entry in data["projects"]:
        if not isinstance(entry, dict) or set(entry) != {before_field, "current_path", "files"}:
            raise ValueError(f"invalid {label} source migration")
        before = entry[before_field]
        current = entry["current_path"]
        before_directory = _local(ROOT, before)
        current_directory = _local(ROOT, current)
        if before in projects or current in destinations:
            raise ValueError(f"missing or duplicate {label} source migration: {before}")
        projects[before] = entry
        destinations.add(current)
        hash_field = "historical_sha256" if before_field == "historical_path" else "before_sha256"
        before_files, _ = _recorded_files(entry, hash_field)
        for directory in (before_directory, current_directory):
            for relative in before_files:
                _local(directory, relative)
    return projects


def _recorded_files(entry, before_field):
    files = entry["files"]
    if not isinstance(files, list) or not files:
        raise ValueError("missing source fixture inventory")
    before, current = {}, {}
    for file in files:
        if not isinstance(file, dict) or set(file) != {"path", before_field, "current_sha256"}:
            raise ValueError("invalid source fixture inventory")
        path = file["path"]
        _local(ROOT, path)
        if path in before:
            raise ValueError(f"duplicate source fixture file: {path}")
        if not (PurePosixPath(path).suffix == ".qli" or PurePosixPath(path).name == "Qargo.toml"):
            raise ValueError(f"non-source fixture file: {path}")
        for field in (before_field, "current_sha256"):
            if not isinstance(file[field], str) or not re.fullmatch(r"[0-9a-f]{64}", file[field]):
                raise ValueError(f"invalid source fixture hash: {path}")
        before[path] = file[before_field]
        current[path] = file["current_sha256"]
    return before, current


def _inventory(directory):
    result = {}
    for path in directory.rglob("*"):
        if path.is_file() and (path.suffix == ".qli" or path.name == "Qargo.toml"):
            relative = path.relative_to(directory).as_posix()
            _local(directory, relative)
            result[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def _verify_pair(before, current, entry, before_field):
    before_files, current_files = _recorded_files(entry, before_field)
    for directory, expected in ((before, before_files), (current, current_files)):
        for relative in expected:
            _local(directory, relative)
        if _inventory(directory) != expected:
            raise ValueError(f"source fixture identity changed: {directory}")


def current_source_fixture(historical):
    """Check each explicit migration link and return its final project path."""
    historical = Path(historical)
    key = historical.relative_to(ROOT).as_posix()
    _local(ROOT, key)
    entry = _projects(_read_map(MAP), "historical_path", "explicit").get(key)
    if entry is None:
        raise ValueError(f"missing or duplicate explicit source migration: {key}")
    current = _local(ROOT, entry["current_path"])
    _verify_pair(historical, current, entry, "historical_sha256")
    namespace_map = _local(ROOT, NAMESPACE_MAP)
    if not namespace_map.is_file():
        raise ValueError(f"missing semantic namespace source map: {namespace_map}")
    namespaces = _read_map(namespace_map)
    if (namespaces.get("format") != "qleisli.semantic-namespace-source-map" or
            type(namespaces.get("version")) is not int or namespaces["version"] != 1):
        raise ValueError("invalid semantic namespace source map")
    next_entry = _projects(namespaces, "before_path", "namespace").get(entry["current_path"])
    if next_entry is not None:
        selected = _local(ROOT, next_entry["current_path"])
        _verify_pair(current, selected, next_entry, "before_sha256")
        return selected
    return current


def source_hashes(project):
    """Record the actual project inputs selected for execution."""
    return {p.relative_to(project).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(project.rglob("*"))
            if p.is_file() and (p.suffix == ".qli" or p.name == "Qargo.toml")}
