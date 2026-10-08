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
COHERENT_MAP = "tests/fixtures/frontend_v030/coherent-basis/source-map.json"
CHECKED_MAP = "tests/fixtures/frontend_v030/checked-operation/source-map.json"
CLASSICAL_MAP = "tests/fixtures/frontend_v030/classical-functions/source-map.json"
CLIENT_CONST_MAP = "tests/fixtures/frontend_v030/const-client-headers/source-map.json"
APPLICATION_MAP = "tests/fixtures/frontend_v030/operation-application/source-map.json"
APPLICATION_MAP = "tests/fixtures/frontend_v030/operation-application/source-map.json"
CONST_MAP = "tests/fixtures/frontend_v030/const-parameters/source-map.json"
QFOR_MAP = "tests/fixtures/frontend_v030/qfor/source-map.json"


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


def _file_entries(data, label):
    if not isinstance(data.get("files"), list):
        raise ValueError(f"invalid {label} source file migrations")
    entries, destinations = {}, set()
    for entry in data["files"]:
        if not isinstance(entry, dict) or set(entry) != {
                "before_path", "current_path", "before_sha256", "current_sha256"}:
            raise ValueError(f"invalid {label} source file migration")
        for field in ("before_path", "current_path"):
            relative = entry[field]
            _local(ROOT, relative)
            if PurePosixPath(relative).suffix != ".qli":
                raise ValueError(f"non-source fixture file: {relative}")
        before, current = entry["before_path"], entry["current_path"]
        if before in entries or current in destinations:
            raise ValueError(f"duplicate {label} source file migration: {before}")
        for field in ("before_sha256", "current_sha256"):
            if not isinstance(entry[field], str) or not re.fullmatch(r"[0-9a-f]{64}", entry[field]):
                raise ValueError(f"invalid source fixture hash: {before}")
        entries[before] = entry
        destinations.add(current)
    return entries


def _migration_maps():
    maps = []
    for relative, format_name, label in (
            (NAMESPACE_MAP, "qleisli.semantic-namespace-source-map", "semantic namespace"),
            (COHERENT_MAP, "qleisli.coherent-basis-source-map", "coherent basis"),
            (CHECKED_MAP, "qleisli.checked-operation-source-map", "checked operation"),
            (CLASSICAL_MAP, "qleisli.classical-function-source-map", "classical function"),
            (QFOR_MAP, "qleisli.qfor-source-map", "quantum fold"),
            (CONST_MAP, "qleisli.const-parameter-source-map", "const parameter"),
            (APPLICATION_MAP, "qleisli.operation-application-source-map", "operation application"),
            (CLIENT_CONST_MAP, "qleisli.const-client-source-map", "const client")):
        path = _local(ROOT, relative)
        if not path.is_file():
            raise ValueError(f"missing {label} source map: {path}")
        data = _read_map(path)
        if (data.get("format") != format_name or
                type(data.get("version")) is not int or data["version"] != 1):
            raise ValueError(f"invalid {label} source map")
        files = _file_entries(data, label)
        # Validate even unselected project metadata; a file selector cannot
        # turn a malformed or escaping recorded project into a fallback.
        projects = _projects(data, "before_path", "namespace" if label == "semantic namespace"
                             else label)
        maps.append((files, projects))
    return maps


def current_source_file(historical):
    """Check each explicit file migration and return its final .qli path."""
    historical = Path(historical)
    if not historical.is_absolute():
        historical = ROOT / historical
    key = historical.relative_to(ROOT).as_posix()
    current = _local(ROOT, key)
    if PurePosixPath(key).suffix != ".qli":
        raise ValueError(f"non-source fixture file: {key}")
    for files, _ in _migration_maps():
        entry = files.get(current.relative_to(ROOT).as_posix())
        if entry is None:
            continue
        selected = _local(ROOT, entry["current_path"])
        for path, field in ((current, "before_sha256"), (selected, "current_sha256")):
            if (not path.is_file() or
                    hashlib.sha256(path.read_bytes()).hexdigest() != entry[field]):
                raise ValueError(f"source fixture identity changed: {path}")
        current = selected
    return current


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
    for _, projects in _migration_maps():
        next_entry = projects.get(current.relative_to(ROOT).as_posix())
        if next_entry is not None:
            selected = _local(ROOT, next_entry["current_path"])
            _verify_pair(current, selected, next_entry, "before_sha256")
            current = selected
    return current


def source_hashes(project):
    """Record the actual project inputs selected for execution."""
    return {p.relative_to(project).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(project.rglob("*"))
            if p.is_file() and (p.suffix == ".qli" or p.name == "Qargo.toml")}
