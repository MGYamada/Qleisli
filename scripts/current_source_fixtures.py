"""Select explicitly migrated source fixtures without rewriting historical inputs.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAP = ROOT / "tests/fixtures/frontend_v030/ordinary-type-client-integration/source-map.json"


def current_source_fixture(historical):
    """Check both recorded source identities and return the current project path."""
    historical = Path(historical)
    key = historical.relative_to(ROOT).as_posix()
    matches = [entry for entry in json.loads(MAP.read_text())["projects"]
               if entry["historical_path"] == key]
    if len(matches) != 1:
        raise ValueError(f"missing or duplicate explicit source migration: {key}")
    entry = matches[0]
    current = ROOT / entry["current_path"]
    for directory, field in ((historical, "historical_sha256"), (current, "current_sha256")):
        expected = {file["path"]: file[field] for file in entry["files"]}
        actual = {p.relative_to(directory).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in directory.rglob("*")
                  if p.is_file() and (p.suffix == ".qli" or p.name == "Qargo.toml")}
        if actual != expected:
            raise ValueError(f"source fixture identity changed: {directory}")
    return current


def source_hashes(project):
    """Record the actual project inputs selected for execution."""
    return {p.relative_to(project).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(project.rglob("*"))
            if p.is_file() and (p.suffix == ".qli" or p.name == "Qargo.toml")}
