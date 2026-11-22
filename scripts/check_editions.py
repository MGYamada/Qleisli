#!/usr/bin/env python3
"""Check filesystem editions and exact retained historical experiment inputs.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""

import hashlib
import json
import os
from pathlib import Path
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SKIP = {".git", ".lake", "target", "__pycache__", ".venv"}
MANIFEST_NAMES = ("Qlirgo.toml", "Qargo.toml")
HISTORY = "scripts/edition_history.json"
HISTORY_SHA256 = "e81d1fbb1b148ffb0ebeeaf3f87a33d5ce7a430b9a2bab1e0eb569e120f7f542"
HISTORICAL_ROOT = "tests/fixtures/constitution_v030/routed-control-commutation"
REJECTED_AUTHORING_ROOT = "tests/fixtures/authoring_sessions/operation-application-v030"
REJECTED_CONST_ROOT = "tests/fixtures/authoring_sessions/const-parameters-v030"
REJECTED_ARROW_ROOT = "tests/fixtures/authoring_sessions/general-arrows-v030"
REJECTED_ADJOINT_ROOT = "tests/fixtures/authoring_sessions/direct-arrow-adjoint-v030"
REJECTED_EXIT_ROOT = "tests/fixtures/authoring_sessions/structured-exit-v030"


def historical_inputs(root):
    """An exact historical exception, never filesystem source admission.

    Fixed metadata identifies the original record, generator and every input.
    A new file, missing file or changed byte does not inherit the exception.
    Small independent checker fixtures need no record when this history is absent.
    """
    def frozen(name, expected):
        path = root
        for part in Path(name).parts:
            path /= part
            if path.is_symlink():
                raise ValueError(f"{name}: historical input must not follow symlinks")
        if not path.is_file():
            raise ValueError(f"{name}: missing historical input")
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError(f"{name}: historical input identity changed")
        return data

    if not (root / HISTORY).exists():
        if any((root / name).exists() for name in
               (HISTORICAL_ROOT, REJECTED_AUTHORING_ROOT, REJECTED_CONST_ROOT,
                REJECTED_EXIT_ROOT, REJECTED_ARROW_ROOT, REJECTED_ADJOINT_ROOT)):
            raise ValueError(f"missing {HISTORY} for preserved historical inputs")
        return set(), set()
    records = json.loads(frozen(HISTORY, HISTORY_SHA256))["records"]
    manifests, sources = set(), set()
    for record in records:
        base = Path(record["root"])
        for name, sha in {**record["anchors"], **record["files"]}.items():
            frozen(str(base / name), sha)
        actual = {
            str(path.relative_to(root / base))
            for project in record["projects"]
            for path in (root / base / project).rglob("*")
            if path.name in MANIFEST_NAMES or path.suffix in {".qli", ".qlt"}
        }
        if actual != record["files"].keys():
            raise ValueError(f"{base}: historical source inventory changed")
        for name in record["files"]:
            path = root / base / name
            (manifests if path.name in MANIFEST_NAMES else sources).add(path)
    return manifests, sources


def checkout_paths(root):
    for directory, children, files in os.walk(root):
        current = Path(directory)
        if current != root and (".git" in files or ".git" in children):
            # Git worktrees use a gitfile rather than a .git directory.
            children.clear()
            continue
        children[:] = [name for name in children if name not in SKIP]
        for name in (*children, *files):
            path = current / name
            if name in MANIFEST_NAMES or path.suffix in {".qli", ".qlt"}:
                yield path


def check_editions(root: Path):
    errors, manifests, sources = [], {}, []
    historical_manifests, historical_sources = set(), set()
    try:
        historical_manifests, historical_sources = historical_inputs(root)
    except (OSError, UnicodeError, ValueError) as failure:
        errors.append(str(failure))
    for name in MANIFEST_NAMES:
        path = root / name
        if path.exists() or path.is_symlink():
            errors.append(f"{name} belongs in source trees, not the repository root")
    for required in ("corpus/Qargo.toml", "stdlib/Qlirgo.toml"):
        if not (root / required).is_file():
            errors.append(f"missing {required}")
    for path in sorted(checkout_paths(root)):
        relative = path.relative_to(root)
        if path.name in MANIFEST_NAMES:
            if path in historical_manifests:
                # Deliberately invalid for filesystem admission; only the exact
                # recorded sources below receive historical classification.
                manifests[path] = False
                continue
            try:
                if path.is_symlink() or not path.is_file():
                    raise ValueError("manifest must be a regular file, not a symlink")
                raw = path.read_bytes()
                if len(raw) > 65_536:
                    raise ValueError("manifest exceeds 65536 bytes")
                data = tomllib.loads(raw.decode("utf-8"))
                if type(data.get("schema-version")) is not int or data["schema-version"] != 2:
                    raise ValueError("requires schema-version = 2")
                qrate = data.get("qrate")
                if not isinstance(qrate, dict) or type(qrate.get("edition")) is not str:
                    raise ValueError('requires explicit string [qrate].edition = "2026"')
                if qrate["edition"] != "2026":
                    raise ValueError(f'unsupported edition {qrate["edition"]!r}; expected "2026"')
                manifests[path] = raw
            except (OSError, UnicodeError, ValueError) as failure:
                manifests[path] = False
                errors.append(f"{relative}: {failure}")
        elif path.suffix in {".qli", ".qlt"} and path.is_file():
            sources.append(path)
    for canonical, raw in list(manifests.items()):
        if canonical.name != MANIFEST_NAMES[0] or not raw:
            continue
        legacy = canonical.with_name(MANIFEST_NAMES[1])
        if legacy in manifests and manifests[legacy] != raw:
            manifests[canonical] = False
            errors.append(f"{canonical.relative_to(root)}: Qlirgo.toml and Qargo.toml must have identical bytes")
    for source in sources:
        if source in historical_sources:
            continue
        manifest = None
        for parent in source.parents:
            manifest = next((parent / name for name in MANIFEST_NAMES
                             if parent / name in manifests), None)
            if manifest is not None:
                break
            if parent == root:
                break
        if manifest is None:
            errors.append(f"{source.relative_to(root)}: missing enclosing Qlirgo.toml")
        elif not manifests[manifest]:
            errors.append(f"{source.relative_to(root)}: invalid enclosing {manifest.relative_to(root)}")
    std_manifest = root / "stdlib/Qlirgo.toml"
    if manifests.get(std_manifest):
        try:
            data = tomllib.loads(std_manifest.read_text())
            version = tomllib.loads((root / "Cargo.toml").read_text())["package"]["version"]
            if data["qrate"].get("name") != "std" or data["qrate"].get("version") != version:
                raise ValueError("std qrate name/version must match std and the Cargo product version")
            if set(data) != {"schema-version", "qrate", "source", "tests", "docs"}:
                raise ValueError("std requires the complete schema-2 qargo manifest")
            if set(data["qrate"]) != {"name", "version", "edition"}:
                raise ValueError("std requires name, version and edition")
            for key, directory in (("source", "src"), ("tests", "tests"), ("docs", "docs")):
                if data[key] != {"root": directory} or not (root / "stdlib" / directory).is_dir():
                    raise ValueError(f"std requires existing [{key}] root = {directory!r}")
        except (OSError, KeyError, ValueError) as failure:
            errors.append(f"stdlib/Qlirgo.toml: {failure}")
    current = set(sources) - historical_sources
    return errors, {"manifests": len(manifests) - len(historical_manifests),
                    "qli": sum(p.suffix == ".qli" for p in current),
                    "qlt": sum(p.suffix == ".qlt" for p in current),
                    "historical_manifests": len(historical_manifests),
                    "historical_sources": len(historical_sources)}


def main():
    errors, counts = check_editions(ROOT)
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    print(f'Edition 2026: {counts["qli"]} .qli and {counts["qlt"]} .qlt files covered by '
          f'{counts["manifests"]} explicit manifests; no repository-root manifest.')
    if counts["historical_sources"]:
        print(f'Historical inputs: {counts["historical_sources"]} exact source files and '
              f'{counts["historical_manifests"]} non-admitting manifests retained by hash; '
              'not valid filesystem source projects.')
    return 0


if __name__ == "__main__":
    sys.exit(main())
