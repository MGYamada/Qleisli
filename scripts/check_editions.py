#!/usr/bin/env python3
"""Check explicit edition coverage of every repository .qli and .qlt file.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

from pathlib import Path
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SKIP = {".git", ".lake", "target", "__pycache__", ".venv"}


def check_editions(root: Path):
    errors, manifests, sources = [], {}, []
    if (root / "Qargo.toml").exists():
        errors.append("Qargo.toml belongs in source trees, not the repository root")
    for required in ("corpus/Qargo.toml", "stdlib/Qargo.toml"):
        if not (root / required).is_file():
            errors.append(f"missing {required}")
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if any(part in SKIP for part in relative.parts):
            continue
        if path.name == "Qargo.toml":
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
                manifests[path] = True
            except (OSError, UnicodeError, ValueError) as failure:
                manifests[path] = False
                errors.append(f"{relative}: {failure}")
        elif path.suffix in {".qli", ".qlt"} and path.is_file():
            sources.append(path)
    for source in sources:
        manifest = None
        for parent in source.parents:
            candidate = parent / "Qargo.toml"
            if candidate in manifests:
                manifest = candidate
                break
            if parent == root:
                break
        if manifest is None:
            errors.append(f"{source.relative_to(root)}: missing enclosing Qargo.toml")
        elif not manifests[manifest]:
            errors.append(f"{source.relative_to(root)}: invalid enclosing {manifest.relative_to(root)}")
    std_manifest = root / "stdlib/Qargo.toml"
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
            errors.append(f"stdlib/Qargo.toml: {failure}")
    return errors, {"manifests": len(manifests), "qli": sum(p.suffix == ".qli" for p in sources),
                    "qlt": sum(p.suffix == ".qlt" for p in sources)}


def main():
    errors, counts = check_editions(ROOT)
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    print(f'Edition 2026: {counts["qli"]} .qli and {counts["qlt"]} .qlt files covered by '
          f'{counts["manifests"]} explicit manifests; no repository-root manifest.')
    return 0


if __name__ == "__main__":
    sys.exit(main())
