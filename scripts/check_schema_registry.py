#!/usr/bin/env python3
"""Bind the closed schema registry to rebuilt Lean theorem types and sources.

The manifest is a repository artifact, never an input supplied by an IR producer.
--write deliberately refreshes it after all builds and audits; --source-only
checks packaging/source identity, not theorem validity or compiled correspondence.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "lean/schema-registry.json"
DECLARATIONS = {
    "qft-dyadic8/1": "Qleisli.Schema.qft_sound",
    "controlled-power/1": "Qleisli.Schema.power_coherent_sound",
    "qpe-instrument/1": "Qleisli.Schema.qpe_sound",
}
CHECKER = "QleisliKernel.Schema.check"
PARAMETERS = {
    "qft-dyadic8/1": [("width", 1, 8)],
    "controlled-power/1": [("exponent", 0, 12), ("provider", 0, 2**32 - 1)],
    "qpe-instrument/1": [("target_width", 1, 8), ("precision", 1, 8),
                         ("provider", 0, 2**32 - 1)],
}


class RegistryError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise RegistryError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False, allow_nan=False).encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, f"duplicate JSON field: {key}")
            result[key] = value
        return result
    def invalid(value):
        raise RegistryError(f"invalid JSON constant: {value}")
    require(len(data) <= 8 * 1024 * 1024, "registry/export exceeds 8 MiB")
    return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid)


def source_revision(root):
    paths = [*root.glob("lean/Qleisli/**/*.lean"),
             *root.glob("lean-kernel/QleisliKernel/**/*.lean")]
    paths += [root / name for name in (
        "lean/Qleisli.lean", "lean/Audit.lean", "lean/SchemaExport.lean",
        "lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json",
        "lean-kernel/QleisliKernel.lean", "lean-kernel/Audit.lean", "lean-kernel/Tests.lean",
        "lean-kernel/Main.lean", "lean-kernel/Protocol.lean", "lean-kernel/lean-toolchain",
        "lean-kernel/lakefile.toml", "lean-kernel/lake-manifest.json",
        "scripts/check_lean_kernel.py", "scripts/check_schema_registry.py")]
    files = {}
    for path in sorted(paths):
        require(path.is_file() and not path.is_symlink(), f"missing/linked registry source: {path}")
        files[path.relative_to(root).as_posix()] = digest(path.read_bytes())
    require(any(p.startswith("lean/Qleisli/") for p in files), "no proof sources")
    require(any(p.startswith("lean-kernel/QleisliKernel/") for p in files), "no kernel sources")
    return {"algorithm": "sha256-sorted-path-and-content-map-v1",
            "sha256": digest(canonical(files)), "files": files}


def constants(tree):
    if not isinstance(tree, list):
        return set()
    result = {tree[1]} if len(tree) >= 2 and tree[0] == "constant" else set()
    for child in tree:
        if isinstance(child, list):
            result.update(constants(child))
    return result


def expected_manifest(export, revision):
    require(isinstance(export, dict) and set(export) == {"format", "version", "checker", "entries"},
            "invalid type-export fields")
    require(export["format"] == "qleisli.schema-type-export" and type(export["version"]) is int
            and export["version"] == 1, "unsupported type export")
    fields = {"declaration", "module", "universe_parameters", "type", "readable_type"}
    checker = export["checker"]
    require(isinstance(checker, dict) and set(checker) == fields
            and checker["declaration"] == CHECKER and checker["module"] == "QleisliKernel.Schema",
            "wrong executable checker declaration")
    require(isinstance(export["entries"], list) and
            [entry.get("id") for entry in export["entries"]] == list(DECLARATIONS),
            "unknown, missing, reordered or duplicate registry IDs")
    entries = []
    for item in export["entries"]:
        require(set(item) == {"id", "theorem"}, "invalid theorem entry fields")
        rule, theorem = item["id"], item["theorem"]
        require(isinstance(theorem, dict) and set(theorem) == fields and
                theorem["declaration"] == DECLARATIONS[rule] and theorem["module"] == "Qleisli.Schema",
                f"wrong theorem declaration: {rule}")
        require(CHECKER in constants(theorem["type"]), f"theorem omits actual checker: {rule}")
        entries.append({
            "id": rule, "version": 1, "template_version": 1,
            "parameters": [{"name": name, "kind": "natural", "min": low, "max": high}
                           for name, low, high in PARAMETERS[rule]],
            "constraints": ["target_width + precision <= 16"] if rule == "qpe-instrument/1" else [],
            "external_enabled": False,
            "status": "proved-component; external IR projection and provider binding pending",
            "theorem": theorem,
        })
    return {"format": "qleisli.schema-registry", "version": 1,
            "profile": "qpe-dyadic8-v1", "lean_toolchain": "leanprover/lean4:v4.30.0",
            "source_revision": revision, "checker": checker, "entries": entries}


def manifest_export(manifest):
    return {"format": "qleisli.schema-type-export", "version": 1,
            "checker": manifest["checker"],
            "entries": [{"id": item["id"], "theorem": item["theorem"]}
                        for item in manifest["entries"]]}


def verify_manifest(manifest, export, revision):
    require(canonical(manifest) == canonical(expected_manifest(export, revision)),
            "schema manifest differs from current types, domains, enablement or source revision; "
            "review the change, then use --write to rebuild and audit")


def run(argv, cwd, records):
    started = time.monotonic()
    result = subprocess.run(argv, cwd=cwd, capture_output=True, check=False)
    records.append({"argv": argv, "cwd": cwd.name, "exit_code": result.returncode,
                    "seconds": round(time.monotonic() - started, 3),
                    "stdout_sha256": digest(result.stdout), "stderr_sha256": digest(result.stderr),
                    "diagnostics": (result.stdout + result.stderr).decode(errors="replace")[:4000]})
    require(result.returncode == 0, f"command failed: {argv}\n" +
            (result.stdout + result.stderr).decode(errors="replace")[:4000])
    return result.stdout


def check(root, write=False, source_only=False, report=None):
    require(not (write and source_only), "--write requires rebuilt types and audits")
    record = report if report is not None else {}
    record.update(format="qleisli.schema-registry-validation", version=1,
                  mode="source-identity-only" if source_only else "rebuilt-types-and-audits",
                  status="error", commands=[])
    revision = source_revision(root)
    manifest_path = root / MANIFEST
    if source_only:
        manifest = read_json(manifest_path.read_bytes())
        verify_manifest(manifest, manifest_export(manifest), revision)
    else:
        commands = record["commands"]
        run([sys.executable, "scripts/check_lean_kernel.py"], root, commands)
        for package in ("lean-kernel", "lean"):
            run(["lake", "build"], root / package, commands)
            run(["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"], root / package, commands)
        run(["lake", "env", "leanchecker", "--fresh", "QleisliKernel"], root / "lean-kernel", commands)
        export = read_json(run(["lake", "env", "lean", "-DwarningAsError=true", "SchemaExport.lean"],
                               root / "lean", commands))
        require(revision == source_revision(root), "source changed during registry validation")
        manifest = expected_manifest(export, revision)
        if write:
            manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
        else:
            verify_manifest(read_json(manifest_path.read_bytes()), export, revision)
    record.update(status="passed", source_revision=revision["sha256"],
                  manifest_sha256=digest(manifest_path.read_bytes()), entries=len(DECLARATIONS),
                  externally_enabled=0)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {}
    try:
        check(args.root.resolve(), args.write, args.source_only, report)
    except (RegistryError, OSError, ValueError, KeyError, TypeError, RecursionError) as error:
        report.update(status="error", error=str(error))
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "commands"}, sort_keys=True))
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
