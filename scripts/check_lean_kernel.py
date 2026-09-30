#!/usr/bin/env python3
"""Check the no-Mathlib executable package's source/import/build policy.

This review guard is complemented by lean-kernel/Audit.lean's compiled audit;
it is not a sandbox for malicious Lean metaprograms or a compiler proof.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import argparse
import json
from pathlib import Path
import re
import sys
import tomllib

from check_docs import lean_imports


ROOT = Path(__file__).resolve().parent.parent
TOOLCHAIN = "leanprover/lean4:v4.30.0"
FORBIDDEN = {
    "unsafe", "partial", "axiom", "sorry", "admit", "native_decide",
    "noncomputable", "implemented_by", "extern", "csimp", "run_cmd",
    "elab", "elab_rules", "macro", "macro_rules", "initialize",
    "builtin_initialize",
}
TOKEN = re.compile(r"[^\W\d][\w'.]*", re.UNICODE)


def lean_code(text: str) -> str:
    """Mask comments and plain/raw literals, preserving line coordinates.

    Interpolated strings retain their tokens: Lean expressions inside them
    must not hide a forbidden construct. This intentionally conservative
    scanner is a source-policy check, not a second Lean parser.
    """
    result = list(text)

    def mask(start, end):
        for index in range(start, end):
            if result[index] != "\n":
                result[index] = " "

    index = 0
    while index < len(text):
        start = index
        if text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif text.startswith("/-", index):
            index += 2
            depth = 1
            while index < len(text) and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ValueError("unterminated block comment")
        elif raw := re.match(r'r(#+)?"', text[index:]):
            terminator = '"' + (raw[1] or "")
            end = text.find(terminator, index + len(raw[0]))
            if end < 0:
                raise ValueError("unterminated raw string")
            index = end + len(terminator)
        elif text[index] == '"' and index > 0 and text[index - 1] == "!":
            # Keep the whole interpolated body visible to token policy. This
            # can conservatively reject forbidden words in its literal text.
            index += 1
            while index < len(text) and text[index] != '"':
                index += 2 if text[index] == "\\" else 1
            if index >= len(text):
                raise ValueError("unterminated interpolated string")
            index += 1
            continue
        elif text[index] == '"':
            index += 1
            while index < len(text) and text[index] != '"':
                index += 2 if text[index] == "\\" else 1
            if index >= len(text):
                raise ValueError("unterminated string")
            index += 1
        elif text[index] == "'" and (
                match := re.match(r"'(?:\\.|[^'\\])'", text[index:], re.DOTALL)):
            index += len(match[0])
        else:
            index += 1
            continue
        mask(start, index)
    return "".join(result)


def source_errors(text: str) -> list[str]:
    try:
        code = lean_code(text)
    except ValueError as error:
        return [str(error)]
    errors = []
    # The identifier lexer omits '#'; command evaluation must be checked on the
    # masked source itself. Both forms can perform IO during elaboration.
    for match in re.finditer(r"#\s*eval\b!?", code):
        line = code.count("\n", 0, match.start()) + 1
        errors.append(f"line {line}: forbidden executable-source command {match[0]}")
    for match in TOKEN.finditer(code):
        token = match[0]
        if token in FORBIDDEN or token.startswith("debug."):
            line = code.count("\n", 0, match.start()) + 1
            errors.append(f"line {line}: forbidden executable-source token {token}")
    # Native evaluation can also be requested without the native_decide alias.
    if re.search(r"\bdecide\s*\+\s*native\b", code):
        errors.append("native proof evaluation is forbidden")
    return errors


def check_kernel(root: Path) -> tuple[list[str], int]:
    package = root / "lean-kernel"
    errors = []
    sources = {}
    for path in sorted(package.rglob("*.lean")):
        relative = path.relative_to(package)
        if ".lake" in relative.parts or relative.as_posix() == "Audit.lean":
            continue
        name = ".".join(relative.with_suffix("").parts)
        if name == "Tests":
            for error in source_errors(path.read_text(encoding="utf-8")):
                errors.append(f"{path.relative_to(root)}: {error}")
            continue  # Separate reduction tests, never an executable import.
        if not (name in {"QleisliKernel", "Main", "Protocol"}
                or name.startswith("QleisliKernel.")):
            errors.append(f"unaudited kernel source module: {name}")
        sources[name] = path
        for error in source_errors(path.read_text(encoding="utf-8")):
            errors.append(f"{path.relative_to(root)}: {error}")

    visited = set()

    def visit(name, transport, stack):
        if name in stack:
            errors.append(f"cyclic kernel import: {name}")
            return
        key = (name, transport)
        if key in visited:
            return
        visited.add(key)
        if name not in sources:
            if name == "Init" or name.startswith("Init."):
                return
            if name == "Std" or name.startswith("Std."):
                return
            if transport and (name == "Lean" or name.startswith("Lean.")):
                return
            errors.append(f"missing or forbidden kernel import: {name}")
            return
        if not transport and name in {"Main", "Protocol"}:
            errors.append(f"pure kernel imports transport module: {name}")
            return
        for dependency in lean_imports(sources[name].read_text(encoding="utf-8")):
            if name.startswith("QleisliKernel.Semantics.") and not (
                    dependency == "Init" or dependency.startswith("Init.") or
                    dependency == "Std" or dependency.startswith("Std.") or
                    dependency.startswith("QleisliKernel.Semantics.")):
                errors.append(f"reference semantics imports checker/transport: {name} -> {dependency}")
            visit(dependency, transport, stack | {name})

    for name in ["QleisliKernel", "Main"]:
        if name not in sources:
            errors.append(f"missing kernel root: {name}")
        else:
            visit(name, name == "Main", set())
    reachable = {name for name, _ in visited}
    for name in sorted(sources.keys() - reachable):
        errors.append(f"kernel module absent from root import/audit: {name}")
    audit = package / "Audit.lean"
    if not audit.is_file():
        errors.append("missing compiled kernel audit")
    elif not {"QleisliKernel", "Main"} <= set(lean_imports(audit.read_text(encoding="utf-8"))):
        errors.append("compiled audit must import both QleisliKernel and Main")
    try:
        manifest = tomllib.loads((package / "lakefile.toml").read_text(encoding="utf-8"))
        if manifest.get("require"):
            errors.append("executable kernel must have no external Lake requirements")
        if (package / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
            errors.append("executable kernel must use Lean 4.30.0")
        lock = json.loads((package / "lake-manifest.json").read_text(encoding="utf-8"))
        if lock.get("packages") != []:
            errors.append("executable kernel manifest must contain zero external packages")
    except (OSError, ValueError) as error:
        errors.append(f"kernel package metadata: {error}")
    # The separate complex reference models may use Mathlib, but must obey
    # the same direction of dependence: acceptance imports specification.
    for path in sorted((root / "lean/Qleisli/Semantics").rglob("*.lean")):
        for dependency in lean_imports(path.read_text(encoding="utf-8")):
            if not (dependency in {"Init", "Std", "Mathlib"} or
                    dependency.startswith(("Init.", "Std.", "Mathlib.",
                        "Qleisli.Semantics.", "QleisliKernel.Semantics."))):
                errors.append(f"complex reference semantics imports checker/transport: "
                              f"{path.relative_to(root)} -> {dependency}")
    return errors, len(sources)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    errors, count = check_kernel(args.root)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Checked {count} executable kernel/transport source modules; no external Lake dependencies.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
