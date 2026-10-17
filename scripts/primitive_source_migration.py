"""Prepare explicit, reviewable source translations for the primitive cutover.

This is an offline authoring helper, never a parser or acceptance fallback.
Callers must retain the original text and review every reported ambiguity.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
from dataclasses import dataclass


BARE = {name: name for name in (
    "h", "phase", "unit", "finish", "split", "join", "measure_z", "discard",
    "take_bit", "put_bit", "empty_bits", "prepend_bit")}
BARE["phase_eighth"] = "global_phase_eighth"
GATES = {"id", "t", "s", "sdg", "tdg", "z", "x", "cnot", "toffoli",
         "swap", "controlled_phase"}
OLD = {}
for module, names in (
        ("quantum", {"h", "phase", "phase_eighth", "unit", "finish", "split", "join"} | (GATES - {"swap"}) | {"init0"}),
        ("observe", {"measure_z", "reset", "discard"}),
        ("registers", {"take_bit", "put_bit", "empty", "consume_empty"}),
        ("classical", {"empty_bits", "prepend_bit"})):
    for name in names:
        OLD[("std", module, name)] = (
            None if name in BARE else
            ("std", "gate", name) if name in GATES else
            ("std", "state", name) if name in {"init0", "reset"} else
            ("std", "structure", name))


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int
    kind: str


def tokens(source):
    """Retain exact offsets and comment/string bytes, including nested comments."""
    result = []
    at = 0
    while at < len(source):
        start = at
        if source[at].isspace():
            at += 1
            continue
        if source.startswith("//", at):
            end = source.find("\n", at)
            at = len(source) if end < 0 else end
            kind = "comment"
        elif source.startswith("/*", at):
            at += 2
            level = 1
            while at < len(source) and level:
                if source.startswith("/*", at):
                    level += 1
                    at += 2
                elif source.startswith("*/", at):
                    level -= 1
                    at += 2
                else:
                    at += 1
            if level:
                raise ValueError("unterminated block comment")
            kind = "comment"
        elif source[at] == '"':
            at += 1
            while at < len(source):
                if source[at] == "\\":
                    at += 2
                elif source[at] == '"':
                    at += 1
                    break
                else:
                    at += 1
            else:
                raise ValueError("unterminated quoted text")
            kind = "quoted"
        elif source[at].isalpha() or source[at] == "_":
            at += 1
            while at < len(source) and (source[at].isalnum() or source[at] == "_"):
                at += 1
            kind = "identifier"
        else:
            at += 2 if source.startswith("::", at) else 1
            kind = "punctuation"
        result.append(Token(source[start:at], start, at, kind))
    return result


def _import_paths(items):
    at = 0

    def tree(prefix):
        nonlocal at
        if at < len(items) and items[at].text == "{":
            at += 1
            paths = []
            while at < len(items) and items[at].text != "}":
                paths.extend(tree(prefix))
                if at < len(items) and items[at].text == ",":
                    at += 1
                elif at >= len(items) or items[at].text != "}":
                    raise ValueError("malformed import group")
            if not paths or at >= len(items):
                raise ValueError("empty or unclosed import group")
            at += 1
            return paths
        path = list(prefix)
        while at < len(items) and items[at].kind == "identifier":
            path.append(items[at].text)
            at += 1
            if at >= len(items) or items[at].text != "::":
                return [tuple(path)]
            at += 1
            if at < len(items) and items[at].text == "{":
                return tree(tuple(path))
        raise ValueError("unsupported import syntax, alias, or glob")

    paths = tree(())
    if at != len(items) or any(len(path) < 2 for path in paths):
        raise ValueError("unsupported import syntax, alias, or glob")
    return paths


def _possibly_bound(name, items):
    """Conservatively refuse a rename when the old name may be locally bound."""
    closure_parameters = False
    for index, token in enumerate(items):
        if token.text == "|":
            closure_parameters = not closure_parameters
            continue
        if token.text != name:
            continue
        if closure_parameters:
            return True
        previous = items[index - 1].text if index else ""
        following = items[index + 1].text if index + 1 < len(items) else ""
        if previous in {"fn", "meaning", "type", "const", "as", "let", "qfor", "for"} or following == ":":
            return True
        # A tuple-pattern binder may appear after fn/qfor/as or before let assignment.
        cursor = index - 1
        while cursor >= 0 and items[cursor].text not in {";", "{", "}", "="}:
            if items[cursor].text in {"let", "fn", "qfor", "for", "as"}:
                return True
            cursor -= 1
    return False


def migrate_qli(source):
    """Return source/edits/issues; any ambiguity returns original source unchanged.

    id remains generic ordinary source. Its uninstantiated references are
    reported for a separately reviewed explicit type argument or local provider.
    Comments and quoted text never undergo spelling replacement. Byte identity
    is recorded by the caller; offsets here are Python Unicode text offsets.
    """
    try:
        all_tokens = tokens(source)
        code = [token for token in all_tokens if token.kind != "comment"]
    except ValueError as error:
        return {"source": source, "edits": [], "issues": [str(error)]}
    edits, issues, imported = [], [], set()
    import_names = []
    all_import_paths = []
    import_ranges = []
    depth = 0
    at = 0
    while at < len(code):
        token = code[at]
        if depth == 0 and token.text == "use" and (at == 0 or code[at - 1].text != "fn"):
            end = at + 1
            while end < len(code) and code[end].text != ";":
                end += 1
            if end == len(code):
                issues.append("unterminated import statement")
                break
            import_ranges.append((token.start, code[end].end))
            try:
                paths = _import_paths(code[at + 1:end])
            except ValueError as error:
                issues.append(str(error))
                at = end + 1
                continue
            imported.update(path[-1] for path in paths if path in OLD)
            import_names.extend(path[-1] for path in paths)
            all_import_paths.extend(paths)
            if any(path[:2] in {("std", "quantum"), ("std", "observe"),
                               ("std", "registers"), ("std", "classical")}
                   and path not in OLD for path in paths):
                issues.append("unknown retired import: explicit negative/manual review required")
            if any(path in OLD for path in paths):
                comments = [t.text for t in all_tokens if t.kind == "comment"
                            and token.start <= t.start < code[end].end]
                replacements = [OLD.get(path, path) for path in paths]
                text = "\n".join(comments + ["use " + "::".join(path) + ";"
                                             for path in replacements if path is not None])
                if comments:
                    text += "\n"
                edits.append((token.start, code[end].end, text, "import"))
            at = end + 1
            continue
        depth += (token.text == "{") - (token.text == "}")
        at += 1
    runtime = [t for t in code if not any(start <= t.start < end for start, end in import_ranges)]
    for name in imported:
        if import_names.count(name) > 1 or any(
                token.text == name and index > 0 and runtime[index - 1].text in {"fn", "meaning"}
                for index, token in enumerate(runtime)):
            issues.append(f"import {name} conflicts with another declaration/import; preserve negative or review explicitly")
    if "phase_eighth" in imported:
        if (_possibly_bound("phase_eighth", runtime) or
                _possibly_bound("global_phase_eighth", runtime) or
                "global_phase_eighth" in import_names):
            issues.append("phase_eighth has possible local binding; review its resolved uses")
        else:
            edits.extend((t.start, t.end, "global_phase_eighth", "primitive spelling")
                         for t in runtime if t.text == "phase_eighth")
    # Qualified expression paths are not resolved by this offline translator.
    for index, token in enumerate(runtime):
        if token.text == "std" and index + 2 < len(runtime) and runtime[index + 1].text == "::":
            if runtime[index + 2].text in {"quantum", "observe", "registers", "classical"}:
                issues.append("qualified retired expression path: explicit source review required")
    ordinary_id_imported = "id" in imported or ("std", "gate", "id") in all_import_paths
    if ordinary_id_imported:
        if _possibly_bound("id", runtime):
            issues.append("id has possible local binding; review its resolved uses")
        else:
            for index, token in enumerate(runtime):
                if token.text == "id" and (index + 1 == len(runtime) or runtime[index + 1].text != "["):
                    issues.append(f"id at text offset {token.start} needs an explicit Basis instantiation or closed provider")
    if issues:
        return {"source": source, "edits": [], "issues": list(dict.fromkeys(issues))}
    transformed = source
    for start, end, replacement, _ in sorted(edits, reverse=True):
        transformed = transformed[:start] + replacement + transformed[end:]
    return {"source": transformed, "edits": edits, "issues": []}
