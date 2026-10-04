"""Compare explicit legacy/canonical observations, retaining every changed source.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()


def identical(left, right):
    a = (ROOT / left).read_bytes()
    b = (ROOT / right).read_bytes()
    assert a == b, (left, right)
    return {"before": left, "after": right, "sha256": sha(a)}


def main():
    matches = []
    for old_stage, old, new, files in [
        ("before-follow-up", "legacy-actions-keywords", "canonical-actions-keywords",
         ["finite.qirf.json", "finite.raw.txt", "finite.action.txt"]),
        ("before", "legacy-feedback", "canonical-feedback",
         ["finite.qirf.json", "finite.raw.txt", "finite.action.txt"]),
        ("before", "legacy-readout", "canonical-readout",
         ["proposal.json", "request.json", "precursor.json", "instrument.action.json"]),
        ("before-follow-up", "legacy-unit-drain-readout", "unit-drain-readout",
         ["proposal.json", "request.json", "precursor.json", "instrument.action.json"]),
        ("unit-pattern-before", "unit-pattern-consume", "unit-pattern-consume",
         ["proposal.json", "request.json", "precursor.json"]),
    ]:
        for name in files:
            matches.append(identical(f"{old_stage}/{old}/{name}", f"after/{new}/{name}"))

    old = json.loads((ROOT / "before-source-bearing/legacy-retained-source/finite.qirf.json").read_text())
    new = json.loads((ROOT / "after/canonical-retained-source/finite.qirf.json").read_text())
    old_sources = old.pop("sources")
    new_sources = new.pop("sources")
    assert old == new, "all non-source artifact fields must remain exactly equal"
    assert [s["path"] for s in old_sources] == [s["path"] for s in new_sources]
    assert old_sources != new_sources, "do not present changed source evidence as byte identity"
    before_inputs = json.loads((ROOT / "before-source.json").read_text())["files"]
    after_inputs = json.loads((ROOT / "after-source.json").read_text())["files"]
    changed = []
    for a, b in zip(old_sources, new_sources, strict=True):
        path = a["path"]
        if path == "main":
            assert a["text"] == (ROOT / "sources/legacy-retained-source/main.qli").read_text()
            assert b["text"] == (ROOT / "sources/canonical-retained-source/main.qli").read_text()
        else:
            file = f"stdlib/src/{path.removeprefix('std::')}.qli"
            assert sha(a["text"].encode()) == before_inputs[file]
            assert sha(b["text"].encode()) == after_inputs[file]
        if a != b:
            changed.append({"module": path, "before_sha256": sha(a["text"].encode()),
                            "after_sha256": sha(b["text"].encode())})
    matches.append(identical("before-source-bearing/legacy-retained-source/finite.action.txt",
                             "after/canonical-retained-source/finite.action.txt"))
    return {"status": "passed", "byte_identical_files": matches,
            "source_bearing_semantic_and_structural_fields_equal": True,
            "changed_retained_sources": changed,
            "scope": "Bounded explicit migration comparison; sources are validated against their own build snapshots, never ignored or rewritten by an acceptance path. Source-event spans may change with source spelling."}


if __name__ == "__main__":
    print(json.dumps(main(), indent=2, sort_keys=True))
