"""Check authoring-record integrity without executing recorded commands.

Hashes detect accidental edits to snapshots; they are not semantic evidence,
authenticated provenance or a claim of a controlled model benchmark.
"""

from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent.parent / "tests/fixtures/authoring_sessions"


def local_file(root: Path, name: str) -> Path:
    if not isinstance(name, str) or not name or Path(name).is_absolute() or ".." in Path(name).parts:
        raise ValueError("expected a local relative path")
    path = root / name
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"missing or nonlocal file: {name}")
    return path


def check_session(manifest: Path) -> tuple[int, int]:
    root = manifest.parent
    data = json.loads(manifest.read_text(encoding="utf-8"))
    if data["format"] != 1 or data["kind"] not in ("informed_first_attempt", "curated_repair_replay"):
        raise ValueError("unknown record format/kind")
    for key in ("task", "author", "project_version"):
        if not isinstance(data[key], str) or not data[key].strip():
            raise ValueError(f"missing {key}")
    if not re.fullmatch(r"[0-9a-f]{40}", data["baseline_commit"]):
        raise ValueError("baseline must be an exact Git commit")
    if not local_file(root, data["context"]).read_text(encoding="utf-8").strip():
        raise ValueError("empty context")
    attempts = data["attempts"]
    if not isinstance(attempts, list) or not attempts:
        raise ValueError("missing first attempt")
    observed = set()
    for index, attempt in enumerate(attempts, 1):
        if attempt["id"] != f"attempt-{index:02d}" or not attempt["reason"].strip():
            raise ValueError("attempt IDs must be consecutive with reasons")
        directory = root / attempt["id"]
        sources = {str(path.relative_to(directory)) for path in directory.rglob("*.qli")}
        if not sources or sources != set(attempt["sha256"]):
            raise ValueError("snapshot source inventory differs from manifest")
        for name, digest in attempt["sha256"].items():
            actual = hashlib.sha256(local_file(directory, name).read_bytes()).hexdigest()
            if digest != actual:
                raise ValueError(f"snapshot hash mismatch: {attempt['id']}/{name}")
        if not attempt["observations"]:
            raise ValueError("attempt has no recorded observation")
        for name in attempt["observations"]:
            if name in observed:
                raise ValueError("observation assigned more than once")
            observed.add(name)
            event = json.loads(local_file(root, name).read_text(encoding="utf-8"))
            command = event["command"]
            if not isinstance(command, list) or not command or not all(isinstance(x, str) for x in command):
                raise ValueError("record command as an argument list")
            if type(event["exit_code"]) is not int or not event["recorded_utc"]:
                raise ValueError("missing observation exit/time")
            if "stdout" in event:
                result = event["stdout"]
                expected = "ok" if event["exit_code"] == 0 else "error"
                if result["format"] != "qleisli.result" or result["version"] != 1 or result["outcome"] != expected:
                    raise ValueError("recorded JSON outcome contradicts exit status")
            elif not isinstance(event.get("transcript"), str) or not event["transcript"]:
                raise ValueError("missing observation output")
    actual_attempts = {path.name for path in root.glob("attempt-*") if path.is_dir()}
    if actual_attempts != {attempt["id"] for attempt in attempts}:
        raise ValueError("unregistered attempt directory")
    return len(attempts), len(observed)


def main() -> int:
    manifests = sorted(ROOT.glob("*/session.json"))
    if not manifests:
        print("No authoring sessions found", file=sys.stderr)
        return 1
    attempts = observations = 0
    for manifest in manifests:
        try:
            count, events = check_session(manifest)
        except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
            print(f"{manifest}: {error}", file=sys.stderr)
            return 1
        attempts += count
        observations += events
    print(f"Checked {len(manifests)} authoring records, {attempts} snapshots and {observations} observations; no recorded command executed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
