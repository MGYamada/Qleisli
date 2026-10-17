"""Check authoring-record integrity without executing recorded commands.

Hashes detect accidental edits to snapshots; they are not semantic evidence,
authenticated provenance or a claim of a controlled model benchmark.
"""

from pathlib import Path
import hashlib
import json
import re
import stat
import sys

ROOT = Path(__file__).resolve().parent.parent / "tests/fixtures/authoring_sessions"
REPOSITORY = Path(__file__).resolve().parent.parent


def local_file(root: Path, name: str) -> Path:
    if not isinstance(name, str) or not name or Path(name).is_absolute() or ".." in Path(name).parts:
        raise ValueError("expected a local relative path")
    path = root / name
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"missing or nonlocal file: {name}")
    return path


RETAINED_INDEX = "retained-source-records-v1.json"
RETAINED_DIRECTORY = "retained-source-records-v1"


def unique_retained_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate retained-source index key")
        result[key] = value
    return result


def retained_source_record_index(raw, read_bytes, stored_paths):
    """Validate an exact inert-copy inventory; never select an arbitrary root.

    The callback reads only canonical names beneath the fixed authoring root.
    This pure reader is also used by immutable fixture-reference inspection.
    Git metadata records recovery provenance; no Git or command is executed.
    """
    data = json.loads(raw, object_pairs_hook=unique_retained_object)
    if not isinstance(data, dict) or set(data) != {"format", "entries"} or type(data["format"]) is not int or data["format"] != 1:
        raise ValueError("unknown retained-source index format")
    if not isinstance(data["entries"], list) or not data["entries"]:
        raise ValueError("retained-source index needs entries")
    fields = {"kind", "session", "session_sha256", "id", "path", "sha256", "git_commit", "git_blob"}
    result, targets = {}, set()
    for entry in data["entries"]:
        if not isinstance(entry, dict) or set(entry) != fields or entry["kind"] != "source_record":
            raise ValueError("retained source must bind the source_record class")
        session, logical, identity = entry["session"], entry["path"], entry["id"]
        if not all(isinstance(value, str) for value in (session, logical, identity)):
            raise ValueError("retained source names must be strings")
        for name in (session, logical):
            if not name or "\\" in name or Path(name).is_absolute() or ".." in Path(name).parts or Path(name).as_posix() != name:
                raise ValueError("retained source needs a canonical local relative path")
        if len(Path(session).parts) != 2 or Path(session).name != "session.json" or not logical.endswith(".qli") or not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", identity):
            raise ValueError("retained source has an invalid session, ID or source class")
        for key, length in (("session_sha256", 64), ("sha256", 64), ("git_commit", 40), ("git_blob", 40)):
            if not isinstance(entry[key], str) or not re.fullmatch(r"[0-9a-f]{" + str(length) + "}", entry[key]):
                raise ValueError("retained source needs exact hashes and recovery commit")
        original = read_bytes(session)
        if hashlib.sha256(original).hexdigest() != entry["session_sha256"]:
            raise ValueError("retained source original session hash mismatch")
        session_data = json.loads(original)
        if not isinstance(session_data, dict) or session_data.get("format") != 1 or session_data.get("kind") not in ("informed_first_attempt", "curated_repair_replay"):
            raise ValueError("retained source needs an original authoring session")
        records = [record for record in session_data.get("source_records", []) if record.get("id") == identity]
        if len(records) != 1 or records[0].get("sha256", {}).get(logical) != entry["sha256"]:
            raise ValueError("retained source differs from the original record path/hash")
        key = (session, identity, logical)
        if key in result:
            raise ValueError("duplicate retained source record")
        target = (Path(RETAINED_DIRECTORY) / Path(session).parent / identity / logical).as_posix() + ".txt"
        source = read_bytes(target)
        if hashlib.sha256(source).hexdigest() != entry["sha256"]:
            raise ValueError("retained source hash mismatch")
        blob = hashlib.sha1(b"blob " + str(len(source)).encode("ascii") + b"\0" + source).hexdigest()
        if blob != entry["git_blob"]:
            raise ValueError("retained source recovery blob mismatch")
        result[key] = target
        targets.add(target)
    if set(stored_paths) != targets:
        raise ValueError("retained source copy inventory differs from the reviewed index")
    return result


def retained_source_records(repository):
    root = repository / "tests/fixtures/authoring_sessions"
    index, archive = root / RETAINED_INDEX, root / RETAINED_DIRECTORY
    if not root.resolve().is_relative_to(repository.resolve()):
        raise ValueError("retained source root is not local")
    if not index.exists():
        if archive.exists():
            raise ValueError("unregistered retained-source copy directory")
        return {}
    stored = set()
    if archive.exists():
        for path in (archive, *archive.rglob("*")):
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode):
                raise ValueError("retained sources forbid symbolic links")
            if stat.S_ISREG(mode):
                stored.add(path.relative_to(root).as_posix())
            elif not stat.S_ISDIR(mode):
                raise ValueError("retained sources forbid nonregular archive entries")

    def read_bytes(name):
        path = local_file(root, name)
        current = path
        while current != root.parent:
            if current.is_symlink():
                raise ValueError("retained sources forbid symbolic links")
            current = current.parent
        return path.read_bytes()

    return retained_source_record_index(read_bytes(RETAINED_INDEX), read_bytes, stored)


def check_reports(root: Path, record: dict) -> None:
    """Linked diagnostics/reports are not timestamped command observations."""
    for name in record.get("reports", []):
        if not isinstance(json.loads(local_file(root, name).read_text(encoding="utf-8")), dict):
            raise ValueError("linked report must be a JSON object")


def check_session(manifest: Path, *, repository: Path = REPOSITORY) -> tuple[int, int]:
    root = manifest.parent
    data = json.loads(manifest.read_text(encoding="utf-8"))
    retained = retained_source_records(repository)
    authoring_root = repository / "tests/fixtures/authoring_sessions"
    try:
        session_name = manifest.resolve().relative_to(authoring_root.resolve()).as_posix()
    except ValueError:
        session_name = None
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
        check_reports(root, attempt)
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
    source_ids = set()
    for record in data.get("source_records", []):
        if not record["id"] or record["id"] in source_ids or not record["reason"].strip():
            raise ValueError("source records need unique IDs and reasons")
        source_ids.add(record["id"])
        if not record["sha256"]:
            raise ValueError("source record has no source hashes")
        for name, digest in record["sha256"].items():
            key = (session_name, record["id"], name)
            if key in retained:
                source = local_file(authoring_root, retained[key])
            else:
                source = local_file(repository, name)
            actual = hashlib.sha256(source.read_bytes()).hexdigest()
            if digest != actual:
                raise ValueError(f"source record hash mismatch: {record['id']}/{name}")
        check_reports(root, record)
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
