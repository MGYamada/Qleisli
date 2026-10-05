#!/usr/bin/env python3
"""Seventy-two literal first-source checks; records and predictions select no commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import sys

sys.dont_write_bytecode = True
DESIGN = Path(__file__).resolve().parent
ROOT = DESIGN.parent
REPO = ROOT.parents[3]
OUT = ROOT / "before"
LIMIT = 1 << 20
CLI = Path("/private/tmp/qleisli-bounded-validation-target/debug/qleisli")
CLI_SHA = "d219e3cb0e546c8173ab1215ffd94cacc7c032ce9abd145b98949bbb2c4d089e"
NATIVE = REPO / "lean-kernel/.lake/build/bin/qleisli-kernel"
NATIVE_SHA = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
WRAPPER = REPO / "tests/fixtures/authoring_sessions/common-parameter-declaration-v030/native-log.py"
WRAPPER_SHA = "3b249471941bf1ec91c0d7506c7ba38b39d7c365efdc23b45ba4e195a486f3fd"
HELPER = REPO / "tests/fixtures/frontend_v030/qft-exact-request-design/native-capture-design-01/bounded_process.py"
HELPER_SHA = "0ce0b915687f1df32c2d9775353fb1c01aa2a5ad45642b2c2379bfcfa84be4be"
FIRST_SHA = "753edf0e0fe01b6b3a2f597250b237cd8a0574e07ac0f67da3d483e77d1ea2db"
SESSION_SHA = "520b60a5f2289ca7049944bd25265313d8d65f915187cfa7afe344306fe43400"
REGISTRY_SHA = "511d68af1834ca8c2063b3b0a1c6307ad499a5e978c0361c79df6311bd6c93d1"
MSRV = REPO / "tests/fixtures/frontend_v030/common-frontend-next-unit-01/formal-access-candidate-01/validation/msrv-attempt-01"
CASES = ("mixed-qif-and-generic", "private-zero-fold-owner", "dead-arm-missing-adjoint",
         "private-basis-valid", "private-basis-bad-result", "qif-formal-controlled",
         "qif-formal-apply-only", "qif-wrong-effect", "qif-wrong-shape",
         "computed-unary-predicate", "computed-wrong-arity", "owner-shadow-move-valid",
         "owner-shadow-live-invalid", "static-shadows-global-valid",
         "runtime-shadows-static-policy", "runtime-shadows-static-call-invalid",
         "natural-runtime-shadow-invalid", "bundled-import-control")
FORMS = (("finite", "text"), ("finite", "json"),
         ("selected-auto", "text"), ("selected-auto", "json"))
EMBEDDED = ("stdlib/Qargo.toml", "stdlib/src/arithmetic.qli", "stdlib/src/basis.qli",
            "stdlib/src/routines.qli", "stdlib/src/transforms.qli",
            "docs/src/reference/discovery.md")


def timestamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(LIMIT), b""):
            result.update(block)
    return result.hexdigest()


def read_bounded(path):
    with path.open("rb") as stream:
        value = stream.read(LIMIT + 1)
    if len(value) > LIMIT:
        raise ValueError("record exceeds 1 MiB: " + str(path))
    return value


def record(path):
    return dict(bytes=path.stat().st_size, sha256=sha(path), mode=path.stat().st_mode & 0o777)


def save(path, value):
    data = (json.dumps(value, indent=2) + "\n").encode()
    if len(data) > LIMIT:
        raise ValueError("JSON record exceeds 1 MiB")
    with path.open("xb") as stream:
        stream.write(data)


def repository_path(name):
    path = (REPO / name).resolve()
    path.relative_to(REPO)
    return path


def checkout_head():
    # This checkout uses a .git directory. HEAD is an identity marker only.
    git = REPO / ".git"
    head = read_bounded(git / "HEAD").decode().strip()
    if re.fullmatch(r"[0-9a-f]{40}", head):
        return head
    if not head.startswith("ref: refs/"):
        raise ValueError("unsupported checkout HEAD representation")
    ref = head[5:]
    path = (git / ref).resolve()
    path.relative_to(git.resolve())
    if path.exists():
        value = read_bounded(path).decode().strip()
    else:
        value = next((line.split()[0] for line in read_bounded(git / "packed-refs").decode().splitlines()
                      if not line.startswith(("#", "^")) and line.split()[1:] == [ref]), "")
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise ValueError("checkout ref is not an exact commit identity")
    return value


def identity():
    old = json.loads(read_bounded(MSRV / "inputs-before.json"))["files"]
    if len(old) != 715 or old != json.loads(read_bounded(MSRV / "inputs-after.json"))["files"]:
        raise ValueError("terminal MSRV declared 715-row map differs")
    terminal = json.loads(read_bounded(MSRV / "results.json"))
    if (terminal["status"] != "passed" or terminal["remaining_stages_not_run"] != 0
            or terminal["cli_sha256_after"] != CLI_SHA or not terminal["cli_rebuild_completed"]):
        raise ValueError("terminal MSRV consumed-CLI association differs")
    paths = list((REPO / "src").rglob("*.rs"))
    paths += [REPO / name for name in EMBEDDED + ("Cargo.toml", "Cargo.lock")]
    paths += [p for name in ("build.rs", "rust-toolchain", "rust-toolchain.toml") if (p := REPO / name).is_file()]
    if (REPO / ".cargo").exists():
        paths += [p for p in (REPO / ".cargo").rglob("*") if p.is_file()]
    rust = {str(p.relative_to(REPO)): record(p) for p in sorted(set(paths))}
    # All production Rust/embedded bytes also occur in the independently
    # recorded build inputs, except discovery.md (explicitly guarded above).
    for name, row in rust.items():
        if name in old and row["sha256"] != old[name]:
            raise ValueError("production build input changed since consumed MSRV CLI: " + name)
    return dict(checkout_head=checkout_head(), cli_path=str(CLI), cli_sha256=sha(CLI),
        native_path=str(NATIVE), native_sha256=sha(NATIVE), rust_build_files=rust,
        msrv_current_inputs={name: record(repository_path(name)) for name in sorted(old)},
        msrv_records={p.name: record(p) for p in sorted(MSRV.iterdir()) if p.is_file()})


def command(case, profile, presentation):
    project = ROOT / "attempt-01" / case
    argv = [str(CLI), "check", str(project)] if profile == "finite" else [
        str(CLI), "check", "--entry=main::main", "--module=main=" + str(project / "main.qli"), "--ir-profile=auto"]
    argv.append("--lean-kernel=" + str(WRAPPER))
    if presentation == "json":
        argv.append("--format=json")
    return argv


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs-sha256", required=True)
    args = parser.parse_args()
    if sys.version_info < (3, 11):
        raise ValueError("development Python 3.11+ required")
    if not re.fullmatch(r"[0-9a-f]{64}", args.inputs_sha256):
        parser.error("inputs SHA must be 64 lowercase hexadecimal digits")
    input_path = DESIGN / "inputs.json"  # Root freezes only after its formal commit/barrier.
    if sha(input_path) != args.inputs_sha256:
        raise ValueError("explicit reviewed prospective map changed")
    inputs = json.loads(read_bounded(input_path))
    if sha(ROOT / "first-files.json") != FIRST_SHA:
        raise ValueError("immutable source-only FIRST map changed")
    first = json.loads(read_bounded(ROOT / "first-files.json"))["files"]
    if len(first) != 41:
        raise ValueError("complete FIRST file count differs")

    def unchanged():
        if sha(input_path) != args.inputs_sha256 or sha(ROOT / "first-files.json") != FIRST_SHA:
            raise ValueError("reviewed maps changed")
        for row in first + inputs["frozen_files"]:
            path = repository_path(row["path"])
            if record(path) != {key: row[key] for key in ("bytes", "sha256", "mode")}:
                raise ValueError("FIRST/capture source/record changed: " + row["path"])
        if {p.name for p in (ROOT / "attempt-01").iterdir()} != set(CASES):
            raise ValueError("complete FIRST case inventory changed")
        for case in CASES:
            if {p.name for p in (ROOT / "attempt-01" / case).iterdir()} != {"main.qli", "Qargo.toml"}:
                raise ValueError("complete FIRST project inventory changed")
        if identity() != inputs["identity"]:
            raise ValueError("checkout/source/build-record/CLI/native inputs changed")
        registry = json.loads(read_bounded(ROOT / "registry-inputs.json"))
        for row in registry["registry"] + [registry["manifest"]]:
            path = repository_path(row["repository_path"])
            if path.stat().st_size != row["bytes"] or sha(path) != row["sha256"]:
                raise ValueError("actual bundled source/manifest changed")
        if sha(WRAPPER) != WRAPPER_SHA or sha(HELPER) != HELPER_SHA:
            raise ValueError("reviewed capture helper/forwarder changed")

    unchanged()
    if sha(ROOT / "session.before.json") != SESSION_SHA or sha(ROOT / "registry-inputs.json") != REGISTRY_SHA:
        raise ValueError("FIRST session/registry record changed")
    if inputs["identity"]["cli_sha256"] != CLI_SHA or inputs["identity"]["native_sha256"] != NATIVE_SHA:
        raise ValueError("fixed current MSRV CLI/native identity differs")
    order = [(case, profile, presentation) for case in CASES for profile, presentation in FORMS]
    if [command(*item) for item in order] != inputs["commands"]:
        raise ValueError("literal seventy-two command mapping differs")
    if not os.access(CLI, os.X_OK) or not os.access(WRAPPER, os.X_OK):
        raise ValueError("fixed CLI/forwarder not executable")
    session = json.loads(read_bounded(ROOT / "session.before.json"))
    if (ROOT / "session.json").exists() or session["attempts"][0]["observations"]:
        raise ValueError("FIRST must remain unobserved before capture")
    spec = importlib.util.spec_from_file_location("original_ast_reviewed_bounded_capture", HELPER)
    if spec is None or spec.loader is None:
        raise ValueError("cannot load guarded streaming helper")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)  # Only reviewed authored helper, never recorded argv/code.
    soft, hard = resource.getrlimit(resource.RLIMIT_FSIZE)
    ceiling = min([LIMIT] + [n for n in (soft, hard) if n != resource.RLIM_INFINITY])
    resource.setrlimit(resource.RLIMIT_FSIZE, (ceiling, ceiling))
    OUT.mkdir()  # One shot; original inputs and partial capture are never overwritten.
    (OUT / "executed-driver.py.txt").open("xb").write(Path(__file__).read_bytes())
    save(OUT / "started.json", dict(recorded_utc=timestamp(), inputs_sha256=args.inputs_sha256,
        status="first-capture-started-no-outcomes-predicted", outer_seconds=55,
        regular_file_byte_ceiling=ceiling, python=sys.executable, python_version=sys.version))
    save(OUT / "identity.before.json", dict(identity=inputs["identity"], first_files_sha256=FIRST_SHA,
        inputs_sha256=args.inputs_sha256, scope="Declared incomplete input closure; HEAD is an identity marker, not a compiled-source attestation."))
    rows = []
    try:
        for case, profile, presentation in order:
            unchanged()
            label = case + "-" + profile + "-check-" + presentation
            argv = command(case, profile, presentation)
            journal = OUT / (label + ".native.jsonl")
            journal.touch(exist_ok=False)
            env = dict(os.environ, QLEISLI_PARAMETER_NATIVE_LOG=str(journal), PYTHONDONTWRITEBYTECODE="1")
            env.pop("QLEISLI_KERNEL", None)
            env.pop("QLEISLI_HIERARCHY_KERNEL", None)
            save(OUT / (label + ".command-before.json"), dict(recorded_utc=timestamp(), argv=argv, cwd=str(REPO)))
            result = helper.capture(argv, REPO, env, b"", seconds=55, output_limit=LIMIT)
            stdout, stderr = result.pop("stdout"), result.pop("stderr")
            stdout_path, stderr_path = OUT / (label + ".stdout.bin"), OUT / (label + ".stderr.bin")
            for path, data in ((stdout_path, stdout), (stderr_path, stderr)):
                with path.open("xb") as stream:
                    stream.write(data)
            attempts = [json.loads(line) for line in read_bounded(journal).splitlines()]
            event = dict(command=argv, cwd=str(REPO), exit_code=result["returncode"], recorded_utc=timestamp(),
                client_capture=result, native_forwarded_attempts=len(attempts), native_argv_log=journal.name,
                native_count_scope="Forwarder JSONL rows immediately before execv; no independent native-start/exit attestation.",
                stdout_raw=stdout_path.name, stderr_raw=stderr_path.name, stdout_sha256=sha(stdout_path),
                stderr_sha256=sha(stderr_path), native_journal_sha256=sha(journal), outcomes_predicted=False)
            transcript = (stdout + stderr).decode(errors="replace")
            event.update(transcript=transcript[:65536], transcript_limited_prefix=len(transcript) > 65536,
                transcript_scope="At most 65536 decoded characters; exact bounded captured raw prefixes retained separately.")
            if presentation == "json":
                try:
                    decoded = json.loads(stdout)
                    if isinstance(decoded, dict) and decoded.get("format") == "qleisli.result":
                        event["stdout"] = decoded
                except (ValueError, UnicodeError) as error:
                    event["json_parse_error"] = str(error)
            save(OUT / (label + ".json"), event)
            rows.append(dict(case=case, profile=profile, presentation=presentation,
                observation="before/" + label + ".json", exit_code=event["exit_code"], native_forwarded_attempts=len(attempts)))
            unchanged()
            print(label, event["exit_code"], len(attempts), flush=True)
            if not result["spawned"] or result["reason"] is not None:
                save(OUT / "incomplete.json", dict(rows=rows, session_published=False,
                    reason="Actual operational failure retained; no retry or invented child exit.",
                    process_scope="Outer group cleanup does not attest all separate native descendant groups."))
                return 1
        save(OUT / "summary.json", dict(rows=rows, actual_observation_count=len(rows),
            actual_successes=sum(row["exit_code"] == 0 for row in rows),
            actual_nonzero_exits=sum(row["exit_code"] != 0 for row in rows),
            native_forwarded_attempts=sum(row["native_forwarded_attempts"] for row in rows),
            source_repairs=0, predictions_used_as_assertions=False, source_meaning_verified=False,
            scope="Completed first check captures only; no source preservation, generic/stdlib completion or native-start attestation."))
        unchanged()
        save(OUT / "identity.final.json", dict(identity=identity(), first_inputs_unchanged=True))
        save(OUT / "files.json", dict(files={p.name: record(p) for p in sorted(OUT.iterdir()) if p.is_file()}, self_excluded="files.json"))
        session["attempts"][0]["observations"] = [row["observation"] for row in rows]
        session["status"] = "actual-first-observations-retained"
        unchanged()
        save(ROOT / "session.json", session)
        return 0
    except BaseException as error:
        save(OUT / "aborted.json", dict(recorded_utc=timestamp(), completed_observations=len(rows),
            error_type=type(error).__name__, message=str(error), note="Partial output retained; no repair/retry."))
        raise


if __name__ == "__main__":
    sys.exit(main())
