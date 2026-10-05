#!/usr/bin/env python3
"""Forty fixed first-source checks; observations never select commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[3]
CLI = Path("/private/tmp/qleisli-bounded-validation-target/debug/qleisli")
CLI_SHA256 = "db571ad2fcdac89e52e0835a61732b72bb00df7b04ae4ecba33a34888c366a8a"
NATIVE = REPO / "lean-kernel/.lake/build/bin/qleisli-kernel"
NATIVE_SHA256 = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"
WRAPPER = REPO / "tests/fixtures/authoring_sessions/common-parameter-declaration-v030/native-log.py"
WRAPPER_SHA256 = "3b249471941bf1ec91c0d7506c7ba38b39d7c365efdc23b45ba4e195a486f3fd"
HELPER = REPO / "tests/fixtures/frontend_v030/qft-exact-request-design/native-capture-design-01/bounded_process.py"
HELPER_SHA256 = "0ce0b915687f1df32c2d9775353fb1c01aa2a5ad45642b2c2379bfcfa84be4be"
OUT = ROOT / "before"
LIMIT = 1 << 20
CASES = (
    "valid-operation", "valid-dependent-basis", "forward-natural", "forward-basis",
    "duplicate-access", "wrong-kind-access", "static-runtime-collision",
    "unused-missing-access", "natural-priority", "basis-scan-priority",
)
FORMS = (("finite", "text"), ("finite", "json"),
         ("selected-auto", "text"), ("selected-auto", "json"))
CONTRACTS = (
    "CONSTITUTION.md", "GOVERNANCE.md", "governance/README.md",
    "governance/ratification-2026.json", "governance/guarantees.json",
    "governance/interpretations/initial-2026-reviewed.txt",
    "governance/interpretations/initial-2026-adoption.json",
    "governance/proposals/exactness-2026.md",
    "governance/interpretations/exactness-2026-adoption.json",
    "governance/proposals/initial-guarantees.json",
    "governance/guarantees/initial-2026-admission.json",
    "governance/guarantees/current-evidence.json",
    "docs/src/reference/authority.md", "docs/src/reference/type-model.md",
    "docs/src/reference/source-text.md", "Cargo.toml", "Cargo.lock",
    "lean-kernel/lean-toolchain", "lean-kernel/lakefile.toml", "lean-kernel/lake-manifest.json",
)


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
        data = stream.read(LIMIT + 1)
    if len(data) > LIMIT:
        raise ValueError("record exceeds 1 MiB: " + str(path))
    return data


def save(path, value):
    data = (json.dumps(value, indent=2) + "\n").encode()
    if len(data) > LIMIT:
        raise ValueError("JSON record exceeds 1 MiB")
    with path.open("xb") as stream:
        stream.write(data)


def identity():
    files = list((REPO / "src").rglob("*.rs"))
    files += [p for p in (REPO / "lean-kernel").rglob("*.lean") if ".lake" not in p.parts]
    files += [p for p in (REPO / "stdlib").rglob("*")
              if p.is_file() and p.suffix in {".qli", ".toml"}]
    files += [REPO / name for name in CONTRACTS]
    return dict(cli_path=str(CLI), cli_sha256=sha(CLI), native_path=str(NATIVE),
                native_sha256=sha(NATIVE),
                files={str(p.relative_to(REPO)): dict(bytes=p.stat().st_size, sha256=sha(p))
                       for p in sorted(set(files))})


def command(case, profile, presentation):
    # Literal filenames and forms only; commands-before.json is never executed.
    project = ROOT / "attempt-01" / case
    if profile == "finite":
        argv = [str(CLI), "check", str(project)]
    else:
        argv = [str(CLI), "check", "--entry=main::main",
                "--module=main=" + str(project / "main.qli"), "--ir-profile=auto"]
    argv.append("--lean-kernel=" + str(WRAPPER))
    if presentation == "json":
        argv.append("--format=json")
    return argv


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--first-files-sha256", required=True)
    args = parser.parse_args()
    if sys.version_info < (3, 11):
        raise ValueError("development Python 3.11+ is required")
    if len(args.first_files_sha256) != 64 or any(c not in "0123456789abcdef" for c in args.first_files_sha256):
        parser.error("first-files SHA must be 64 lowercase hexadecimal digits")
    first_path = ROOT / "first-files.json"
    if sha(first_path) != args.first_files_sha256:
        raise ValueError("explicit reviewed FIRST map hash differs")
    frozen = json.loads(read_bounded(first_path))["files"]
    prepared = json.loads(read_bounded(ROOT / "identity-prepared.json"))["identity"]

    def unchanged():
        if sha(first_path) != args.first_files_sha256:
            raise ValueError("FIRST map changed")
        for row in frozen:
            path = (REPO / row["path"]).resolve()
            path.relative_to(REPO)
            if path.stat().st_size != row["bytes"] or sha(path) != row["sha256"] or path.stat().st_mode & 0o777 != row["mode"]:
                raise ValueError("FIRST source/record/helper changed: " + row["path"])
        if {p.name for p in (ROOT / "attempt-01").iterdir()} != set(CASES):
            raise ValueError("complete FIRST case inventory changed")
        for case in CASES:
            if {p.name for p in (ROOT / "attempt-01" / case).iterdir()} != {"main.qli", "Qargo.toml"}:
                raise ValueError("complete FIRST project inventory changed")
        if identity() != prepared:
            raise ValueError("source/CLI/native/contracts changed after preparation")
        if sha(WRAPPER) != WRAPPER_SHA256 or sha(HELPER) != HELPER_SHA256:
            raise ValueError("reviewed capture helper/forwarder changed")

    unchanged()
    if prepared["cli_sha256"] != CLI_SHA256 or prepared["native_sha256"] != NATIVE_SHA256:
        raise ValueError("fixed CLI/native hash differs")
    if not os.access(CLI, os.X_OK) or not os.access(WRAPPER, os.X_OK):
        raise ValueError("fixed CLI/forwarder is not executable")
    spec = importlib.util.spec_from_file_location("qft_reviewed_bounded_capture", HELPER)
    if spec is None or spec.loader is None:
        raise ValueError("cannot load reviewed streaming helper")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    session = json.loads(read_bounded(ROOT / "session.before.json"))
    if (ROOT / "session.json").exists() or session["attempts"][0]["observations"]:
        raise ValueError("FIRST session must remain unpublished/unobserved")
    # Bound even the reused append-only native journal. This is an operational
    # harness ceiling, not a source/type/kernel rule or quantity guarantee.
    soft, hard = resource.getrlimit(resource.RLIMIT_FSIZE)
    ceilings = [LIMIT] + [n for n in (soft, hard) if n != resource.RLIM_INFINITY]
    ceiling = min(ceilings)
    resource.setrlimit(resource.RLIMIT_FSIZE, (ceiling, ceiling))
    OUT.mkdir()  # One shot; partial observations are never overwritten/retried.
    save(OUT / "started.json", dict(recorded_utc=timestamp(), first_files_sha256=args.first_files_sha256,
        status="first-capture-started-no-outcomes-predicted", python=sys.executable,
        python_version=sys.version, regular_file_byte_ceiling=ceiling, outer_seconds=55))
    rows = []
    try:
        for case in CASES:
            for profile, presentation in FORMS:
                unchanged()
                label = case + "-" + profile + "-check-" + presentation
                journal = OUT / (label + ".native.jsonl")
                journal.touch(exist_ok=False)
                argv = command(case, profile, presentation)
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
                event = dict(command=argv, exit_code=result["returncode"], recorded_utc=timestamp(),
                    client_capture=result, native_forwarded_attempts=len(attempts), native_argv_log=journal.name,
                    native_count_scope="Actual forwarder JSONL rows immediately before execv; no independently observed native starts/exits.",
                    stdout_raw=stdout_path.name, stderr_raw=stderr_path.name,
                    stdout_sha256=sha(stdout_path), stderr_sha256=sha(stderr_path),
                    native_journal_sha256=sha(journal), outcomes_predicted=False)
                transcript = (stdout + stderr).decode(errors="replace")
                event["transcript"] = transcript[:65536]
                event["transcript_limited_prefix"] = len(transcript) > 65536
                event["transcript_scope"] = "At most 65536 decoded characters; exact captured raw byte prefixes remain in separate files."
                if presentation == "json":
                    try:
                        decoded = json.loads(stdout)
                        event["parsed_json_shape"] = "object" if isinstance(decoded, dict) else type(decoded).__name__
                        if isinstance(decoded, dict) and decoded.get("format") == "qleisli.result":
                            event["stdout"] = decoded
                    except (ValueError, UnicodeError) as error:
                        event["json_parse_error"] = str(error)
                save(OUT / (label + ".json"), event)
                rows.append(dict(case=case, profile=profile, presentation=presentation,
                    observation="before/" + label + ".json", exit_code=event["exit_code"],
                    native_forwarded_attempts=event["native_forwarded_attempts"]))
                unchanged()
                print(label, event["exit_code"], event["native_forwarded_attempts"], flush=True)
                if not result["spawned"] or result["reason"] is not None:
                    save(OUT / "incomplete.json", dict(rows=rows, session_published=False,
                        reason="Actual operational failure retained; no retry, repair or invented exit.",
                        process_scope="Outer group cleanup does not attest all separate native descendant groups."))
                    return 1
        save(OUT / "summary.json", dict(rows=rows, actual_observation_count=len(rows),
            native_forwarded_attempts=sum(row["native_forwarded_attempts"] for row in rows),
            source_repairs=0, predictions_used_as_assertions=False, source_meaning_verified=False,
            scope="Forty completed check captures; no runtime oracle, source preservation or native-start attestation."))
        session["attempts"][0]["observations"] = [row["observation"] for row in rows]
        session["status"] = "actual-first-observations-retained"
        unchanged()
        save(OUT / "identity.final.json", dict(identity=identity(), first_inputs_unchanged=True))
        unchanged()
        save(ROOT / "session.json", session)
        return 0
    except BaseException as error:
        save(OUT / "aborted.json", dict(recorded_utc=timestamp(), completed_observations=len(rows),
            error_type=type(error).__name__, message=str(error), note="Partial output retained; no repair/retry."))
        raise


if __name__ == "__main__":
    sys.exit(main())
