#!/usr/bin/env python3
"""Scoped 0.3.0 readiness, never release approval or publication (Issue #142).

GitHub remains the work ledger. Reviewed requirements come from a caller-trusted
Git base; receipts come from same-run producer outputs, not candidate assertions.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile
import tomllib

from check_ratification_packet import PacketError, ROOT, exact_keys, json_object, read_file
from check_distribution import clean_candidate, read_archive, tracked_files
from ci_profiles import SUITES, check_needs
from maintain_release import version_plan

REQUIREMENTS = "release/requirements.json"
ACCEPTANCE = "release/acceptance.json"
LEDGER = "governance/guarantees.json"
GROUPS = {
    "G01": [129, 134, 137, 138, 149],
    "G02": [135, 136, 139, 140, 154, 280, 281], "G03": [141, 142],
    "G04": [22, 27, 43, 44, 84, 100],
    "G05": [28, 30, 31, 39, 40, 45, 46, 47, 63, 83, 89],
    "G06": [29, 69, 70, 71, 72, 73, 74, 75, 76, 77, 79, 85, 86, 156, 157, 158, 198, 303],
    "G07": [37, 64, 81, 87, 88, 125, 194, 195, 215],
    "G08": [25, 32, 33, 34, 35, 57, 67, 68, 80, 82, 196, 250],
    "G09": [120, 121, 122, 123, 124, 126, 127, 161, 162, 163, 164, 165],
    "G10": [41, 58, 65, 131, 167],
    "G11": [169, 170, 171, 172, 173, 174, 230, 231, 255],
    "G12": [133, 224, 225, 226, 237, 245, 270, 272], "G13": [48, 234, 253, 254],
}
ISSUES = {number for numbers in GROUPS.values() for number in numbers}
ROLES = {"implementation", "reference", "migration", "positive", "negative", "jurisdictions",
         "production", "compatibility"}
NATIVE_JOBS = {"check-macos-source": "aarch64-apple-darwin",
               "check-lean-kernel": "x86_64-unknown-linux-gnu"}
IDENTITIES = {"edition": "2026", "qrate_schema": 2, "native_protocol": "qleisli.qirf-native 1"}
SHA = re.compile(r"[0-9a-f]{64}\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")


def require(condition, message):
    if not condition:
        raise PacketError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def nonempty(value, label):
    require(type(value) is str and bool(value.strip()), f"{label}: require nonempty text")


def envelope(value, kind, fields):
    exact_keys(value, {"format", "version", *fields}, kind)
    require(value["format"] == f"qleisli.{kind}" and type(value["version"]) is int
            and value["version"] == 1, f"{kind}: unknown format/version")


def git(root, *args):
    result = subprocess.run(["git", "-C", str(root), *args], capture_output=True)
    require(result.returncode == 0, "Git input unavailable: " + result.stderr.decode(errors="replace"))
    return result.stdout


class Snapshot:
    """Hold the bytes used, then reject later changes, including input records."""
    def __init__(self):
        self.files = {}

    def read(self, root, name):
        key = (Path(root), name)
        data = read_file(*key)
        require(key not in self.files or self.files[key] == data, f"input changed: {name}")
        self.files[key] = data
        return data

    def ref(self, root, value):
        exact_keys(value, {"path", "sha256"}, "file reference")
        require(type(value["sha256"]) is str and SHA.fullmatch(value["sha256"]), "invalid digest")
        data = self.read(root, value["path"])
        require(digest(data) == value["sha256"], f"stale evidence: {value['path']}")
        return data

    def unchanged(self):
        for (root, name), data in self.files.items():
            require(read_file(root, name) == data, f"input changed during checking: {name}")


def indexed(rows, label, expected=None):
    require(type(rows) is list, f"{label}: require a list")
    result = {}
    for row in rows:
        require(type(row) is dict and "id" in row, f"{label}: missing ID")
        identifier = row["id"]
        require(type(identifier) in {str, int} and identifier not in result, f"{label}: invalid/duplicate ID")
        result[identifier] = row
    if expected is not None:
        require(result.keys() == expected, f"{label}: missing or unexpected IDs")
    return result


def requirements(root, base, snapshot):
    require(type(base) is str and COMMIT.fullmatch(base), "require caller-selected exact trusted base commit")
    require(git(root, "rev-parse", base + "^{commit}").decode().strip() == base, "trusted base is not a commit")
    # Do not let the candidate select a ref or replace the reviewed criterion list.
    try:
        raw = git(root, "show", f"{base}:{REQUIREMENTS}")
    except PacketError as error:
        raise PacketError(f"missing reviewed {REQUIREMENTS} at trusted base; GitHub acceptance work is incomplete") from error
    data = json_object(raw, REQUIREMENTS)
    envelope(data, "release-requirements", {"release_line", "identities", "groups", "issues", "review"})
    require(data["release_line"] == "0.3.0" and data["identities"] == IDENTITIES,
            "reviewed release/edition/schema identities differ")
    require(type(data["identities"]["qrate_schema"]) is int, "qrate schema must be an integer")
    require(data["groups"] == GROUPS, "reviewed requirements must retain all 13 groups/108 Issues")
    require(all(type(number) is int for numbers in data["groups"].values() for number in numbers),
            "group Issue identities must be integers")
    # References in the reviewed requirements resolve against immutable Git blobs.
    def frozen_ref(ref):
        exact_keys(ref, {"path", "sha256"}, "reviewed file")
        # Use the same normalized path policy as filesystem references.
        from ci_profiles import valid_path
        require(type(ref["path"]) is str and valid_path(ref["path"]), "invalid reviewed path")
        content = git(root, "show", f"{base}:{ref['path']}")
        require(digest(content) == ref["sha256"], "reviewed snapshot digest mismatch")
        return content
    frozen_ref(data["review"])
    rows = indexed(data["issues"], "reviewed Issues", ISSUES)
    all_roles = set()
    for number, row in rows.items():
        exact_keys(row, {"id", "snapshot", "criteria"}, f"Issue {number}")
        body = frozen_ref(row["snapshot"]).decode("utf-8")
        criteria = indexed(row["criteria"], f"Issue {number} criteria")
        require(bool(criteria), f"Issue {number}: missing reviewed criteria")
        for identifier, criterion in criteria.items():
            exact_keys(criterion, {"id", "text", "scope", "roles"}, "reviewed criterion")
            nonempty(identifier, "criterion ID")
            nonempty(criterion["text"], "criterion text")
            require(criterion["text"] in body, f"Issue {number}: criterion absent from reviewed snapshot")
            require(criterion["scope"] in {"required", "explicit-later-version"}, "unknown criterion scope")
            roles = criterion["roles"]
            require(type(roles) is list and len(set(roles)) == len(roles)
                    and set(roles) <= ROLES, "unknown/duplicate evidence roles")
            require(bool(roles) if criterion["scope"] == "required" else not roles,
                    "required criteria need evidence; later scope must be explicit in trusted snapshot")
            all_roles.update(roles)
    require(all_roles == ROLES, "reviewed criteria omit a required evidence category")
    return data, raw


def acceptance(root, expected, raw_requirements, snapshot, ledger):
    data = json_object(snapshot.read(root, ACCEPTANCE), ACCEPTANCE)
    envelope(data, "release-acceptance", {"requirements_sha256", "identities", "issues", "proof_scope", "schema_registry"})
    require(data["requirements_sha256"] == digest(raw_requirements), "acceptance criterion snapshot changed")
    require(data["identities"] == IDENTITIES and type(data["identities"]["qrate_schema"]) is int,
            "edition/release/schema coordinates differ")
    snapshot.ref(root, data["schema_registry"])
    require(data["schema_registry"]["path"] == "lean/schema-registry.json", "wrong schema registry")
    rows = indexed(data["issues"], "acceptance Issues", ISSUES)
    for required in expected["issues"]:
        number = required["id"]
        row = rows[number]
        exact_keys(row, {"id", "criteria"}, f"accepted Issue {number}")
        criteria = indexed(row["criteria"], f"Issue {number} criteria", {c["id"] for c in required["criteria"]})
        for criterion in required["criteria"]:
            record = criteria[criterion["id"]]
            exact_keys(record, {"id", "disposition", "review", "evidence"}, "criterion evidence")
            wanted = "implemented" if criterion["scope"] == "required" else "explicit-later-version"
            require(record["disposition"] == wanted, f"Issue {number}/{criterion['id']}: unresolved or unauthorized exclusion")
            snapshot.ref(root, record["review"])
            require(type(record["evidence"]) is dict and record["evidence"].keys() == set(criterion["roles"]),
                    f"Issue {number}: missing/unknown evidence roles")
            for ref in record["evidence"].values():
                snapshot.ref(root, ref)
    scope = data["proof_scope"]
    exact_keys(scope, {"claim", "ledger_sha256", "admitted", "pending"}, "proof scope")
    require(scope["claim"] == "scoped-pre-v1", "this gate cannot establish full constitutional conformance")
    require(scope["ledger_sha256"] == digest(snapshot.read(root, LEDGER)), "stale proof-status disclosure")
    for field, ledger_key in [("admitted", "discharged_guarantees"), ("pending", "pending_obligations")]:
        require(type(scope[field]) is list and scope[field] == sorted(row["id"] for row in ledger[ledger_key]),
                f"proof scope {field}: removed guarantee, fabricated discharge or hidden pending duty")
    return data


def hosted_context(root, env):
    require(env.get("GITHUB_ACTIONS") == "true", "require trusted same-run hosted context; offline JSON is not CI provenance")
    require(env.get("GITHUB_REPOSITORY") == "MGYamada/Qleisli", "unexpected hosted repository")
    event = env.get("GITHUB_EVENT_NAME")
    require(event in {"push", "workflow_dispatch"}, "release readiness requires a tag or explicit manual request")
    if event == "push":
        require(env.get("GITHUB_REF", "").startswith("refs/tags/v"), "push readiness requires a release tag")
    else:
        require(env.get("RELEASE_READINESS") == "true", "manual readiness must be explicitly requested")
    for name in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"):
        require(re.fullmatch(r"[1-9][0-9]*", env.get(name, "")) is not None, f"invalid {name}")
    candidate = clean_candidate(root)
    require(candidate["commit"] == env.get("GITHUB_SHA"), "checkout differs from trusted hosted commit")
    return dict(repository=env["GITHUB_REPOSITORY"], commit=candidate["commit"], tree=candidate["tree"],
                run_id=env["GITHUB_RUN_ID"], attempt=env["GITHUB_RUN_ATTEMPT"], event=event)


def capture_context(root, env):
    """Producer identity also supports normal full/model proof jobs."""
    require(env.get("GITHUB_ACTIONS") == "true" and env.get("GITHUB_REPOSITORY") == "MGYamada/Qleisli",
            "producer requires hosted repository context")
    candidate = clean_candidate(root)
    require(candidate["commit"] == env.get("GITHUB_SHA"), "producer commit mismatch")
    for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"):
        require(re.fullmatch(r"[1-9][0-9]*", env.get(key, "")) is not None, f"invalid {key}")
    return dict(repository=env["GITHUB_REPOSITORY"], commit=candidate["commit"], tree=candidate["tree"],
                run_id=env["GITHUB_RUN_ID"], attempt=env["GITHUB_RUN_ATTEMPT"], event=env["GITHUB_EVENT_NAME"])


def write_json(path, data):
    with path.open("x", encoding="utf-8") as out:
        json.dump(data, out, indent=2, sort_keys=True)
        out.write("\n")


def record_constitution(root, output, env):
    from check_constitution import check_constitution
    require(not output.resolve().is_relative_to(root.resolve()), "receipt must be outside candidate")
    context = capture_context(root, env)
    before = read_file(root, LEDGER)
    result = check_constitution(root, verify_lean=True)
    require(capture_context(root, env) == context and read_file(root, LEDGER) == before,
            "source/evidence changed during live constitutional replay")
    write_json(output, dict(format="qleisli.release-constitution", version=1, context=context,
                            ledger_sha256=digest(before), result=result))


def record_job(root, output, job, env, *, distribution=None, native=None, constitution=None):
    require(job in SUITES and env.get("GITHUB_JOB") == job, "wrong producer job")
    context = hosted_context(root, env)
    require(not output.resolve().is_relative_to(root.resolve()), "receipt must be outside candidate")
    output.mkdir(parents=True, exist_ok=False)
    files = {}
    def copy(path, name):
        data = read_file(path.parent, path.name)
        (output / name).write_bytes(data)
        files[name] = digest(data)
    if job == "check-distribution":
        require(distribution is not None, "distribution producer missing report")
        data = json_object(read_file(distribution.parent, distribution.name), "distribution report")
        require(data.get("status") == "passed", "failed distribution validation")
        copy(distribution, "distribution.json")
        for key, name in [("crate", "package.crate"), ("source_archive", "source.tar")]:
            source = Path(data[key]["path"])
            require(source.resolve().parent == Path(data["artifacts"]).resolve()
                    and source.resolve().is_relative_to(distribution.parent.resolve()), "distribution file outside producer directory")
            copy(source, name)
    elif job in NATIVE_JOBS:
        require(native is not None, "native producer missing asset directory")
        version = tomllib.loads(read_file(root, "Cargo.toml").decode())["package"]["version"]
        name = f"qleisli-kernel-{version}-{NATIVE_JOBS[job]}.tar.gz"
        copy(native / name, name)
        copy(native / (name + ".sha256"), name + ".sha256")
    elif job == "check-lean":
        require(constitution is not None, "Lean producer missing live replay receipt")
        copy(constitution, "constitution.json")
    require(capture_context(root, env) == context, "candidate changed during receipt recording")
    receipt = dict(format="qleisli.release-job", version=1, context=context, job=job, files=files)
    write_json(output / "receipt.json", receipt)
    with open(env["GITHUB_OUTPUT"], "a", encoding="utf-8") as out:
        out.write(f"release_receipt_sha256={digest((output / 'receipt.json').read_bytes())}\n")


def receipts(evidence, needs, context, snapshot):
    check_needs(needs, context["commit"])
    selection = needs["changes"]["outputs"]
    require(selection["profile"] == "full" and selection["proof_lane"] == "full", "release requires full suites and full proof lane")
    result = {}
    for job in SUITES:
        expected = needs[job].get("outputs", {}).get("release_receipt_sha256")
        require(type(expected) is str and SHA.fullmatch(expected), f"{job}: missing trusted producer digest")
        directory = evidence / f"release-receipt-{job}-{context['commit']}-{context['attempt']}"
        raw = snapshot.read(directory, "receipt.json")
        require(digest(raw) == expected, f"{job}: receipt differs from trusted producer digest")
        receipt = json_object(raw, job)
        envelope(receipt, "release-job", {"context", "job", "files"})
        require(receipt["context"] == context and receipt["job"] == job, f"{job}: wrong commit/tree/run/attempt/job identity")
        require(type(receipt["files"]) is dict, "receipt files must be an object")
        files = {name: snapshot.ref(directory, dict(path=name, sha256=sha)) for name, sha in receipt["files"].items()}
        result[job] = files
    return result


def archive_bytes(data, *, prefix="", expected=None):
    # Parse exactly the snapshotted bytes, never reopen a mutable supplied path.
    with tempfile.TemporaryDirectory(prefix="qleisli-release-archive-") as temporary:
        path = Path(temporary) / "asset.tar"
        path.write_bytes(data)
        return read_archive(path, prefix=prefix, expected=expected)


def artifacts(root, files, context, version, snapshot):
    tracked = tracked_files(root, context["commit"])
    for (directory, name), data in snapshot.files.items():
        if directory == root:
            require(name in tracked and tracked[name].data == data,
                    f"candidate evidence must be an exact tracked Git blob: {name}")
    dist = files["check-distribution"]
    require(dist.keys() == {"distribution.json", "package.crate", "source.tar"}, "incomplete package/source/install evidence")
    report = json_object(dist["distribution.json"], "distribution report")
    require(report.get("format") == "qleisli.distribution-validation" and type(report.get("version")) is int
            and report["version"] == 1 and report.get("status") == "passed", "failed/unknown distribution report")
    require(report.get("candidate") == {"commit": context["commit"], "tree": context["tree"], "clean": True}, "distribution candidate mismatch")
    require(report.get("package", {}).get("version") == version, "distribution product version mismatch")
    require(report.get("installed_quickstart", {}).get("package") == "qleisli"
            and report["installed_quickstart"].get("version") == version
            and report["installed_quickstart"].get("checks") == ["Bell check/run/sample in text and JSON", "embedded qft2", "reject measured-owner reuse"], "fresh installation did not pass")
    require(report.get("commands") and all(type(c.get("exit_code")) is int and c["exit_code"] == 0 for c in report["commands"]), "missing/failed distribution commands")
    for key, name in [("crate", "package.crate"), ("source_archive", "source.tar")]:
        require(report.get(key, {}).get("sha256") == digest(dist[name]), f"{name}: distribution digest mismatch")
    archive_bytes(dist["source.tar"], expected=tracked)
    crate = archive_bytes(dist["package.crate"], prefix=f"qleisli-{version}")
    vcs = json_object(crate[".cargo_vcs_info.json"].data, "crate VCS")
    require(vcs.get("git", {}).get("sha1") == context["commit"] and not vcs.get("git", {}).get("dirty", False), "crate source commit mismatch")
    manifest = tomllib.loads(crate["Cargo.toml"].data.decode())
    require(manifest["package"]["version"] == version, "crate version mismatch")
    for job, target in NATIVE_JOBS.items():
        name = f"qleisli-kernel-{version}-{target}.tar.gz"
        require(files[job].keys() == {name, name + ".sha256"}, f"{job}: missing/unexpected native assets")
        require(files[job][name + ".sha256"] == f"{digest(files[job][name])}  {name}\n".encode(), "native checksum mismatch")
        payload = archive_bytes(files[job][name], prefix=name[:-7])
        distribution = json_object(payload["distribution.json"].data, "native distribution")
        envelope(distribution, "kernel-distribution", {"source_commit", "package_version", "target", "bundle_manifest_sha256", "archive_script_sha256"})
        require((distribution["source_commit"], distribution["package_version"], distribution["target"]) == (context["commit"], version, target), "native source/version/target mismatch")
        require(distribution["archive_script_sha256"] == digest(snapshot.read(root, "scripts/archive_lean_kernel.py")), "native archive script differs")
        require(distribution["bundle_manifest_sha256"] == digest(payload["manifest.json"].data), "native manifest digest mismatch")
        bundle = json_object(payload["manifest.json"].data, "native manifest")
        require(bundle.get("format") == "qleisli.native-bundle" and type(bundle.get("version")) is int and bundle["version"] == 1,
                "unknown native manifest")
        require(bundle.get("package_version") == version and bundle.get("protocol") == IDENTITIES["native_protocol"], "native release/protocol mismatch")
        require(bundle.get("validation", {}).get("lane") == "full" and bundle["validation"].get("fresh_replay") is True, "native fresh full replay missing")
        expected_sources = {path for path in tracked if path.startswith("lean-kernel/") and (path.endswith(".lean") or Path(path).name in {"lakefile.toml", "lake-manifest.json", "lean-toolchain"})}
        expected_sources.update({"scripts/check_lean_kernel.py", "scripts/package_lean_kernel.py"})
        require(type(bundle.get("sources")) is dict and bundle["sources"].keys() == expected_sources, "native source inventory missing/incomplete")
        for path, sha in bundle["sources"].items():
            require(path in tracked and digest(tracked[path].data) == sha, "native source identity mismatch")
        hashes = {path: digest(value.data) for path, value in payload.items() if path not in {"manifest.json", "distribution.json", "INSTALL.txt"}}
        require(hashes == bundle.get("files") and {"bin/qleisli-kernel", "LICENSE", "NOTICE", "lean-runtime-licenses/LICENSE"} <= hashes.keys(), "native payload inventory mismatch")


def _check(root=ROOT, *, base_ref=None, env=None, evidence=None):
    env = dict(os.environ if env is None else env)
    require(base_ref is not None, "release readiness requires caller-selected trusted base and hosted evidence context; admission is not release approval")
    root = Path(root).resolve()
    context = hosted_context(root, env)
    snapshot = Snapshot()
    expected, raw = requirements(root, base_ref, snapshot)
    version = tomllib.loads(snapshot.read(root, "Cargo.toml").decode())["package"]["version"]
    require(re.fullmatch(r"0\.3\.0(?:-(?:alpha|beta|rc)(?:\.[1-9][0-9]*)?)?", version), "gate supports only scoped 0.3.0 product releases")
    if context["event"] == "push":
        require(env["GITHUB_REF"] == f"refs/tags/v{version}", "release tag and product version differ")
    require(not version_plan(root, version), "product versions are not synchronized")
    from check_constitution import check_constitution
    result = check_constitution(root, base_ref=base_ref)
    ledger = json_object(snapshot.read(root, LEDGER), LEDGER)
    acceptance(root, expected, raw, snapshot, ledger)
    require(evidence is not None or env.get("RELEASE_EVIDENCE"), "missing downloaded producer evidence directory")
    directory = Path(evidence or env["RELEASE_EVIDENCE"]).resolve()
    require(not directory.is_relative_to(root), "verification receipts must be outside candidate commit")
    needs = json_object(env.get("RELEASE_NEEDS_JSON", "").encode(), "trusted workflow needs")
    files = receipts(directory, needs, context, snapshot)
    proof_files = files["check-lean"]
    require(proof_files.keys() == {"constitution.json"}, "missing live constitutional proof receipt")
    proof = json_object(proof_files["constitution.json"], "constitutional receipt")
    envelope(proof, "release-constitution", {"context", "ledger_sha256", "result"})
    require(proof["context"] == context and proof["ledger_sha256"] == digest(snapshot.read(root, LEDGER)), "stale constitutional replay")
    require(proof["result"] == dict(result, mode="current-Lean-replay"), "source-only or mismatched guarantee replay")
    for job in set(SUITES) - {*NATIVE_JOBS, "check-lean", "check-distribution"}:
        require(not files[job], f"{job}: unexpected evidence files")
    artifacts(root, files, context, version, snapshot)
    snapshot.unchanged()
    require(hosted_context(root, env) == context, "candidate changed during readiness verification")
    return dict(format="qleisli.release-readiness", version=1, context=context, product_version=version,
                identities=IDENTITIES, status="ready-scoped-candidate", publication="not-authorized-or-performed",
                admitted=result["admitted_guarantees"], pending=result["pending_obligations"])


def check(root=ROOT, *, base_ref=None, env=None, evidence=None):
    try:
        return _check(root, base_ref=base_ref, env=env, evidence=evidence)
    except PacketError:
        raise
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError) as error:
        # Keep malformed artifact failures in the same fail-closed API used by
        # the legacy constitutional CLI, without a traceback or success receipt.
        raise PacketError(f"invalid release evidence: {error}") from error


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--base-ref")
    parser.add_argument("--evidence", type=Path)
    parser.add_argument("--record-job", choices=SUITES)
    parser.add_argument("--record-constitution", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--distribution", type=Path)
    parser.add_argument("--native", type=Path)
    parser.add_argument("--constitution", type=Path)
    args = parser.parse_args(argv)
    try:
        require(not (args.record_job and args.record_constitution), "select only one producer")
        if args.record_job or args.record_constitution:
            require(args.output is not None, "producer requires --output")
            if args.record_constitution:
                record_constitution(args.root, args.output, os.environ)
            else:
                record_job(args.root, args.output, args.record_job, os.environ,
                           distribution=args.distribution, native=args.native, constitution=args.constitution)
        else:
            result = check(args.root, base_ref=args.base_ref or os.environ.get("RELEASE_TRUSTED_BASE"), evidence=args.evidence)
            print(json.dumps(result, sort_keys=True))
        return 0
    except (PacketError, OSError, ValueError, KeyError, TypeError, UnicodeError) as error:
        print(f"release readiness: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
