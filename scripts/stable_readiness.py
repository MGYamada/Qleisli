"""Validate the 0.3.0 stable supplement and its earlier Actions run.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import datetime
import io
import re
import subprocess
import zipfile

from check_ratification_packet import json_object

REQUIREMENTS = "release/stable-requirements.json"
ACCEPTANCE = "release/stable-acceptance.json"
BASELINE_ACCEPTANCE = "release/stable-baseline-acceptance.json"
CRITERIA = {
    "349-manifest-selection": {"implementation", "reference", "positive", "negative"},
    "349-version-sync-packaging": {"implementation", "positive", "production"},
    "349-companion-candidate": {"compatibility"},
    "622-request-and-admission": {"implementation", "reference", "production"},
    "622-compatibility-migration": {"migration", "positive", "negative"},
    "622-cli-outcomes": {"implementation", "positive", "negative"},
}
TARGETS = {
    "aarch64-apple-darwin",
    "x86_64-apple-darwin",
    "x86_64-unknown-linux-musl",
}
TOOLS = {"qlirgo", "qlinties", "qlifmt", "qlidoc"}
WORKFLOW_PATH = ".github/workflows/ci.yml"


def requirements(root, base, baseline, snapshot):
    from check_release_ready import COMMIT, IDENTITIES, digest, envelope, git, indexed, require
    from check_ratification_packet import PacketError

    try:
        raw = git(root, "show", f"{base}:{REQUIREMENTS}")
    except PacketError as cause:
        raise PacketError("stable release requires a supplement from the reviewed requirements base") from cause
    data = json_object(raw, REQUIREMENTS)
    envelope(data, "stable-requirements", {
        "product_version", "baseline_sha256", "identities", "criteria", "companion_commit", "review",
    })
    require(data["product_version"] == "0.3.0" and data["baseline_sha256"] == digest(baseline),
            "stable supplement is for another product version or baseline")
    identities = dict(IDENTITIES, native_protocol="qleisli.native-result 4")
    require(data["identities"] == identities and type(data["identities"]["qrate_schema"]) is int,
            "stable supplement has incorrect interface identities")
    require(type(data["companion_commit"]) is str and COMMIT.fullmatch(data["companion_commit"]),
            "stable supplement must pin the exact qlirgo candidate commit")
    rows = indexed(data["criteria"], "stable criteria", set(CRITERIA))
    for identifier, row in rows.items():
        require(row == {"id": identifier, "roles": sorted(CRITERIA[identifier])},
                f"{identifier}: reviewed stable evidence roles differ")
    review = data["review"]
    checked = snapshot.ref(root, review)
    require(checked == git(root, "show", f"{base}:{review['path']}"),
            "stable supplement review must be in the reviewed requirements base")
    return data, raw


def acceptance(root, expected, raw, snapshot):
    from check_release_ready import digest, envelope, indexed, require

    data = json_object(snapshot.read(root, ACCEPTANCE), ACCEPTANCE)
    envelope(data, "stable-acceptance", {"requirements_sha256", "criteria"})
    require(data["requirements_sha256"] == digest(raw), "stable acceptance references stale requirements")
    rows = indexed(data["criteria"], "stable criterion evidence", set(CRITERIA))
    for identifier, roles in CRITERIA.items():
        row = rows[identifier]
        require(row.keys() == {"id", "status", "evidence"} and row["status"] == "passed",
                f"{identifier}: missing or unsuccessful stable criterion")
        require(type(row["evidence"]) is dict and row["evidence"].keys() == roles,
                f"{identifier}: missing or unexpected stable evidence roles")
        for ref in row["evidence"].values():
            snapshot.ref(root, ref)
    return expected["companion_commit"]


def companion(receipt, context, commit, crate_sha, std_sha, kernels):
    from check_release_ready import SHA, envelope, indexed, require

    envelope(receipt, "stable-companion-qualification", {
        "context", "companion_commit", "companion_version", "compiler_version", "dependency_kind",
        "crate_sha256", "std_manifest_sha256", "hosts",
    })
    require(receipt["context"] == context and receipt["companion_commit"] == commit,
            "companion evidence has a different candidate, run or attempt")
    require(receipt["compiler_version"] == "0.3.0" and receipt["companion_version"] == "0.2.0"
            and receipt["dependency_kind"] == "candidate-package",
            "stable companion qualification requires the non-registry candidate pair")
    require(receipt["crate_sha256"] == crate_sha and receipt["std_manifest_sha256"] == std_sha,
            "companion evidence used a different crate or bundled std")
    hosts = indexed(receipt["hosts"], "companion hosts", TARGETS)
    for target, host in hosts.items():
        require(host.keys() == {"id", "tools", "kernel_sha256", "kernel_origin", "checks"}
                and type(host["tools"]) is dict and host["tools"].keys() == TOOLS
                and all(type(value) is str and SHA.fullmatch(value) for value in host["tools"].values())
                and type(host["kernel_sha256"]) is str and SHA.fullmatch(host["kernel_sha256"])
                and host["checks"] == ["manifest-pair", "check", "build", "lint", "fmt", "doc"],
                f"{target}: incomplete companion evidence")
        if target == "x86_64-apple-darwin":
            require(host["kernel_origin"] == "full-source-replay", "Intel Mac requires exact source replay")
        else:
            upstream = "x86_64-unknown-linux-gnu" if target.endswith("musl") else target
            require(host["kernel_origin"] == "candidate-native-bundle"
                    and host["kernel_sha256"] == kernels[upstream], f"{target}: wrong candidate checker")


def github(path):
    from check_release_ready import require

    result = subprocess.run(["gh", "api", path], capture_output=True, timeout=45)
    require(result.returncode == 0, f"Actions verification failed for {path}")
    return result.stdout


def positive_id(value):
    return type(value) is str and re.fullmatch(r"[1-9][0-9]*", value) is not None


def timestamp(value):
    return datetime.datetime.fromisoformat(value.replace("Z", "+00:00"))


def artifact_name(context):
    return f"stable-pre-tag-{context['commit']}-{context['attempt']}"


def previous_record(env, context, expected, api=None):
    """Read trusted Actions metadata and artifact bytes for the configured run/attempt."""
    from check_release_ready import digest, require

    if api is None:
        api = github
    run = env.get("RELEASE_PRETAG_RUN_ID")
    attempt = env.get("RELEASE_PRETAG_ATTEMPT")
    require(positive_id(run) and positive_id(attempt) and run != context["run_id"],
            "stable tag requires a separate reviewed pre-tag run and attempt")
    prefix = f"repos/{context['repository']}/actions"
    prior = f"{prefix}/runs/{run}"
    current = json_object(api(f"{prefix}/runs/{context['run_id']}"), "tag run")
    meta = json_object(api(f"{prior}/attempts/{attempt}"), "pre-tag attempt")
    require(current["id"] == int(context["run_id"]) and current["event"] == "push"
            and current["head_sha"] == context["commit"] and current["path"] == WORKFLOW_PATH
            and current["repository"]["full_name"] == context["repository"],
            "tag workflow identity differs")
    require(meta["id"] == int(run) and meta["run_attempt"] == int(attempt)
            and meta["event"] == "workflow_dispatch" and meta["head_branch"] == "main"
            and meta["path"] == WORKFLOW_PATH and meta["workflow_id"] == current["workflow_id"]
            and meta["head_repository"]["full_name"] == context["repository"]
            and meta["head_sha"] == context["commit"] and meta["status"] == "completed"
            and meta["conclusion"] == "success", "earlier run is not the matching successful pre-tag attempt")
    jobs = json_object(api(f"{prior}/attempts/{attempt}/jobs?per_page=100"), "pre-tag jobs")
    gates = [job for job in jobs["jobs"] if job["name"] == "release-readiness"]
    require(len(gates) == 1 and gates[0]["conclusion"] == "success"
            and timestamp(meta["updated_at"]) < timestamp(current["created_at"])
            and timestamp(gates[0]["completed_at"]) < timestamp(current["created_at"]),
            "pre-tag release gate did not complete before the tag run")
    prior_context = dict(context, event="workflow_dispatch", run_id=run, attempt=attempt)
    name = artifact_name(prior_context)
    rows = json_object(api(f"{prior}/artifacts?name={name}&per_page=100"), "pre-tag artifacts")
    items = [row for row in rows["artifacts"] if row["name"] == name]
    require(len(items) == 1 and items[0]["expired"] is False, "missing or expired pre-tag record")
    item = items[0]
    require(item["workflow_run"]["id"] == int(run) and item["workflow_run"]["head_sha"] == context["commit"]
            and type(item["id"]) is int and item["id"] > 0 and 0 < item["size_in_bytes"] <= 65536,
            "pre-tag record has the wrong run identity or size")
    archive = api(f"{prefix}/artifacts/{item['id']}/zip")
    require(len(archive) == item["size_in_bytes"] and item["digest"] == f"sha256:{digest(archive)}",
            "pre-tag record differs from the Actions artifact")
    with zipfile.ZipFile(io.BytesIO(archive)) as bundle:
        require(bundle.namelist() == ["stable-pre-tag.json"] and
                bundle.getinfo("stable-pre-tag.json").file_size <= 16384, "invalid pre-tag artifact contents")
        accepted = json_object(bundle.read("stable-pre-tag.json"), "pre-tag record")
    require(accepted == dict(expected, context=prior_context), "pre-tag record does not match this stable release")
