"""Run the stable qlirgo candidate against a checked, unpacked Qleisli crate.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib

from check_release_ready import capture_context, digest, git, require, write_json
from check_ratification_packet import PacketError, json_object
from check_distribution import read_archive
from stable_readiness import TARGETS, TOOLS, REQUIREMENTS


def selected_commit(root, base):
    from check_release_ready import COMMIT

    require(COMMIT.fullmatch(base), "stable companion requires an exact reviewed base")
    packet = json_object(git(root, "show", f"{base}:{REQUIREMENTS}"), REQUIREMENTS)
    require(packet.get("product_version") == "0.3.0" and
            COMMIT.fullmatch(packet.get("companion_commit", "")), "invalid stable companion pin")
    return packet["companion_commit"]


def materialize(archive, prefix, root):
    for name, item in read_archive(archive, prefix=prefix).items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(item.data)
        path.chmod(item.mode)


def command(argv, directory, env):
    subprocess.run(argv, cwd=directory, env=env, check=True)


def manifest_cases(binary, env, temporary):
    valid = (b'schema-version = 2\n[qrate]\nname = "sample"\nversion = "0.1.0"\n'
             b'edition = "2026"\n[source]\nroot = "src"\n'
             b'[tests]\nroot = "tests"\n[docs]\nroot = "docs"\n')
    missing = valid.replace(b'edition = "2026"\n', b'')
    for index, (canonical, legacy, accepted) in enumerate([
        (valid, None, True), (None, valid, True), (valid, valid, True),
        (valid, valid + b"# differs\n", False), (missing, None, False), (None, missing, False),
    ]):
        project = temporary / str(index)
        (project / "src").mkdir(parents=True)
        (project / "tests").mkdir()
        (project / "docs").mkdir()
        (project / "src/main.qli").write_text("observe fn main() -> Bit { measure_z(init0()) }\n")
        for name, raw in [("Qlirgo.toml", canonical), ("Qargo.toml", legacy)]:
            if raw is not None:
                (project / name).write_bytes(raw)
        name = "Qlirgo.toml" if canonical is not None else "Qargo.toml"
        run = subprocess.run([str(binary), "check", "--manifest-path", str(project / name),
                              "--format=json"], env=env, cwd=project, capture_output=True, timeout=90)
        require(run.returncode == (0 if accepted else 1),
                f"qlirgo manifest case {index} differed: {run.stdout!r} {run.stderr!r}")


def qualify(args, root):
    context = capture_context(root, os.environ)
    companion_commit = selected_commit(root, args.base)
    companion = args.companion.resolve()
    require(git(companion, "rev-parse", "HEAD").decode().strip() == companion_commit and
            not git(companion, "status", "--porcelain"), "wrong or dirty companion checkout")
    require(args.target in TARGETS, "unknown companion host")
    manifest = tomllib.loads((companion / "Cargo.toml").read_text())
    product = manifest["package"]["version"]
    dependency = manifest["workspace"]["dependencies"]["qleisli"]
    require(product == "0.2.0" and dependency == "=0.3.0", "companion version or exact Qleisli pin differs")
    crate_sha = digest(args.crate.read_bytes())
    with tempfile.TemporaryDirectory(prefix="stable-companion-") as parent:
        scope = Path(parent).resolve()
        qleisli = scope / "qleisli"
        materialize(args.crate, "qleisli-0.3.0", qleisli)
        source = json_object((qleisli / ".cargo_vcs_info.json").read_bytes(), "candidate crate VCS")
        require(source["git"]["sha1"] == context["commit"] and not source["git"].get("dirty"),
                "companion inputs do not contain the exact candidate crate")
        env = dict(os.environ, CARGO_TARGET_DIR=str(scope / "target"))
        if args.target == "x86_64-apple-darwin":
            # Run from the current exact Qleisli tree because the complete proof
            # replay includes fixtures that are intentionally outside the crate.
            native = scope / "intel-native"
            command([sys.executable, "scripts/package_lean_kernel.py", "--validation", "full",
                     "--output", str(native)], root, env)
            kernel = native / "bin/qleisli-kernel"
            origin = "full-source-replay"
        else:
            require(args.native is not None, "candidate bundle is required")
            target = "x86_64-unknown-linux-gnu" if args.target.endswith("musl") else args.target
            native = scope / "native"
            materialize(args.native, f"qleisli-kernel-0.3.0-{target}", native)
            kernel = native / "bin/qleisli-kernel"
            origin = "candidate-native-bundle"
        env["QLEISLI_KERNEL"] = str(kernel)
        # Use a disposable Git archive of the exact companion commit. Cargo can
        # resolve the local patch there without changing any release lockfile.
        archive = scope / "companion.tar"
        archive.write_bytes(git(companion, "archive", "HEAD"))
        isolated = scope / "companion"
        materialize(archive, "", isolated)
        patch = "patch.crates-io.qleisli.path=" + json.dumps(str(qleisli))
        cargo = ["cargo", "--config", patch]
        command([*cargo, "build", "--bins", "--target", args.target], isolated, env)
        metadata = json_object(subprocess.check_output(
            [*cargo, "metadata", "--locked", "--format-version=1"], cwd=isolated, env=env), "linked packages")
        linked = [item for item in metadata["packages"] if item["name"] == "qleisli"]
        require(len(linked) == 1 and linked[0]["version"] == "0.3.0" and linked[0]["source"] is None
                and Path(linked[0]["manifest_path"]) == qleisli / "Cargo.toml",
                "companion did not resolve to the candidate package")
        binaries = scope / "target" / args.target / "debug"
        command([sys.executable, "scripts/verify_release.py", "--source-root", str(isolated),
                 "--bin-dir", str(binaries), "--qleisli-source-root", str(qleisli)], isolated, env)
        manifest_cases(binaries / "qlirgo", env, scope)
        write_json(args.output, dict(
            format="qleisli.stable-companion-qualification", version=1, context=context,
            companion_commit=companion_commit, companion_version="0.2.0", compiler_version="0.3.0",
            dependency_kind="candidate-package", crate_sha256=crate_sha,
            std_manifest_sha256=digest((qleisli / "stdlib/Qlirgo.toml").read_bytes()),
            hosts=[dict(id=args.target, tools={name: digest((binaries / name).read_bytes()) for name in TOOLS},
                        kernel_sha256=digest(kernel.read_bytes()), kernel_origin=origin,
                        checks=["manifest-pair", "check", "build", "lint", "fmt", "doc"])]))


def collect(root, directory, output):
    from stable_readiness import companion

    records = [json_object(path.read_bytes(), "stable companion host") for path in
               sorted(directory.glob("*/companion.json"))]
    require(len(records) == len(TARGETS), "missing stable companion host result")
    shared = {key: value for key, value in records[0].items() if key != "hosts"}
    hosts = []
    for record in records:
        require({key: value for key, value in record.items() if key != "hosts"} == shared
                and len(record["hosts"]) == 1, "companion hosts used different candidate inputs")
        hosts.extend(record["hosts"])
    by_target = {host["id"]: host["kernel_sha256"] for host in hosts}
    combined = dict(shared, hosts=hosts)
    # The final release gate validates the candidate bundle hashes independently.
    companion(combined, capture_context(root, os.environ), shared["companion_commit"],
              shared["crate_sha256"], shared["std_manifest_sha256"],
              {"aarch64-apple-darwin": by_target["aarch64-apple-darwin"],
               "x86_64-unknown-linux-gnu": by_target["x86_64-unknown-linux-musl"]})
    write_json(output, combined)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="")
    parser.add_argument("--pin", action="store_true")
    parser.add_argument("--collect", type=Path)
    parser.add_argument("--target", choices=sorted(TARGETS))
    parser.add_argument("--companion", type=Path)
    parser.add_argument("--crate", type=Path)
    parser.add_argument("--native", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        if args.pin:
            print(selected_commit(root, args.base))
        elif args.collect:
            collect(root, args.collect, args.output)
        else:
            qualify(args, root)
    except (PacketError, OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"stable companion qualification: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
