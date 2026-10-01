#!/usr/bin/env python3
"""Exercise the documented quickstart with an already installed executable.

Runs outside the checkout with no helper tools on the child's PATH. Does not
download, install or publish anything. Python 3.11+ is a development dependency.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import argparse
import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib


def require(condition, message):
    if not condition:
        raise ValueError(message)


def quickstart(path):
    text = path.read_text(encoding="utf-8")
    matches = re.findall(
        r"<!-- quickstart:bell -->\s*```qli\n(.*?)```\s*<!-- /quickstart:bell -->",
        text, re.DOTALL,
    )
    require(len(matches) == 1, f"expected one marked Bell program in {path}")
    return text, matches[0]


def quickstart_manifest(text):
    matches = re.findall(
        r"<!-- quickstart:manifest -->\s*```toml\n(.*?)```\s*<!-- /quickstart:manifest -->",
        text, re.DOTALL,
    )
    require(len(matches) == 1, "expected one marked edition manifest")
    manifest = tomllib.loads(matches[0])
    require(manifest == {"schema-version": 2, "qrate": {"edition": "2026"}},
            "quickstart must declare edition 2026 explicitly")
    return matches[0]


def check(root, binary):
    package = tomllib.loads((root / "Cargo.toml").read_text())["package"]
    registry = root / package["readme"]
    readme, source = quickstart(root / "README.md")
    landing, landing_source = quickstart(registry)
    require(source == landing_source, "repository and registry quickstarts differ")
    manifest = quickstart_manifest(readme)
    require(manifest == quickstart_manifest(landing), "quickstart edition manifests differ")
    install = f'cargo install {package["name"]} --version {package["version"]} --locked'
    for text in [readme, landing]:
        require(install in text, "quickstart install command differs from manifest")
    # The registry page must not depend on relative repository links or MathJax.
    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", landing):
        require(target.startswith(("https://", "#")), f"relative registry link: {target}")
        prefix = "https://github.com/MGYamada/Qleisli/blob/"
        if target.startswith(prefix):
            ref, relative = target[len(prefix):].split("/", 1)
            require(ref == "v" + package["version"], "registry link uses a different source version")
            require((root / relative.split("#")[0]).is_file(),
                    f"missing registry link target: {target}")
    require("```math" not in landing and "$$" not in landing,
            "registry README requires a math renderer")

    with tempfile.TemporaryDirectory(prefix="qleisli-installed-") as directory:
        work = Path(directory)
        empty_path = work / "no-helper-tools"
        empty_path.mkdir()
        env = dict(os.environ, PATH=str(empty_path))

        def invoke(*args, status=0, structured=True):
            command = [str(binary), *args]
            if structured:
                command.append("--format=json")
            result = subprocess.run(command, cwd=work, env=env, capture_output=True,
                                    text=True, timeout=60, check=False)
            require(result.returncode == status and not result.stderr,
                    f"{args}: exit {result.returncode}: {result.stderr or result.stdout}")
            if not structured:
                return result.stdout
            payload = json.loads(result.stdout)
            require(payload["format"] == "qleisli.result" and payload["version"] == 1,
                    "unexpected JSON envelope")
            require(payload["outcome"] == ("error" if status else "ok"),
                    "unexpected command outcome")
            return payload

        def write_project(name, body):
            project = work / name
            project.mkdir()
            (project / "Qargo.toml").write_text(manifest, encoding="utf-8")
            (project / "main.qli").write_text(body, encoding="utf-8")

        write_project("bell", source)
        invoke("check", "bell", structured=False)
        output = invoke("run", "bell", structured=False)
        text_distribution = {bits: float(weight) for bits, weight in
                             (row.split(": ") for row in output.splitlines())}
        require(set(text_distribution) == {"00", "11"}
                and all(math.isclose(p, 0.5, abs_tol=1e-12, rel_tol=0)
                        for p in text_distribution.values()), "wrong Bell distribution")
        invoke("sample", "bell", "--shots=8", "--seed=0", structured=False)
        require(invoke("check", "bell")["result"] == {"verified": True},
                "Bell was not verified")
        sampled = invoke("sample", "bell", "--shots=8", "--seed=0")
        shots = sampled["result"]["shots"]
        require(len(shots) == 8 and all(s["bits"] in [[False, False], [True, True]]
                                      for s in shots), "invalid Bell shots")

        # Resolve an ordinary embedded .qli library module, not only built-ins.
        write_project("bundled-library", """
use std::quantum::init0;
use std::quantum::join;
use std::quantum::split;
use std::transforms::qft2;
use std::observe::measure_z;
observe fn main() -> (CBit, CBit) {
    let (a, b) = split(qft2(join(init0(), init0())));
    (measure_z(a), measure_z(b))
}
""")
        rows = invoke("run", "bundled-library")["result"]["distribution"]
        require({tuple(row["bits"]) for row in rows}
                == {(False, False), (False, True), (True, False), (True, True)}
                and len(rows) == 4
                and all(math.isclose(row["probability"], 0.25, abs_tol=1e-12, rel_tol=0)
                        for row in rows), "embedded QFT library failed")

        write_project("invalid-ownership", """
use std::quantum::init0;
use std::observe::measure_z;
observe fn main() -> (CBit, CBit) {
    let q = init0();
    (measure_z(q), measure_z(q))
}
""")
        rejected = invoke("check", "invalid-ownership", status=1)
        require(any(d["code"] == "ownership" for d in rejected["diagnostics"]),
                "reuse of a measured owner did not produce an ownership diagnostic")
    return {"package": package["name"], "version": package["version"],
            "binary": str(binary), "readmes": "matching Bell source and version",
            "registry_links": "absolute; repository targets exist locally",
            "checks": ["Bell check/run/sample in text and JSON", "embedded qft2",
                       "reject measured-owner reuse"],
            "execution": "temporary directory; empty helper-tool PATH",
            "publication": "not performed"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.root.resolve(), args.binary.resolve()), indent=2))
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f"installation check failed: {error}\n")


if __name__ == "__main__":
    main()
