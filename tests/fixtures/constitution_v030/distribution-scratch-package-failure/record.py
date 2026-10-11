#!/usr/bin/env python3
"""Record the small package-failure and preservation-failure regressions.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root, output = args.root.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    sys.path.insert(0, str(root / "scripts"))
    from test_check_distribution import ScratchTests

    observations = []
    methods = ["test_failed_package_preserves_unverified_crate_before_cleanup",
               "test_partial_copy_failure_preserves_sole_crate_and_original_failure",
               "test_failed_crate_preservation_keeps_external_target_without_retaining_work"]
    for method in methods:
        case = ScratchTests(method)
        case.setUp()
        run_validation = case.run_validation

        def observed_run(**kwargs):
            report, driver = run_validation(**kwargs)
            number = len(observations)
            prefix = f"{number:02d}"
            (output / (prefix + "-report.json")).write_bytes((case.base / "report.json").read_bytes())
            command = report["commands"][-1]
            for stream in ["stdout", "stderr"]:
                (output / (prefix + "-command." + stream)).write_bytes(Path(command[stream]).read_bytes())
            retained = report.get("unverified_crate", {}).get("path") or report.get("unretained_crate_path")
            data = Path(retained).read_bytes()
            assert data == driver.crate_bytes
            partials = {p.name: base64.b64encode(p.read_bytes()).decode()
                        for p in Path(report["artifacts"]).glob("*.partial")}
            observations.append({"case": method, "fail_package": kwargs.get("fail_package", False),
                "report": prefix + "-report.json", "status": report["status"],
                "work": report["work"], "candidate_bytes_preserved": True,
                "candidate_sha256": hashlib.sha256(data).hexdigest(),
                "candidate_base64": base64.b64encode(data).decode(),
                "partial_base64": partials})
            return report, driver

        case.run_validation = observed_run
        try:
            getattr(case, method)()
        finally:
            case.doCleanups()
    record = {"scope": "Synthetic Cargo/client execution with real validator, archives, copies and cleanup. "
                       "All bytes are tiny fixture data. No Cargo/Lean build or installer was run. "
                       "Test harness removes its own temporary repositories after observation.",
              "argv": sys.argv, "python": sys.version,
              "sources": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                          for name in ["scripts/check_distribution.py", "scripts/test_check_distribution.py"]},
              "observations": observations}
    (output / "observations.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps([{"case": item["case"], "fail_package": item["fail_package"],
                       "status": item["status"], "work": item["work"]["status"],
                       "candidate_bytes_preserved": item["candidate_bytes_preserved"]}
                      for item in observations], indent=2))


if __name__ == "__main__":
    main()
