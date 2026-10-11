#!/usr/bin/env python3
"""Record small synthetic distribution runs without compiling or installing.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import contextlib
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--baseline", type=Path,
                        help="run the two original cases using the saved pre-change validator")
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    sys.path.insert(0, str(root / "scripts"))
    import check_distribution as validator
    import test_check_distribution as tests

    source = root / "scripts/check_distribution.py"
    if args.baseline:
        source = args.baseline.resolve()
        spec = importlib.util.spec_from_loader("distribution_baseline", loader=None)
        validator = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = validator
        exec(compile(source.read_bytes(), str(source), "exec"), validator.__dict__)
    cases = [("success", False, False, False, False),
             ("failure", True, False, False, False)]
    if not args.baseline:
        cases += [("keep-success", False, True, False, False),
                  ("keep-failure", True, True, False, False),
                  ("external-success", False, False, True, False),
                  ("external-failure", True, False, True, False),
                  ("cleanup-error", False, False, False, True),
                  ("failure-and-cleanup-error", True, False, False, True)]
    records = []
    for name, fail, keep, external, cleanup_error in cases:
        case = tests.ScratchTests()
        case.setUp()
        try:
            kwargs = {} if args.baseline else {"keep_work": keep}
            if external:
                target = case.base / "caller-target"
                target.mkdir()
                (target / "sentinel").write_bytes(b"caller owned\n")
                kwargs["target_dir"] = target
            with contextlib.ExitStack() as stack:
                stack.enter_context(patch.object(tests, "validate", validator.validate))
                if cleanup_error:
                    stack.enter_context(patch.object(validator.shutil, "rmtree",
                        side_effect=OSError("synthetic cleanup denied")))
                report, driver = case.run_validation(fail=fail, **kwargs)
            case.assert_durable_evidence(report)
            directory = output / name
            directory.mkdir()
            (directory / "report.json").write_bytes((case.base / "report.json").read_bytes())
            (directory / "logs").mkdir()
            for path in (Path(report["artifacts"]) / "logs").iterdir():
                (directory / "logs" / path.name).write_bytes(path.read_bytes())
            work = Path(report.get("work", {}).get("path") or report["artifacts"])
            records.append({"case": name, "result": report["status"],
                "work_status": report.get("work", {}).get("status", "legacy-unreported"),
                "source_present_after_validate": (work / "source").is_dir(),
                "package_present_after_validate": (work / "packaged-source").is_dir(),
                "installation_present_after_validate": driver.installed.is_dir(),
                "target_count": len(driver.target_paths),
                "targets_present_after_validate": sum(path.is_dir() for path in driver.target_paths),
                "external_sentinel_unchanged": (target / "sentinel").read_bytes() == b"caller owned\n"
                    if external else None,
                "durable_evidence_verified": True})
        finally:
            # The harness owns its entire tiny fixture. This is separate from
            # the validator's lifecycle being observed above.
            case.doCleanups()
    record = {"scope": "Synthetic Rust/Cargo/client commands; real local Git, archives and validator. "
                       "No compiler, installer or Lean execution. Harness removes its tiny fixture "
                       "after recording; original report paths are historical locations.",
              "argv": sys.argv, "python": sys.version,
              "validator": str(source), "validator_sha256": sha(source),
              "driver_sha256": sha(root / "scripts/test_check_distribution.py"),
              "observations": records}
    (output / "observations.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
