#!/usr/bin/env python3
"""Pure maintenance refusal checks. Never execute Lean or a captured command."""
import copy
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

import refresh_current_proof_records as maintenance
import check_schema_registry as registry


class MaintenanceRefusalTests(unittest.TestCase):
    def test_timeout_kills_owned_group_even_when_parent_exits_after_term(self):
        process = Mock(pid=123, returncode=-9)
        process.wait.side_effect = [maintenance.subprocess.TimeoutExpired(["lake"], 900), 0, -9]
        with patch.object(maintenance.subprocess, "Popen", return_value=process) as launched, patch.object(maintenance.os, "killpg") as killed:
            self.assertEqual(maintenance.execute(["lake"], Path("/synthetic"), "stdout", "stderr", 900), (-9, "timeout"))
        launched.assert_called_once_with(["lake"], cwd=Path("/synthetic"), stdout="stdout", stderr="stderr", start_new_session=True)
        self.assertEqual(killed.call_args_list, [unittest.mock.call(123, maintenance.signal.SIGTERM), unittest.mock.call(123, maintenance.signal.SIGKILL)])
        self.assertEqual(process.wait.call_args_list, [unittest.mock.call(timeout=900), unittest.mock.call(timeout=5), unittest.mock.call()])
        self.assertEqual(maintenance.TIMEOUTS["full-tests"], 900)
        self.assertEqual(maintenance.TIMEOUTS["extract"], 300)

    def test_real_cli_hosted_dispatch_accepts_only_the_planned_hosted_arguments(self):
        head = "a" * 40
        context = dict(format=1, status="not-applicable", event="push", checkout_sha=head, repository="MGYamada/Qleisli", limit=1_000_000)
        with tempfile.TemporaryDirectory() as directory:
            event = Path(directory) / "event.json"
            event.write_text(json.dumps({"before": "0" * 40}))
            environment = dict(GITHUB_ACTIONS="true", GITHUB_EVENT_PATH=str(event), GITHUB_EVENT_NAME="push", GITHUB_SHA=head, GITHUB_REF="refs/heads/codex/beta-finite-adts", GITHUB_REPOSITORY="MGYamada/Qleisli")
            with patch.dict(maintenance.os.environ, environment), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                with patch.object(maintenance.size_policy, "hosted_context", return_value=context) as hosted:
                    self.assertEqual(maintenance.size_policy.main([]), 0)
                    hosted.assert_called_once()
                with patch.object(maintenance.fixture_policy, "hosted_context", return_value=context) as hosted, patch.object(maintenance.fixture_policy, "load_policy", return_value=({}, "policy-digest")), patch.object(maintenance.fixture_policy, "committed_totals", return_value={}), patch.object(maintenance.fixture_policy, "enforce", return_value=dict(status="allowed")):
                    self.assertEqual(maintenance.fixture_policy.main(["--hosted"]), 0)
                    hosted.assert_called_once()
                with patch.object(maintenance.reference_policy, "hosted_context", return_value=context) as hosted, patch.object(maintenance.reference_policy, "inspect", return_value=dict(status="allowed")):
                    self.assertEqual(maintenance.reference_policy.main(["--hosted"]), 0)
                    hosted.assert_called_once()
                # The old draft's local overrides must remain prohibited; the
                # producer never clears GITHUB_ACTIONS to evade these guards.
                for module in (maintenance.size_policy, maintenance.fixture_policy, maintenance.reference_policy):
                    self.assertEqual(module.main(["--base", maintenance.BASE, "--head", head]), 1)
                self.assertEqual(maintenance.os.environ["GITHUB_ACTIONS"], "true")

    def test_cumulative_inspection_is_additional_fixed_base_policy_without_exception(self):
        head = "a" * 40
        diff = dict(base=maintenance.BASE, head=head, merge_base=maintenance.BASE)
        with patch.object(maintenance, "git", return_value=(head+"\n").encode()), patch.object(maintenance.size_policy, "count_diff", return_value=diff) as counted, patch.object(maintenance.size_policy, "policy_result", return_value=dict(status="allowed")) as whole, patch.object(maintenance.fixture_policy, "load_policy", return_value=({}, "digest")), patch.object(maintenance.fixture_policy, "committed_totals", return_value={}), patch.object(maintenance.fixture_policy, "fixture_growth", return_value={}), patch.object(maintenance.fixture_policy, "enforce", return_value=dict(status="allowed")) as fixtures, patch.object(maintenance.reference_policy, "inspect", return_value=dict(status="allowed")) as references:
            maintenance.cumulative(head)
            counted.assert_called_once_with(maintenance.ROOT, maintenance.BASE, head)
            whole.assert_called_once_with(diff)
            self.assertEqual(len(fixtures.call_args.args), 3)
            references.assert_called_once_with(maintenance.ROOT, maintenance.BASE, head)
            whole.return_value = dict(status="forbidden")
            with self.assertRaises(ValueError):
                maintenance.cumulative(head)

    def test_actual_lean_version_requires_exact_pinned_version_line(self):
        maintenance.lean_version(b"Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit reviewed, Release)\n")
        for output in (b"Lean (version 4.30.01, x)\n", b"Lean (version 4.30.0-rc1, x)\n", b"prefix Lean (version 4.30.0, x)\n", b"Lean (version 4.30.0, x)\nextra\n"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                maintenance.lean_version(output)

    def test_fixed_output_mismatch_stderr_and_failed_status_are_refused(self):
        maintenance.actual_result(0, b"fixed\xff\n", b"", b"fixed\xff\n")
        for code, stdout, stderr in [(1, b"fixed", b""), (None, b"fixed", b""), (True, b"fixed", b""), (0, b"other", b""), (0, b"fixed", b"warning")]:
            with self.subTest(code=code, stdout=stdout, stderr=stderr), self.assertRaises(ValueError):
                maintenance.actual_result(code, stdout, stderr, b"fixed")

    def test_exact_head_does_not_accept_refs_or_mixed_commits(self):
        maintenance.exact_head("a" * 40, "a" * 40)
        for requested, observed in [("HEAD", "a" * 40), ("a" * 40, "b" * 40), ("a" * 39, "a" * 39)]:
            with self.assertRaises(ValueError):
                maintenance.exact_head(requested, observed)

    def test_hosted_context_refuses_unrelated_or_mixed_producers(self):
        commit = "a" * 40
        environment = dict(GITHUB_REPOSITORY="MGYamada/Qleisli", GITHUB_REF="refs/heads/codex/beta-finite-adts", GITHUB_SHA=commit, GITHUB_JOB="produce-review-artifact", GITHUB_EVENT_NAME="push", GITHUB_RUN_ID="1", GITHUB_RUN_ATTEMPT="1", GITHUB_WORKFLOW_REF="MGYamada/Qleisli/.github/workflows/current-proof-records.yml@refs/heads/codex/beta-finite-adts", GITHUB_WORKFLOW_SHA=commit)
        maintenance.hosted_context(commit, environment)
        for key, wrong in [("GITHUB_REPOSITORY", "other/repo"), ("GITHUB_REF", "refs/heads/main"), ("GITHUB_SHA", "b" * 40), ("GITHUB_JOB", "check-lean"), ("GITHUB_EVENT_NAME", "pull_request_target"), ("GITHUB_RUN_ID", "0"), ("GITHUB_RUN_ATTEMPT", "01"), ("GITHUB_WORKFLOW_SHA", "b" * 40)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                maintenance.hosted_context(commit, environment | {key: wrong})

    def test_only_fixed_four_records_may_change(self):
        before = {name: "original" for name in maintenance.ALLOWED}
        self.assertEqual(maintenance.unchanged(before, {name: "fresh" for name in before}, maintenance.ALLOWED), set(before))
        for forbidden in ("CONSTITUTION.md", "lean-kernel/Tests.lean", "governance/proposals/initial-guarantees.json", "tests/fixtures/constitution_v030/initial-guarantees/review-types.stdout.txt"):
            with self.subTest(path=forbidden), self.assertRaises(ValueError):
                maintenance.unchanged(before, before | {forbidden: "replacement"}, maintenance.ALLOWED)
        with self.assertRaises(ValueError):
            maintenance.unchanged({"source": "a"}, {"source": "b"}, maintenance.ALLOWED)

    def test_late_allowed_record_drift_and_failed_restoration_refuse_publication(self):
        planned = {name: b"exact planned bytes" for name in maintenance.ALLOWED}
        maintenance.exact_records(planned, planned)
        for name in maintenance.ALLOWED:
            with self.subTest(path=name), self.assertRaises(ValueError):
                maintenance.exact_records(planned, planned | {name: b"late replacement"})
        with self.assertRaises(ValueError):
            maintenance.unchanged({"source": "before"}, {"source": "after"}, set())

    def test_record_construction_keeps_historical_alpha_and_all_protected_fields(self):
        current = {
            "continuity": {"format": maintenance.continuity.RAW_FORMAT, "source_revision_sha256": "old", "transport": {"unchanged": True}},
            "binding_review": {"command": {"argv": ["fixed"], "seconds": 1}},
            "validation": {"observed_native_build": {"product_version": "0.3.0-alpha", "sha256": "historical"}, "source_revision": {}, "files": {}, "commands": [{"argv": ["review"], "seconds": 1}, {"argv": ["main"], "seconds": 1}], "scope": "historical scope", "axioms": ["propext", "Classical.choice", "Quot.sound"]},
        }
        ledger = {"current_bindings": [{"evidence": {"path": maintenance.CURRENT, "sha256": "old"}}], "discharged_guarantees": ["immutable"], "pending_obligations": ["QS", "PR", "RS"]}
        original_current, original_ledger = copy.deepcopy(current), copy.deepcopy(ledger)
        result = maintenance.proposed(current, ledger, {"sha256": "fresh"}, b"audit", b"schema", {label: {"seconds": 2} for label in ("review", "main", "binding")})
        self.assertEqual(set(result), {maintenance.AUDIT, maintenance.CURRENT, maintenance.LEDGER})
        fresh = maintenance.json.loads(result[maintenance.CURRENT])
        self.assertEqual(fresh["validation"]["observed_native_build"], current["validation"]["observed_native_build"])
        self.assertEqual(fresh["validation"]["axioms"], current["validation"]["axioms"])
        self.assertEqual(fresh["continuity"]["transport"], current["continuity"]["transport"])
        self.assertEqual(current, original_current)
        self.assertEqual(ledger, original_ledger)

    def test_new_output_directory_refuses_existing_inside_traversal_and_symlink(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            root = base / "source"
            root.mkdir()
            created = registry.command_output_directory(root, base / "fresh")
            self.assertTrue(created.is_dir())
            for invalid in (created, root / "inside", base / "fresh" / ".." / "escape"):
                with self.subTest(path=invalid), self.assertRaises(registry.RegistryError):
                    registry.command_output_directory(root, invalid)
            (base / "alias").symlink_to(root, target_is_directory=True)
            with self.assertRaises(registry.RegistryError):
                registry.command_output_directory(root, base / "alias" / "escape")

    def test_fixed_plan_includes_both_transports_original_binding_and_fresh_main(self):
        self.assertEqual([row[0] for row in maintenance.FIXED], ["review", "binding", "basis", "raw", "extract", "main"])
        self.assertEqual(maintenance.FIXED[-1][2], ["lake", "env", "leanchecker", "--fresh", "Main"])
        self.assertTrue(all("-M" not in arg and "-j" not in arg for row in maintenance.FIXED for arg in row[2]))

    def test_missing_failed_skipped_or_extra_fixed_stage_is_refused(self):
        results = {row[0]: {"exit_code": 0} for row in maintenance.FIXED}
        maintenance.complete_fixed_results(results)
        for label in results:
            with self.subTest(label=label), self.assertRaises(ValueError):
                maintenance.complete_fixed_results({key: value for key, value in results.items() if key != label})
            for status in (None, True, 1):
                with self.subTest(label=label, status=status), self.assertRaises(ValueError):
                    maintenance.complete_fixed_results(results | {label: {"exit_code": status}})
        with self.assertRaises(ValueError):
            maintenance.complete_fixed_results(results | {"unplanned": {"exit_code": 0}})


class MaintenanceLifecycleTests(unittest.TestCase):
    def lifecycle(self, fault=None):
        """Exercise actual main and file restoration with synthetic proof results."""
        import contextlib
        import gzip
        from unittest.mock import patch

        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            root, output = base / "source", base / "proof-records"
            root.mkdir()
            commit = "a" * 40
            current = {
                "continuity": {"format": maintenance.continuity.RAW_FORMAT, "source_revision_sha256": "old"},
                "binding_review": {"command": {"seconds": 1}},
                "validation": {
                    "observed_native_build": {"product_version": "0.3.0-alpha", "sha256": "historical"},
                    "source_revision": {}, "files": {}, "commands": [{"seconds": 1}, {"seconds": 1}],
                    "scope": "Ordinary source ADT execution, host-selected roots, constructors/match/qmatch and source-function preservation remain pending.",
                },
            }
            original = {
                maintenance.SCHEMA: b"original schema\n",
                maintenance.AUDIT: b"original audit\n",
                maintenance.CURRENT: maintenance.encoded(current),
                maintenance.LEDGER: maintenance.encoded({"current_bindings": [{"evidence": {"path": maintenance.CURRENT, "sha256": "old"}}], "discharged_guarantees": ["unchanged"]}),
            }
            tracked = set(original)
            fixed_outputs = {}
            for label, cwd, argv, reference in maintenance.FIXED:
                content = b"fixed " + label.encode() + b"\n"
                fixed_outputs[tuple(argv)] = content
                original[reference] = gzip.compress(content, mtime=0) if label == "extract" else content
                tracked.add(reference)
            for name, data in original.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            kernel = root / maintenance.KERNEL
            kernel.parent.mkdir(parents=True, exist_ok=True)
            kernel.write_bytes(b"synthetic checked kernel")
            revision = {"algorithm": "synthetic-test-only", "sha256": "fresh", "files": {}}
            seen, state = [], {"diff": False, "after_diff_inventory": 0}

            def fake_git(*args):
                if args == ("rev-parse", "HEAD"):
                    return (commit + "\n").encode()
                if args == ("rev-parse", "HEAD^{tree}"):
                    return ("b" * 40 + "\n").encode()
                if args == ("status", "--porcelain=v1", "-z"):
                    return b""
                if args == ("diff", "--binary", "--no-ext-diff", "--", *sorted(maintenance.ALLOWED)):
                    state["diff"] = True
                    return b"synthetic four-record patch\n"
                raise AssertionError("unplanned Git call: " + repr(args))

            def fake_inventory():
                if state["diff"]:
                    state["after_diff_inventory"] += 1
                    if fault == "restore" and state["after_diff_inventory"] == 2:
                        (root / maintenance.FIXED[0][3]).write_bytes(b"protected source changed during restoration")
                return {name: {"sha256": maintenance.sha((root / name).read_bytes()), "mode": (root / name).stat().st_mode & 0o777} for name in sorted(tracked)}

            def fake_registry(actual_root, write=False, report=None, command_output_dir=None):
                self.assertEqual(actual_root, root)
                self.assertTrue(write)
                command_output_dir.mkdir()
                report.update(status="passed", commands=[])
                for index in range(7):
                    directory = command_output_dir / f"{index:02d}"
                    directory.mkdir()
                    stdout = b"synthetic canonical stage " + str(index).encode()
                    (directory / "stdout").write_bytes(stdout)
                    (directory / "stderr").write_bytes(b"")
                    report["commands"].append({"stdout_sha256": maintenance.sha(stdout), "stderr_sha256": maintenance.sha(b"")})
                (root / maintenance.SCHEMA).write_bytes(b"fresh schema")

            def fake_execute(argv, cwd, stdout, stderr, limit):
                seen.append(tuple(argv))
                content = fixed_outputs.get(tuple(argv), b"synthetic stage\n")
                if argv == ["lake", "env", "lean", "--version"]:
                    self.assertEqual(limit, 60)
                    content = b"Lean (version 4.30.0, synthetic test)\n"
                if "scripts/check_schema_registry.py" in argv and "--write" in argv:
                    self.assertEqual(argv, [maintenance.sys.executable, "scripts/check_schema_registry.py", "--write", "--report", str(output / "registry-report.json"), "--command-output-dir", str(output / "registry-commands")])
                    self.assertEqual(cwd, root)
                    self.assertEqual(limit, 900)
                    audit = {}
                    fake_registry(root, write=True, report=audit, command_output_dir=output / "registry-commands")
                    (output / "registry-report.json").write_bytes(maintenance.encoded(audit))
                stdout.write(content)
                stderr.write(b"")
                if fault == "timeout" and argv[-1] == "Tests.lean":
                    self.assertEqual(limit, 900)
                    # Even a zero exit after the owned timeout is not success.
                    return 0, "timeout"
                if fault == "late-record" and "scripts/check_constitution.py" in argv:
                    (root / maintenance.CURRENT).write_bytes(b"late unvalidated current record")
                return 0, None

            environment = dict(GITHUB_ACTIONS="true", GITHUB_REPOSITORY="MGYamada/Qleisli", GITHUB_REF="refs/heads/codex/beta-finite-adts", GITHUB_SHA=commit, GITHUB_JOB="produce-review-artifact", GITHUB_EVENT_NAME="push", GITHUB_RUN_ID="1", GITHUB_RUN_ATTEMPT="1", GITHUB_WORKFLOW_REF="MGYamada/Qleisli/.github/workflows/current-proof-records.yml@refs/heads/codex/beta-finite-adts", GITHUB_WORKFLOW_SHA=commit)
            with contextlib.ExitStack() as stack:
                stack.enter_context(patch.object(maintenance, "ROOT", root))
                stack.enter_context(patch.object(maintenance, "git", side_effect=fake_git))
                stack.enter_context(patch.object(maintenance, "inventory", side_effect=fake_inventory))
                stack.enter_context(patch.object(maintenance, "cumulative", return_value={"status": "synthetic-preflight"}))
                stack.enter_context(patch.object(maintenance.registry, "source_revision", return_value=revision))
                stack.enter_context(patch.object(maintenance.guarantees, "validate_audit_record"))
                stack.enter_context(patch.object(maintenance, "execute", side_effect=fake_execute))
                stack.enter_context(patch.dict(maintenance.os.environ, environment))
                stack.enter_context(patch.object(maintenance.sys, "argv", ["refresh_current_proof_records.py", "--source-commit", commit, "--output", str(output)]))
                if fault is None:
                    self.assertEqual(maintenance.main(), 0)
                else:
                    message = {"late-record": "planned four-record bytes changed", "restore": "source drift outside fixed record allowlist", "timeout": "fixed command timed out"}[fault]
                    with self.assertRaisesRegex(ValueError, message):
                        maintenance.main()

            for name in maintenance.ALLOWED:
                self.assertEqual((root / name).read_bytes(), original[name], name)
            report = maintenance.json.loads((output / "report.json").read_bytes())
            self.assertEqual(report["source_commit"], commit)
            self.assertEqual(seen[:3], [
                (maintenance.sys.executable, "scripts/check_pr_size.py"),
                (maintenance.sys.executable, "scripts/check_fixture_budget.py", "--hosted"),
                (maintenance.sys.executable, "scripts/check_fixture_references.py", "--hosted"),
            ])
            self.assertEqual(seen.count((maintenance.sys.executable, "scripts/check_schema_registry.py", "--write", "--report", str(output / "registry-report.json"), "--command-output-dir", str(output / "registry-commands"))), 1)
            for _label, _cwd, argv, _reference in maintenance.FIXED:
                self.assertEqual(seen.count(tuple(argv)), 0 if fault == "timeout" else 1)
            self.assertEqual(seen.count(("lake", "env", "lean", "-DwarningAsError=true", "Tests.lean")), 1)
            if fault == "timeout":
                self.assertEqual(report["commands"][-1]["stop_reason"], "timeout")
                self.assertEqual(report["commands"][-1]["timeout_seconds"], 900)
                self.assertEqual(report["commands"][-1]["exit_code"], 0)
                self.assertEqual(report["commands"][-1]["argv"][-1], "Tests.lean")
                self.assertFalse(state["diff"])
            if fault is None:
                self.assertEqual(report["status"], "passed")
                self.assertEqual((output / "current-records.patch").read_bytes(), b"synthetic four-record patch\n")
                self.assertEqual({path.relative_to(output / "proposed").as_posix() for path in (output / "proposed").rglob("*") if path.is_file()}, maintenance.ALLOWED)
                fresh = maintenance.json.loads((output / "proposed" / maintenance.CURRENT).read_bytes())
                self.assertEqual(fresh["validation"]["observed_native_build"], current["validation"]["observed_native_build"])
            else:
                self.assertEqual(report["status"], "failed")
                self.assertFalse((output / "proposed").exists())
                self.assertFalse((output / "current-records.patch").exists())

    def test_complete_synthetic_plan_restores_source_before_publishing(self):
        self.lifecycle()

    def test_late_allowed_record_drift_restores_originals_without_artifact(self):
        self.lifecycle("late-record")

    def test_restoration_verification_failure_leaves_no_publishable_payload(self):
        self.lifecycle("restore")

    def test_full_test_timeout_restores_originals_without_fixed_proofs_or_payload(self):
        self.lifecycle("timeout")


class HostedPreflightDispatchTests(unittest.TestCase):
    def test_hosted_cli_paths_refuse_all_local_base_head_overrides(self):
        import contextlib
        import io
        from unittest.mock import patch
        import check_pr_size as size
        import check_fixture_budget as budget
        import check_fixture_references as references

        for tool in (size, budget, references):
            with self.subTest(tool=tool.__name__), patch.dict(maintenance.os.environ, {"GITHUB_ACTIONS": "true"}), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(tool.main(["--base", "a" * 40, "--head", "b" * 40]), 1)

    def test_canonical_hosted_cli_dispatch_uses_actual_event_bound_context(self):
        import contextlib
        import io
        from unittest.mock import patch
        import check_pr_size as size
        import check_fixture_budget as budget
        import check_fixture_references as references

        with tempfile.TemporaryDirectory() as temporary:
            event = {"repository": {"full_name": "MGYamada/Qleisli"}, "before": "c" * 40}
            event_path = Path(temporary) / "event.json"
            event_path.write_bytes(maintenance.encoded(event))
            environment = dict(GITHUB_ACTIONS="true", GITHUB_EVENT_PATH=str(event_path), GITHUB_EVENT_NAME="push", GITHUB_SHA="b" * 40, GITHUB_REF="refs/heads/codex/beta-finite-adts", GITHUB_REPOSITORY="MGYamada/Qleisli")
            context = dict(status="not-applicable", event="push", checkout_sha="b" * 40, repository="MGYamada/Qleisli")
            with patch.dict(maintenance.os.environ, environment), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                with patch.object(size, "hosted_context", return_value=context) as checked:
                    self.assertEqual(size.main([]), 0)
                    checked.assert_called_once_with(size.ROOT, "push", event, "b" * 40, environment["GITHUB_REF"], environment["GITHUB_REPOSITORY"])
                with patch.object(budget, "hosted_context", return_value=context) as checked, patch.object(budget, "load_policy", return_value=({}, "synthetic-policy")), patch.object(budget, "committed_totals", return_value={}), patch.object(budget, "enforce", return_value={"status": "allowed", "failures": []}):
                    self.assertEqual(budget.main(["--hosted"]), 0)
                    checked.assert_called_once_with(budget.ROOT, "push", event, "b" * 40, environment["GITHUB_REF"], environment["GITHUB_REPOSITORY"])
                with patch.object(references, "hosted_context", return_value=context) as checked, patch.object(references, "inspect", return_value={"status": "allowed"}) as inspected:
                    self.assertEqual(references.main(["--hosted"]), 0)
                    checked.assert_called_once_with(references.ROOT, "push", event, "b" * 40, environment["GITHUB_REF"], environment["GITHUB_REPOSITORY"])
                    inspected.assert_called_once_with(references.ROOT, references.BASELINE, "b" * 40, "c" * 40)


if __name__ == "__main__":
    unittest.main()
