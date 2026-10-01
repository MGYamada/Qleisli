"""Measured queue/runner accounting must not become an invented benchmark."""

import copy
import sys
import unittest

sys.dont_write_bytecode = True
from measure_ci import summarize


class Measurements(unittest.TestCase):
    def setUp(self):
        self.run = dict(id=1, html_url="https://example.invalid/run", status="completed", event="pull_request",
                        head_sha="a" * 40, conclusion="success", created_at="2026-10-02T00:00:00Z")
        self.jobs = {"jobs": [
            dict(name="code", status="completed", conclusion="success", started_at="2026-10-02T00:00:10Z", completed_at="2026-10-02T00:01:10Z"),
            dict(name="proof", status="completed", conclusion="success", started_at="2026-10-02T00:00:20Z", completed_at="2026-10-02T00:02:20Z"),
        ]}

    def test_parallel_jobs_separate_queue_latency_and_runner_minutes(self):
        result = summarize(self.run, self.jobs)
        self.assertEqual(result["initial_queue_seconds"], 10)
        self.assertEqual(result["feedback_seconds"], 140)
        self.assertEqual(result["execution_elapsed_seconds"], 130)
        self.assertEqual(result["runner_minutes"], 3)
        self.assertEqual(result["cache_observation"], "unavailable")

    def test_skipped_and_cancelled_jobs_are_not_fabricated_successes(self):
        jobs = copy.deepcopy(self.jobs)
        jobs["jobs"] += [dict(name="skipped", status="completed", conclusion="skipped", started_at=None, completed_at=None)]
        result = summarize(self.run, jobs)
        self.assertEqual(result["jobs"][-1]["conclusion"], "skipped")
        self.assertEqual(result["runner_minutes"], 3)
        jobs["jobs"][0]["conclusion"] = "cancelled"
        self.assertEqual(summarize(self.run, jobs)["jobs"][0]["conclusion"], "cancelled")
        self.run["status"] = "in_progress"
        with self.assertRaises(ValueError):
            summarize(self.run, jobs)

    def test_pr_head_and_checked_merge_sha_are_distinct(self):
        report = dict(head="b" * 40, needs={
            "changes": {"outputs": {"profile": "full"}},
            "check-rust": {"outputs": {"dependency-cache": "true"}},
        })
        result = summarize(self.run, self.jobs, report)
        self.assertEqual(result["head_sha"], "a" * 40)
        self.assertEqual(result["validated_sha"], "b" * 40)
        self.assertEqual(result["dependency_cache"]["check-rust"], "true")

    def test_reruns_do_not_count_the_previous_attempt_or_manual_wait_as_queue(self):
        self.run["run_attempt"] = 2
        self.run["created_at"] = "2026-10-01T23:00:00Z"
        self.run["run_started_at"] = "2026-10-02T00:00:00Z"
        self.assertEqual(summarize(self.run, self.jobs)["initial_queue_seconds"], 10)
        self.assertEqual(summarize(self.run, self.jobs)["feedback_seconds"], 140)


if __name__ == "__main__":
    unittest.main()
