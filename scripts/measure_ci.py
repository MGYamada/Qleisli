#!/usr/bin/env python3
"""Summarize GitHub run/jobs API snapshots without guessing cache or queue data.

Runner minutes are summed job wall time, not GitHub billing (OS multipliers and
rounding differ). Initial queue and feedback elapsed time are reported separately.
Only observed dependency-cache outputs may be labelled hits; Lean project build
caches are disabled, with fresh source/compiled audits and replay unchanged.
"""

import argparse
from datetime import datetime
import json
from pathlib import Path
import sys


def timestamp(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def summarize(run: dict, jobs: dict, validation: dict | None = None) -> dict:
    if run["status"] != "completed" or not isinstance(jobs.get("jobs"), list):
        raise ValueError("only complete observed runs can be measured")
    active = [job for job in jobs["jobs"] if job.get("conclusion") != "skipped" and job.get("started_at") and job.get("completed_at")]
    if not active or any(job.get("status") != "completed" for job in jobs["jobs"]):
        raise ValueError("incomplete job snapshot")
    # All-skipped jobs can have equal timestamps; retain them but charge zero time.
    first = min(timestamp(job["started_at"]) for job in active)
    last = max(timestamp(job["completed_at"]) for job in active)
    reference = run["created_at"] if run.get("run_attempt", 1) == 1 else run["run_started_at"]
    created = timestamp(reference)
    duration = sum((timestamp(job["completed_at"]) - timestamp(job["started_at"])).total_seconds() for job in active)
    result = dict(
        run_id=run["id"], attempt=run.get("run_attempt", 1), url=run["html_url"],
        event=run["event"], head_sha=run["head_sha"], conclusion=run["conclusion"],
        queue_reference=reference,
        initial_queue_seconds=(first - created).total_seconds(),
        feedback_seconds=(last - created).total_seconds(),
        execution_elapsed_seconds=(last - first).total_seconds(),
        runner_seconds=duration, runner_minutes=round(duration / 60, 3),
        cache_observation="unavailable", jobs=[],
    )
    for job in jobs["jobs"]:
        seconds = None
        if job["conclusion"] == "skipped":
            seconds = 0
        elif job.get("started_at") and job.get("completed_at"):
            seconds = (timestamp(job["completed_at"]) - timestamp(job["started_at"])).total_seconds()
            if seconds < 0:
                raise ValueError("inconsistent job timestamps")
        steps = []
        for step in job.get("steps", []):
            elapsed = None
            if step.get("conclusion") == "skipped":
                elapsed = 0
            elif step.get("started_at") and step.get("completed_at"):
                elapsed = (timestamp(step["completed_at"]) - timestamp(step["started_at"])).total_seconds()
                if elapsed < 0:
                    raise ValueError("inconsistent step timestamps")
            steps.append(dict(name=step["name"], conclusion=step.get("conclusion"), seconds=elapsed))
        result["jobs"].append(dict(name=job["name"], conclusion=job["conclusion"], runner_seconds=seconds, steps=steps))
    if validation:
        # PR run.head_sha is the author branch, while jobs validate GitHub's merge
        # commit. Retain both identities rather than claiming they are identical.
        needs = validation["needs"]
        outputs = needs["changes"]["outputs"]
        if outputs.get("head", validation["head"]) != validation["head"] or (
            run["event"] != "pull_request" and run["head_sha"] != validation["head"]
        ):
            raise ValueError("validation artifact is not bound to the observed run")
        result["validated_sha"] = validation["head"]
        result["profile"] = outputs["profile"]
        result["dependency_cache"] = {
            name: item.get("outputs", {}).get("dependency-cache", "unavailable")
            for name, item in needs.items() if name.startswith("check-") and name != "check-docs"
        }
        result["cache_observation"] = "observed required-check outputs; project build cache disabled"
    if any(value < 0 for value in [result["initial_queue_seconds"], result["feedback_seconds"], duration]):
        raise ValueError("inconsistent timestamps")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run", type=Path)
    parser.add_argument("jobs", type=Path)
    parser.add_argument("--validation", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = summarize(json.loads(args.run.read_text()), json.loads(args.jobs.read_text()),
                           json.loads(args.validation.read_text()) if args.validation else None)
        text = json.dumps(result, indent=2) + "\n"
        if args.output:
            args.output.write_text(text)
        else:
            print(text, end="")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as failure:
        print(f"CI measurement: {failure}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
