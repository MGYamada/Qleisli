"""Capture explicitly supplied validation commands; never replay stored records."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time
ROOT = Path(__file__).resolve().parents[5]
BASE = Path(__file__).resolve().parent
name = sys.argv[1]
argv = sys.argv[2:]
assert argv and not (BASE / (name + ".json")).exists(), "Refusing to overwrite evidence"
env = dict(os.environ, CARGO_TARGET_DIR=os.environ.get("QLEISLI_VALIDATION_TARGET", "/private/tmp/qleisli-bounded-validation-target"), CARGO_INCREMENTAL="0", CARGO_PROFILE_DEV_DEBUG="0", CARGO_PROFILE_TEST_DEBUG="0", QLEISLI_KERNEL=str(ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"))
start = time.monotonic()
with (BASE / (name + ".stdout.txt")).open("wb") as out, (BASE / (name + ".stderr.txt")).open("wb") as err:
    result = subprocess.run(argv, cwd=ROOT, env=env, stdout=out, stderr=err)
record = {"argv": argv, "exit_code": result.returncode, "seconds": time.monotonic() - start, "cwd": str(ROOT), "environment": {k: env[k] for k in ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL", "CARGO_PROFILE_DEV_DEBUG", "CARGO_PROFILE_TEST_DEBUG", "QLEISLI_KERNEL")}, "streams": {kind: {"path": (BASE / (name + "." + kind + ".txt")).relative_to(ROOT).as_posix(), "sha256": hashlib.sha256((BASE / (name + "." + kind + ".txt")).read_bytes()).hexdigest()} for kind in ("stdout", "stderr")}}
(BASE / (name + ".json")).write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({k: record[k] for k in ("argv", "exit_code", "seconds")}), flush=True)
for kind in ("stdout", "stderr"):
    print(kind + ":\n" + (BASE / (name + "." + kind + ".txt")).read_text()[-2500:], flush=True)
sys.exit(result.returncode)
