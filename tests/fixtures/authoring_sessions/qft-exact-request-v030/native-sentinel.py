#!/usr/bin/env python3
"""Log an unexpected FIRST-emission native attempt and reject without forwarding.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""

import datetime
import json
from pathlib import Path
import sys


log = Path(__file__).resolve().parent / "first-emissions/native-attempts.jsonl"
with log.open("a", encoding="utf-8") as stream:
    stream.write(json.dumps({
        "argv": sys.argv,
        "cwd": str(Path.cwd()),
        "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "actual_native_checker_forwarded": False,
        "action": "unexpected-native-attempt-rejected",
    }) + "\n")
sys.stderr.write("FIRST emission forbids native checking; attempted call recorded and blocked.\n")
sys.exit(97)
