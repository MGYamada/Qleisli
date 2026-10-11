#!/usr/bin/env python3
"""Log native arguments and delegate unchanged to the fixed native checker."""
import json
import os
import sys

NATIVE = "/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel"
with open(os.environ["QLEISLI_PATTERN_NATIVE_LOG"], "a", encoding="utf-8") as stream:
    stream.write(json.dumps(sys.argv[1:]) + "\n")
os.execv(NATIVE, [NATIVE, *sys.argv[1:]])
