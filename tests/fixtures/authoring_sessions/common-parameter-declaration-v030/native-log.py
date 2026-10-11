#!/usr/bin/env python3
"""Record native argv and delegate unchanged to the one selected checker.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import json
import os
import sys

NATIVE = "/Users/masa/git/Qleisli/lean-kernel/.lake/build/bin/qleisli-kernel"
with open(os.environ["QLEISLI_PARAMETER_NATIVE_LOG"], "a", encoding="utf-8") as stream:
    stream.write(json.dumps(sys.argv[1:]) + "\n")
os.execv(NATIVE, [NATIVE, *sys.argv[1:]])
