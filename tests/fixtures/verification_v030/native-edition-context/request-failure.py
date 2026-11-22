#!/usr/bin/env python3
# Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""Test-only checker replies bound to the bytes received from the host."""
import hashlib
import os
from pathlib import Path
import struct
import sys
import time


case = Path(sys.argv[0]).name
if case == "large-output":
    while True:
        sys.stdout.write("x" * 8192)
        sys.stdout.flush()
if case == "sleep":
    time.sleep(4)
    sys.exit(0)
if case == "inherited-pipe":
    if os.fork() == 0:
        time.sleep(4)
    sys.exit(0)
if case == "empty":
    sys.exit(0)
if sys.argv[1:] != ["--verify-request"]:
    sys.exit(2)
request = sys.stdin.buffer.read()
_, version_len, mode_len = struct.unpack_from("<3I", request, 4)
version = request[16:16 + version_len].decode()
mode_end = 16 + version_len + mode_len
mode = request[16 + version_len:mode_end].decode()
body = request[mode_end:]
print("qleisli.native-result 4")
print(hashlib.sha256(request).hexdigest())
if case == "failed-acceptance":
    print(f"accepted\n2026\n{version}\n{mode}\ninspection\n0\n0")
elif case == "contract" or body == b"complete\n":
    print("error\ncontract")
elif body == b"extra\n":
    print("error\ncontract\nextra")
elif body == b"missing-newline\n":
    print("error\ncontract", end="")
else:
    sys.exit(2)
sys.exit(1)
