"""Untrusted host adapters to the Rust verifier; no Python proof authority.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
from dataclasses import dataclass
import json
import math
import os
from pathlib import Path
import subprocess
import sys

__version__ = "0.2.6"
__all__ = ["Client", "Program", "QleisliError"]


class QleisliError(RuntimeError):
    def __init__(self, diagnostics, *, exit_code=1):
        self.diagnostics = diagnostics
        self.exit_code = exit_code
        super().__init__("; ".join(d["message"] for d in diagnostics))


def _error(code, message):
    return QleisliError([{"code": code, "severity": "error", "message": message,
                          "primary": None, "related": []}])


def _bytes(value, limit):
    if not isinstance(value, (str, bytes)):
        raise TypeError("expected source text or bytes")
    # Bound strings before their worst-case UTF-8 allocation, then bound bytes.
    if len(value) > limit:
        raise _error("limit", "input byte limit exceeded")
    data = value.encode("utf-8") if isinstance(value, str) else value
    if len(data) > limit:
        raise _error("limit", "input byte limit exceeded")
    return data


class Client:
    def __init__(self, executable=None, *, timeout=60):
        self.executable = os.fspath(executable or os.environ.get("QLEISLI_BIN", "qleisli"))
        if not isinstance(timeout, (int, float)) or not math.isfinite(timeout) or timeout <= 0:
            raise ValueError("timeout must be finite and positive")
        self.timeout = timeout

    def _process(self, args, data=None):
        try:
            return subprocess.run(args, input=data, capture_output=True, timeout=self.timeout,
                                  check=False)
        except subprocess.TimeoutExpired as e:
            raise _error("limit", "connection process timed out") from e
        except OSError as e:
            raise _error("connection", str(e)) from e

    def _call(self, action, format, *, data=None, path="-", shots=None, seed=None):
        args = [self.executable, "interop", action, os.fspath(path), f"--input={format}"]
        if action == "sample":
            if type(shots) is not int or not 1 <= shots <= 1_000_000:
                raise ValueError("shots must be an integer in 1..1000000")
            if type(seed) is not int or not 0 <= seed <= 2**64 - 1:
                raise ValueError("seed must be an integer in 0..2**64-1")
            args.extend([f"--shots={shots}", f"--seed={seed}"])
        result = self._process(args, data)
        try:
            document = json.loads(result.stdout)
            if (document["format"] != "qleisli.result" or document["version"] != 1
                    or document["command"] != f"interop {action}"
                    or document["outcome"] != ("ok" if result.returncode == 0 else "error")
                    or not isinstance(document["diagnostics"], list)):
                raise ValueError("unexpected result envelope")
            if result.returncode:
                if not document["diagnostics"] or document["result"] is not None:
                    raise ValueError("inconsistent failure envelope")
                raise QleisliError(document["diagnostics"], exit_code=result.returncode)
            if document["diagnostics"] or not isinstance(document["result"], dict):
                raise ValueError("inconsistent success envelope")
            return document["result"]
        except (ValueError, KeyError, TypeError, UnicodeError) as e:
            raise _error("connection", "invalid Rust connection response") from e

    def from_openqasm(self, source):
        data = self._call("emit-ir", "qasm", data=_bytes(source, 1 << 20))["text"]
        return Program(self, data.encode("utf-8"))

    def from_ir(self, artifact):
        data = _bytes(artifact, 16 << 20)
        self._call("check", "qirf", data=data)
        return Program(self, data)

    def compile_project(self, path):
        data = self._call("emit-ir", "qli", path=Path(path).resolve())["text"]
        return Program(self, data.encode("utf-8"))

    def from_qir(self, source):
        data = _bytes(source, 1 << 20)
        result = self._process([sys.executable, "-m", "qleisli._qir"], data)
        try:
            document = json.loads(result.stdout)
            if result.returncode:
                raise _error(document["code"], document["message"])
            qasm = document["qasm"]
            if not isinstance(qasm, str):
                raise ValueError("invalid reader output")
        except (ValueError, KeyError, TypeError, UnicodeError) as e:
            raise _error("qir", "QIR reader failed or returned an invalid response") from e
        return self.from_openqasm(qasm)


@dataclass(frozen=True)
class Program:
    client: Client
    artifact: bytes

    def _call(self, action, **kwargs):
        return self.client._call(action, "qirf", data=_bytes(self.artifact, 16 << 20), **kwargs)

    def check(self):
        return self._call("check")

    def run(self):
        return self._call("run")

    def sample(self, *, shots, seed):
        return self._call("sample", shots=shots, seed=seed)

    def to_openqasm(self):
        return self._call("emit-qasm")["text"]

    def to_qir(self):
        return self._call("emit-qir")["text"]
