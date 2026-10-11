"""Untrusted host adapters to the Rust CLI and native Lean acceptance gate.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
from dataclasses import dataclass
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

__version__ = "0.3.0-alpha"
__all__ = ["Client", "Program", "QleisliError"]


class QleisliError(RuntimeError):
    def __init__(self, diagnostics, *, exit_code=1):
        self.diagnostics = diagnostics
        self.exit_code = exit_code
        super().__init__("; ".join(d["message"] for d in diagnostics))


def _error(code, message):
    return QleisliError([{"code": code, "severity": "error", "message": message,
                          "primary": None, "related": []}])


def _document(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate response field")
            result[key] = value
        return result

    def invalid_constant(value):
        raise ValueError("non-JSON response constant: " + value)

    def finite_number(value):
        number = float(value)
        if not math.isfinite(number):
            raise ValueError("response number exceeds finite host range")
        return number

    return json.loads(data, object_pairs_hook=unique, parse_constant=invalid_constant,
                      parse_float=finite_number)


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


def _finish_process(process):
    """Stop the owned POSIX session, including the checker's separate group.

    This contains ordinary descendants, not a program deliberately escaping
    its session. Windows retains direct-child cleanup pending a job-object API.
    """
    stopped = set()
    try:
        if os.name == "posix":
            deadline = time.monotonic() + 2
            while True:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise OSError("connection descendants did not stop")
                listing = subprocess.run(["ps", "-e", "-o", "pid=,stat="],
                    capture_output=True, text=True, check=True, timeout=remaining)
                members = []
                for line in listing.stdout.splitlines():
                    pid, state = line.split()
                    pid = int(pid)
                    try:
                        if os.getsid(pid) == process.pid:
                            members.append((pid, state))
                    except ProcessLookupError:
                        pass
                    except PermissionError:
                        # A process belonging to another user is not ours.
                        pass
                # communicate() may have reaped the leader. If that PID now
                # exists again, its session is new and must not be signalled.
                if process.returncode is not None and any(pid == process.pid for pid, _ in members):
                    break
                for pid, _ in members:
                    try:
                        if os.getsid(pid) == process.pid:
                            os.kill(pid, signal.SIGSTOP)
                            stopped.add(pid)
                    except ProcessLookupError:
                        pass
                # Re-scan after stopping every member. A child can start its
                # own group or fork before receiving STOP, but not after it.
                if all(state.startswith(("T", "Z")) for _, state in members):
                    break
    finally:
        for pid in stopped:
            try:
                if os.getsid(pid) == process.pid:
                    os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        process.kill()
        process.wait()


class Client:
    def __init__(self, executable=None, *, timeout=60, lean_kernel=None):
        self.executable = os.fspath(executable or os.environ.get("QLEISLI_BIN", "qleisli"))
        if not isinstance(timeout, (int, float)) or not math.isfinite(timeout) or timeout <= 0:
            raise ValueError("timeout must be finite and positive")
        self.timeout = timeout
        self.lean_kernel = None if lean_kernel is None else os.fsdecode(os.fspath(lean_kernel))
        if self.lean_kernel is not None and (not self.lean_kernel or "\0" in self.lean_kernel):
            raise ValueError("lean_kernel must be a nonempty executable path")

    def _process(self, args, data=None):
        try:
            with subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, start_new_session=os.name == "posix") as process:
                try:
                    stdout, stderr = process.communicate(data, timeout=self.timeout)
                    return subprocess.CompletedProcess(args, process.returncode, stdout, stderr)
                finally:
                    _finish_process(process)
        except subprocess.TimeoutExpired as e:
            raise _error("limit", "connection process timed out") from e
        except (OSError, subprocess.SubprocessError) as e:
            raise _error("connection", str(e)) from e

    def _call(self, action, format, *, data=None, path="-", shots=None, seed=None):
        args = [self.executable, "interop", action, os.fspath(path), f"--input={format}"]
        if self.lean_kernel is not None:
            args.append(f"--lean-kernel={self.lean_kernel}")
        if action == "sample":
            if type(shots) is not int or not 1 <= shots <= 1_000_000:
                raise ValueError("shots must be an integer in 1..1000000")
            if type(seed) is not int or not 0 <= seed <= 2**64 - 1:
                raise ValueError("seed must be an integer in 0..2**64-1")
            args.extend([f"--shots={shots}", f"--seed={seed}"])
        result = self._process(args, data)
        try:
            document = _document(result.stdout)
            if (document["format"] != "qleisli.result" or type(document["version"]) is not int
                    or document["version"] != 1
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
        except (ValueError, KeyError, TypeError, UnicodeError, RecursionError) as e:
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
        # Use this installation's reader, without adding the caller's cwd to
        # the child's import path. Keep the environment's optional PyQIR extra.
        result = self._process([sys.executable, "-P", str(Path(__file__).with_name("_qir.py").resolve())], data)
        try:
            document = _document(result.stdout)
            if result.returncode:
                raise _error(document["code"], document["message"])
            qasm = document["qasm"]
            if not isinstance(qasm, str):
                raise ValueError("invalid reader output")
        except (ValueError, KeyError, TypeError, UnicodeError, RecursionError) as e:
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
