"""Bounded streaming capture for the fixed local client/native commands.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import os
import selectors
import signal
import subprocess
import time


def capture(argv, cwd, env, stdin, seconds, output_limit, on_spawn=None):
    """Return bounded raw prefixes and actual status; never invoke a shell."""
    begin = time.monotonic()
    try:
        process = subprocess.Popen(
            argv, cwd=cwd, env=env, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            start_new_session=True,
        )
    except OSError as error:
        return dict(spawned=False, returncode=None, stdout=b"", stderr=b"",
                    reason="spawn-error", error=str(error), seconds=time.monotonic()-begin,
                    stdin_written=0, stdout_limited=False, stderr_limited=False)
    streams = {"stdout": bytearray(), "stderr": bytearray()}
    limited = {"stdout": False, "stderr": False}
    reason, error, written = None, None, 0
    deadline = begin + seconds
    selector = selectors.DefaultSelector()

    def close(stream):
        try:
            selector.unregister(stream)
        except KeyError:
            pass
        stream.close()

    def kill():
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    try:
        if on_spawn is not None:
            on_spawn(process.pid)
        for stream, name in [(process.stdout, "stdout"), (process.stderr, "stderr")]:
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ, name)
        if stdin:
            os.set_blocking(process.stdin.fileno(), False)
            selector.register(process.stdin, selectors.EVENT_WRITE, "stdin")
        else:
            process.stdin.close()
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                if reason is None:
                    reason = "timeout"
                    kill()
                    deadline = time.monotonic() + 2
                else:
                    for key in list(selector.get_map().values()):
                        close(key.fileobj)
                    break
            for key, _ in selector.select(max(0, min(0.1, remaining))):
                stream, name = key.fileobj, key.data
                if name == "stdin":
                    try:
                        count = os.write(stream.fileno(), stdin[written:written+65536])
                    except BrokenPipeError:
                        close(stream)
                        continue
                    except BlockingIOError:
                        continue
                    written += count
                    if written == len(stdin):
                        close(stream)
                    continue
                try:
                    block = os.read(stream.fileno(), min(65536, output_limit-len(streams[name])+1))
                except BlockingIOError:
                    continue
                if not block:
                    close(stream)
                    continue
                available = output_limit-len(streams[name])
                streams[name].extend(block[:available])
                if len(block) > available:
                    limited[name] = True
                    if reason is None:
                        reason = "output-limit"
                        kill()
                        deadline = time.monotonic() + 2
        try:
            process.wait(timeout=max(0.01, deadline-time.monotonic()))
        except subprocess.TimeoutExpired:
            reason = reason or "timeout"
            kill()
            process.wait(timeout=2)
    except BaseException:
        kill()
        process.wait(timeout=2)
        raise
    finally:
        selector.close()
        for stream in (process.stdin, process.stdout, process.stderr):
            if not stream.closed:
                stream.close()
    return dict(spawned=True, returncode=process.returncode,
                stdout=bytes(streams["stdout"]), stderr=bytes(streams["stderr"]),
                reason=reason, error=error, seconds=time.monotonic()-begin,
                stdin_written=written, stdout_limited=limited["stdout"],
                stderr_limited=limited["stderr"])
