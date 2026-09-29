"""JSON host CLI. Copyright 2026 Masahiko G. Yamada; Apache-2.0."""
import argparse
import json
from pathlib import Path
import sys
from . import Client, QleisliError, _error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("--input", dest="format", choices=["qasm", "qir", "qirf", "qli"], required=True)
    parser.add_argument("--action", choices=["check", "run", "sample", "emit-qasm", "emit-qir", "emit-ir"], default="check")
    parser.add_argument("--executable")
    parser.add_argument("--shots", type=int)
    parser.add_argument("--seed", type=int)
    args = parser.parse_args()
    if args.action == "sample":
        if args.shots is None or args.seed is None:
            parser.error("sample requires --shots and --seed")
    elif args.shots is not None or args.seed is not None:
        parser.error("--shots and --seed require sample")
    status = 0
    try:
        client = Client(args.executable)
        if args.format == "qli":
            program = client.compile_project(args.input)
        else:
            limit = 16 << 20 if args.format == "qirf" else 1 << 20
            with Path(args.input).open("rb") as stream:
                data = stream.read(limit + 1)
            if len(data) > limit:
                raise _error("limit", "input byte limit exceeded")
            program = {"qasm": client.from_openqasm, "qir": client.from_qir, "qirf": client.from_ir}[args.format](data)
        if args.action == "sample":
            result = program.sample(shots=args.shots, seed=args.seed)
        elif args.action.startswith("emit-"):
            text = {"emit-ir": lambda: program.artifact.decode("utf-8"),
                    "emit-qasm": program.to_openqasm, "emit-qir": program.to_qir}[args.action]()
            result = {"text": text}
        else:
            result = getattr(program, args.action)()
        diagnostics = []
    except (QleisliError, OSError, ValueError) as e:
        diagnostics = e.diagnostics if isinstance(e, QleisliError) else _error("host", str(e)).diagnostics
        status, result = 1, None
    print(json.dumps({"format": "qleisli.result", "version": 1, "command": f"interop {args.action}",
                      "outcome": "error" if status else "ok", "diagnostics": diagnostics, "result": result}))
    return status


if __name__ == "__main__":
    sys.exit(main())
