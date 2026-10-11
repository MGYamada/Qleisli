#!/usr/bin/env python3
"""Run Cargo with the repository MSRV compiler and matching subcommands.

Unlike `rustup run VERSION cargo clippy`, this also selects cargo-clippy,
clippy-driver, rustc and rustdoc ahead of unrelated PATH installations.
It never installs a toolchain. Pass ordinary Cargo arguments after this script.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import os
from pathlib import Path
import subprocess
import sys
import tomllib


def main():
    root = Path(__file__).resolve().parents[1]
    version = tomllib.loads((root / "Cargo.toml").read_text())["package"]["rust-version"]
    toolchain = version + ".0" if len(version.split(".")) == 2 else version
    found = subprocess.run(
        ["rustup", "which", "--toolchain", toolchain, "cargo"],
        check=True, text=True, capture_output=True,
    )
    cargo = Path(found.stdout.strip())
    binaries = cargo.parent
    suffix = cargo.suffix
    for name in ("cargo", "rustc", "rustdoc", "cargo-clippy", "clippy-driver"):
        if not (binaries / (name + suffix)).is_file():
            raise RuntimeError(f"missing MSRV executable: {name}; install it explicitly")
    environment = os.environ.copy()
    environment["PATH"] = str(binaries) + os.pathsep + environment.get("PATH", "")
    environment["CARGO"] = str(cargo)
    environment["RUSTC"] = str(binaries / ("rustc" + suffix))
    environment["RUSTDOC"] = str(binaries / ("rustdoc" + suffix))
    environment["RUSTUP_TOOLCHAIN"] = toolchain
    os.execve(str(cargo), [str(cargo), *sys.argv[1:]], environment)


if __name__ == "__main__":
    main()
