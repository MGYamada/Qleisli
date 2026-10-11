#!/usr/bin/env python3
"""Replay the frozen bounded scanner comparison, without building Qleisli.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import argparse
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys


HERE = Path(__file__).resolve().parent


def require_hash(data, expected, label):
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise ValueError(f"{label}: expected {expected}, found {actual}")


def generate(inputs):
    parts = [
        "#![allow(dead_code)]\nmod frontend {",
        r'''pub mod ast {
#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)] pub struct Span {pub start:usize,pub end:usize}
impl Span {pub fn new(start:usize,end:usize)->Self{Self{start,end}}}
}
pub mod documentation {
use super::ast::Span;
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub enum DocStyle { Inner, Outer }
#[derive(Clone,Debug,PartialEq,Eq)] pub struct DocComment {pub style:DocStyle,pub text:String,pub span:Span}
}''',
    ]
    for name, label in [
        ("scanner", "scanner-after"),
        ("old", "finite-before"),
        ("new", "finite-after"),
    ]:
        # Inner module docs cannot precede the generated wrapper imports.
        source = "\n".join(
            line for line in inputs[label].splitlines() if not line.startswith("//!")
        )
        parts.extend([f"pub mod {name} {{", source, "}"])
    for name, label in [("sized_old", "sized-before"), ("sized_new", "sized-after")]:
        source = inputs[label]
        section = source[source.index("fn tokens("):source.index("pub(super) fn parse(")]
        section = section.split("#[cfg(test)]")[0]
        parts.extend([
            f"pub mod {name} {{",
            r'''use super::ast::Span;
#[derive(Clone,Debug,PartialEq,Eq)] pub struct Token {text:String,span:Span}
#[derive(Clone,Debug,PartialEq,Eq)] pub struct Error {code:&'static str,span:Span,message:String}
impl Error {fn new(code:&'static str,span:Span,message:impl Into<String>)->Self {Self{code,span,message:message.into()}}}
type Result<T>=std::result::Result<T,Error>;
fn error(span:Span,message:impl Into<String>)->Error {Error::new("parse",span,message)}
''',
            section.replace("fn tokens(", "pub fn tokens(", 1),
            "}",
        ])
    parts.extend(["}", "\n" + (HERE / "cases.rs.txt").read_text()])
    return "\n".join(parts).encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--check-source-tree", type=Path,
        help="also bind snapshots to the baseline Git objects and current working sources",
    )
    args = parser.parse_args()
    if struct.calcsize("P") != 8:
        parser.error("the recorded Rust usize-based input sequence requires a 64-bit host")
    manifest = json.loads((HERE / "manifest.json").read_text())
    inputs = {}
    for item in manifest["inputs"]:
        data = (HERE / item["snapshot"]).read_bytes()
        require_hash(data, item["sha256"], item["snapshot"])
        inputs[item["label"]] = data.decode()
        if args.check_source_tree:
            if item["revision"] == manifest["baseline_commit"]:
                actual = subprocess.check_output(
                    ["git", "show", f'{item["revision"]}:{item["source"]}'],
                    cwd=args.check_source_tree,
                )
            else:
                actual = (args.check_source_tree / item["source"]).read_bytes()
            require_hash(actual, item["sha256"], item["source"])
    require_hash((HERE / "cases.rs.txt").read_bytes(), manifest["cases_sha256"], "cases")
    require_hash((HERE / "harness.rs").read_bytes(), manifest["harness_sha256"], "frozen harness")
    generated = generate(inputs)
    require_hash(generated, manifest["harness_sha256"], "regenerated harness")

    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source = out / "harness.rs"
    executable = out / "scanner-review"
    source.write_bytes(generated)
    commands = []

    def run(label, argv):
        completed = subprocess.run(argv, cwd=HERE, capture_output=True, timeout=60)
        (out / f"{label}.stdout.txt").write_bytes(completed.stdout)
        (out / f"{label}.stderr.txt").write_bytes(completed.stderr)
        commands.append({
            "argv": argv, "cwd": str(HERE), "exit_code": completed.returncode,
            "stdout": f"{label}.stdout.txt", "stderr": f"{label}.stderr.txt",
        })
        (out / "run.json").write_text(json.dumps({
            "baseline_commit": manifest["baseline_commit"],
            "harness_sha256": manifest["harness_sha256"],
            "source_tree_checked": str(args.check_source_tree) if args.check_source_tree else None,
            "python": sys.version, "commands": commands,
        }, indent=2) + "\n")
        if completed.returncode:
            sys.stderr.buffer.write(completed.stderr)
            raise SystemExit(completed.returncode)
        return completed.stdout

    run("rustc-version", ["rustc", "--version"])
    run("compile", ["rustc", "--edition=2024", "-O", str(source), "-o", str(executable)])
    sys.stdout.buffer.write(run("compare", [str(executable)]))


if __name__ == "__main__":
    main()
