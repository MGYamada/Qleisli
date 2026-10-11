"""Compare explicit syntax derivatives using the actual old/current parsers.

Only UTF-8 source spans are erased from the Debug representation. This bounded
AST comparison is migration evidence, not source preservation or quantum proof.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[5]
BASE = Path(__file__).resolve().parent
BEFORE = "73355382a3db94893982e5954e9400fffcd7f48e"
MODULES = ("ast", "lexer", "scanner", "parser", "documentation")
RUSTC = "/opt/homebrew/bin/rustc"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def parser_binary(directory, before):
    module_directory = directory / "frontend"
    module_directory.mkdir(parents=True)
    identities = {}
    for module in MODULES:
        relative = f"src/frontend/{module}.rs"
        original = (subprocess.check_output(["git", "show", f"{BEFORE}:{relative}"], cwd=ROOT)
                    if before else (ROOT / relative).read_bytes())
        identities[relative] = sha(original)
        selected = original
        if module == "documentation":
            # Keep the original documentation types and complete attach function.
            # The unrelated rendering functions depend on the effect checker;
            # neither parser's syntax/attachment path calls them.
            selected = original[:original.index(b"/// Render a parsed source file")]
        (module_directory / f"{module}.rs").write_bytes(selected)
    driver = ("#![allow(dead_code, unused_imports)]\nmod frontend {\n" +
              "".join(f"    pub mod {module};\n" for module in MODULES) +
              "}\nfn main() {\n"
              " let path=std::env::args().nth(1).expect(\"source path\");\n"
              " let source=std::fs::read_to_string(path).expect(\"read source\");\n"
              " match frontend::parser::parse_module(&source) {\n"
              "  Ok(module)=>println!(\"{:?}\",module),\n"
              "  Err(error)=>{eprintln!(\"{}\",error);std::process::exit(2);}\n"
              " }\n}\n")
    source = directory / "main.rs"
    source.write_text(driver)
    binary = directory / "parser-ast"
    command = [RUSTC, "--edition=2024", str(source), "-o", str(binary)]
    completed = subprocess.run(command, capture_output=True)
    assert completed.returncode == 0, completed.stderr.decode()
    return binary, {"source_hashes": identities, "driver_sha256": sha(driver.encode()),
                    "binary_sha256": sha(binary.read_bytes()), "compile_exit": completed.returncode,
                    "compile_stderr": completed.stderr.decode()}


def main():
    destination = BASE / "parser-ast-comparison-01.json"
    assert not destination.exists(), "Refusing to overwrite actual comparison"
    source_map_path = BASE.parent / "source-map.json"
    entries = json.loads(source_map_path.read_text())["files"]
    records = []
    with tempfile.TemporaryDirectory(prefix="qleisli-basis-parser-", dir="/private/tmp") as temporary:
        old, old_identity = parser_binary(Path(temporary) / "before", True)
        new, new_identity = parser_binary(Path(temporary) / "current", False)
        for entry in entries:
            for field, path_field in (("before_sha256", "before_path"),
                                     ("current_sha256", "current_path")):
                assert sha((ROOT / entry[path_field]).read_bytes()) == entry[field]
            before = subprocess.run([str(old), str(ROOT / entry["before_path"])], capture_output=True)
            current = subprocess.run([str(new), str(ROOT / entry["current_path"])], capture_output=True)
            before_ast = re.sub(rb"Span \{ start: [0-9]+, end: [0-9]+ \}", b"Span {}", before.stdout)
            current_ast = re.sub(rb"Span \{ start: [0-9]+, end: [0-9]+ \}", b"Span {}", current.stdout)
            record = dict(entry, before_exit=before.returncode, current_exit=current.returncode,
                          before_stderr=before.stderr.decode(), current_stderr=current.stderr.decode(),
                          before_ast_sha256=sha(before_ast), current_ast_sha256=sha(current_ast),
                          equal_except_spans=(before.returncode == current.returncode == 0 and
                                              before_ast == current_ast))
            records.append(record)
    result = {"format": "qleisli.coherent-basis-parser-comparison", "version": 1,
              "before_commit": BEFORE, "source_map_sha256": sha(source_map_path.read_bytes()),
              "driver_sha256": sha(Path(__file__).read_bytes()),
              "rustc_version": subprocess.check_output([RUSTC, "--version"], text=True).strip(),
              "before_parser": old_identity, "current_parser": new_identity,
              "normalization": "Erase only complete AST Span { start: integer, end: integer } values.",
              "files": records, "scope": "Bounded actual parser AST equality; no semantic, native, proof or release discharge."}
    destination.write_text(json.dumps(result, indent=2) + "\n")
    failed = [entry["before_path"] for entry in records if not entry["equal_except_spans"]]
    print(json.dumps({"files": len(records), "equal_except_spans": len(records) - len(failed),
                      "failed": failed, "record_sha256": sha(destination.read_bytes())}))
    assert not failed, failed


if __name__ == "__main__":
    main()
