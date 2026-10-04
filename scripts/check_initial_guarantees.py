#!/usr/bin/env python3
"""Check historical scoped-QS meaning and its separately updated current evidence.

The approved proposal retains its historical candidate bytes; check_constitution
validates the separate human admission event. The default checks historical
evidence and current source identities only. It does not replay Lean,
authenticate human approval, review mathematical adequacy, or itself admit a
constitutional guarantee. --verify-lean also checks the recorded
type/axiom output against the already-built Lean environment; it does not build
or independently certify that environment. Run the normal builds/audits first.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import argparse
import hashlib
import io
import math
from pathlib import Path
import re
import subprocess
import sys
import tarfile

import check_schema_registry as registry
from check_constitution import ADOPTION_PATH, ADOPTION_SHA256, REVIEWED_PATH, REVIEWED_SHA256, require_fields
from check_ratification_packet import ROOT, SHA256, PacketError, checked_file, exact_keys, json_object, read_file


PROPOSAL_PATH = "governance/proposals/initial-guarantees.json"
PROPOSAL_SHA256 = "bf9eb89d9ebadd41f16f40c5896b824b0e04fe1655264e102fb179948fa06c02"
FIXTURE = "tests/fixtures/constitution_v030/initial-guarantees"
VALIDATION_PATH = f"{FIXTURE}/validation.json"
REVIEW_PATH = f"{FIXTURE}/Review.lean"
REVIEW_STDOUT = f"{FIXTURE}/review-types.stdout.txt"
REVIEW_STDERR = f"{FIXTURE}/review-types.stderr.txt"
REPLAY_STDOUT = f"{FIXTURE}/native-main-replay.stdout.txt"
REPLAY_STDERR = f"{FIXTURE}/native-main-replay.stderr.txt"
AUDIT_PATH = "tests/fixtures/constitution_v030/ownership-rename-registry.json"
CURRENT_AUDIT_PATH = "tests/fixtures/constitution_v030/current-guarantee-registry.json"
REGISTRY_PATH = "lean/schema-registry.json"
TOOLCHAIN = "leanprover/lean4:v4.30.0"
ARCHIVE_PATH = f"{FIXTURE}/reviewed-source.tar.gz"
ARCHIVE_SHA256 = "8cdfc71a2ca583a3c41a46717b847e6ba904ccffdbb57a768b360d0c88c9e6f3"
ARCHIVED_REGISTRY_PATH = f"{FIXTURE}/reviewed-registry.json"
ARCHIVED_REGISTRY_SHA256 = "ac39211f5a94a0b6b14a794d4bbedc614940cb2b82e4850983df7fc8830759ee"
SEMANTIC_PATH = "governance/guarantees/initial-2026-semantic-sources.json"
CURRENT_PATH = "governance/guarantees/current-evidence.json"
BINDING_SOURCE = f"{FIXTURE}/CurrentBinding.lean"
BINDING_STDOUT = f"{FIXTURE}/current-binding.stdout.txt"
BINDING_STDERR = f"{FIXTURE}/current-binding.stderr.txt"
BINDING_ARGV = ["lake", "env", "lean", "-DwarningAsError=true", f"../{BINDING_SOURCE}"]
BINDING_SOURCE_SHA256 = "2d68b0af55e30c9288f39d75fe31fbed08645553e8e0a1dc77f80ae3ecdebc46"
BINDING_STDOUT_SHA256 = "b9ed648c89e0f255b8251fb40dd8d6f11eb1e0ac5f1884edcf24ceb74835879a"
NATIVE_CHECK = "QleisliKernel.Protocol.Validity.check"
ACCEPTANCE = "QleisliKernel.Protocol.Validity.Acceptance"
NATIVE_SOURCE = "lean-kernel/Protocol/Validity.lean"
REVIEW_SHA256 = "01648635d815afd9b268e84f67e474f7d5258181b43239695d9fc4588f7cffc4"
REVIEW_OUTPUT_SHA256 = "7922e319d2d25bdcbe2e25dc2e7bcdde9d38a3cb0aeed279398fe51ee544ea2b"
REVIEW_ARGV = ["lake", "env", "lean", "-DwarningAsError=true", f"../{REVIEW_PATH}"]
REPLAY_ARGV = ["lake", "env", "leanchecker", "--fresh", "Main"]
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
ENTRIES = {
    "QS-QLV1-OWNERSHIP-2026-01": {
        "theorem": "QleisliKernel.Protocol.Validity.check_ownershipSafe",
        "theorem_source": NATIVE_SOURCE,
        "predicate": "QleisliKernel.Semantics.Ownership.OwnershipSafe",
        "predicate_source": "lean-kernel/QleisliKernel/Semantics/Ownership.lean",
    },
    "QS-QLV1-SCOPE-2026-01": {
        "theorem": "Qleisli.NativeValidity.check_scopeSafe",
        "theorem_source": "lean/Qleisli/NativeValidity.lean",
        "predicate": "QleisliKernel.Semantics.ClassicalScope.ScopeSafe",
        "predicate_source": "lean-kernel/QleisliKernel/Semantics/ClassicalScope.lean",
    },
}


def require(condition, message):
    if not condition:
        raise PacketError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def nonempty_text(value, label):
    require(type(value) is str and bool(value.strip()), f"{label}: expected nonempty text")


def sha256(value, label):
    require(type(value) is str and SHA256.fullmatch(value) is not None, f"{label}: expected SHA-256")


def duration(value, label):
    require(type(value) in {int, float} and math.isfinite(value) and value >= 0,
            f"{label}: expected finite nonnegative elapsed seconds")


def source_revision(root, recorded):
    exact_keys(recorded, {"algorithm", "sha256", "files"}, "source revision")
    require(recorded["algorithm"] == "sha256-sorted-path-and-content-map-v1", "unsupported source revision")
    require(type(recorded["files"]) is dict and bool(recorded["files"]), "missing source closure")
    # Check confinement before invoking the shared source-inventory algorithm.
    # Also cover newly added files, absent from the recorded closure.
    names = set(recorded["files"])
    for pattern in ("lean/Qleisli/**/*.lean", "lean-kernel/QleisliKernel/**/*.lean",
                    "lean-kernel/Protocol/**/*.lean", "lean-kernel/Cli/**/*.lean"):
        names.update(path.relative_to(root).as_posix() for path in root.glob(pattern))
    for name in names:
        data = read_file(root, name)
        if name in recorded["files"]:
            sha256(recorded["files"][name], f"source {name}")
            require(digest(data) == recorded["files"][name], f"stale source identity: {name}")
    current = registry.source_revision(root)
    require(current == recorded, "recorded source closure differs from the current source inventory")
    return current


def check_declaration(root, declaration, path, kind, reader=read_file):
    text = reader(root, path).decode("utf-8")
    namespace, name = declaration.rsplit(".", 1)
    require(re.search(r"^namespace " + re.escape(namespace) + r"\s*$", text, re.M) is not None,
            f"wrong namespace for {declaration}")
    require(re.search(r"^ *" + kind + r" " + re.escape(name) + r"(?:\s|\()", text, re.M) is not None,
            f"missing {kind} declaration {declaration} in {path}")


def validate_review(root, reader=read_file):
    checked_file(root, REVIEW_PATH, REVIEW_SHA256)
    output = checked_file(root, REVIEW_STDOUT, REVIEW_OUTPUT_SHA256).decode("utf-8")
    for declaration in (NATIVE_CHECK, ACCEPTANCE, NATIVE_CHECK + "_acceptance",
                        *(entry["theorem"] for entry in ENTRIES.values())):
        require(output.count(declaration + " :") == 1, f"review output lacks exact declaration {declaration}")
    for entry in ENTRIES.values():
        require(output.count("def " + entry["predicate"] + " :") == 1,
                f"review output lacks independent predicate {entry['predicate']}")
        check_declaration(root, entry["theorem"], entry["theorem_source"], "theorem", reader)
        check_declaration(root, entry["predicate"], entry["predicate_source"], "def", reader)
    check_declaration(root, NATIVE_CHECK, NATIVE_SOURCE, "def", reader)
    check_declaration(root, ACCEPTANCE, NATIVE_SOURCE, "structure", reader)
    expected_axioms = "[propext, Classical.choice.{u}, Quot.sound.{u}]"
    for declaration in (NATIVE_CHECK + "_acceptance", *(entry["theorem"] for entry in ENTRIES.values())):
        require(f"'{declaration}' depends on axioms: {expected_axioms}" in output,
                f"review output lacks recorded axiom set for {declaration}")
    for path in (REVIEW_STDERR, REPLAY_STDOUT, REPLAY_STDERR):
        require(read_file(root, path) == b"", f"unexpected recorded diagnostics: {path}")


def replay_review(root, argv=REVIEW_ARGV, stdout=REVIEW_STDOUT, stderr=REVIEW_STDERR):
    try:
        result = subprocess.run(argv, cwd=root / "lean", capture_output=True, check=False)
    except OSError as error:
        raise PacketError("cannot run Lean review; use the already-built project toolchain") from error
    require(result.returncode == 0, "Lean review failed: " + (result.stdout + result.stderr).decode(errors="replace")[:2000])
    require(result.stdout == read_file(root, stdout) and result.stderr == read_file(root, stderr),
            "current Lean type/axiom output differs from recorded review evidence")


def reference(path, declaration):
    return {"path": path, "declaration": declaration}


def dependency_refs(entry, scope):
    prefix = entry["predicate"].rsplit(".", 1)[0]
    names = ("Inserts", "Run", "Visible", "Phis") if scope else ("Inputs", "Run", "Returned", "Valid")
    result = [reference(entry["predicate_source"], f"{prefix}.{name}") for name in names]
    if not scope:
        result.append(reference("lean-kernel/QleisliKernel/Semantics/RawTrace.lean", "QleisliKernel.Semantics.RawTrace.step"))
    return result + [reference("lean-kernel/QleisliKernel/Semantics/Observation.lean", "QleisliKernel.Semantics.Observation.Program")]


def proof_refs(scope):
    if scope:
        return [reference("lean/Qleisli/NativeValidity.lean", "Qleisli.NativeValidity.check_sound"),
                reference("lean/Qleisli/QirfValidity.lean", "Qleisli.Qirf.Validity.inspect_sound"),
                reference("lean/Qleisli/QirfValidity.lean", "Qleisli.Qirf.Validity.root_meaning"),
                reference("lean-kernel/QleisliKernel/Raw/ObservationScope.lean", "QleisliKernel.Raw.Observation.verify_scopeSafe")]
    return [reference(NATIVE_SOURCE, NATIVE_CHECK + "_acceptance"),
            reference("lean-kernel/QleisliKernel/Qirf/Ownership.lean", "QleisliKernel.Qirf.Validity.inspect_ownershipSafe"),
            reference("lean-kernel/QleisliKernel/Qirf/Ownership.lean", "QleisliKernel.Qirf.Validity.check_ownershipSafe"),
            reference("lean-kernel/QleisliKernel/Raw/ObservationOwnership.lean", "QleisliKernel.Raw.Observation.verify_ownershipSafe")]


def formal_statement(predicate):
    return ("∀ (bytes : ByteArray) (hasRequest : Bool) (work left : Nat),\n"
            f"  ({NATIVE_CHECK} bytes).run work = (.ok hasRequest, left) →\n"
            f"  ∃ binding : {ACCEPTANCE} bytes hasRequest work left,\n"
            "    ∃ program : QleisliKernel.Semantics.Observation.Program,\n"
            "      binding.artifact.programs[binding.artifact.root]? = some program ∧\n"
            f"      {predicate} program")


def validate_proposal(root, proposal, reader=read_file):
    exact_keys(proposal, {"format", "version", "edition", "status", "human_adoption", "authority", "interpretation",
                          "source_binding", "native_boundary", "guarantees", "assumptions_and_limits", "evidence",
                          "decision_requested"}, "guarantee proposal")
    require_fields({key: proposal[key] for key in ("format", "version", "edition", "status", "human_adoption")},
                   dict(format="qleisli.guarantee-proposal", version=1, edition="2026", status="proposed", human_adoption=None),
                   "guarantee proposal; human adoption cannot be fabricated")
    for field in ("authority", "decision_requested"):
        nonempty_text(proposal[field], field)
    require_fields(proposal["interpretation"], dict(id="QS-2026-01",
                   adoption=dict(path=ADOPTION_PATH, sha256=ADOPTION_SHA256),
                   reviewed_text=dict(path=REVIEWED_PATH, sha256=REVIEWED_SHA256)), "parent interpretation")
    checked_file(root, ADOPTION_PATH, ADOPTION_SHA256)
    checked_file(root, REVIEWED_PATH, REVIEWED_SHA256)
    binding = proposal["source_binding"]
    exact_keys(binding, {"registry_path", "algorithm", "sha256", "lean_toolchain", "meaning"}, "source binding")
    require_fields({key: binding[key] for key in ("registry_path", "algorithm", "lean_toolchain")},
                   dict(registry_path=REGISTRY_PATH, algorithm="sha256-sorted-path-and-content-map-v1", lean_toolchain=TOOLCHAIN),
                   "source binding")
    sha256(binding["sha256"], "source binding")
    nonempty_text(binding["meaning"], "source binding meaning")

    boundary = proposal["native_boundary"]
    exact_keys(boundary, {"entrypoint", "acceptance_witness", "acceptance_theorem", "cli", "cli_condition",
                          "quantification", "binding", "bounded_fragment"}, "native boundary")
    for field, expected in (("entrypoint", reference(NATIVE_SOURCE, NATIVE_CHECK)),
                            ("acceptance_witness", reference(NATIVE_SOURCE, ACCEPTANCE)),
                            ("acceptance_theorem", reference(NATIVE_SOURCE, NATIVE_CHECK + "_acceptance")),
                            ("cli", reference("lean-kernel/Cli/Validity.lean", "QleisliKernel.Cli.runValidity"))):
        require_fields(boundary[field], expected, f"native boundary {field}")
    for field in ("cli_condition", "quantification", "binding", "bounded_fragment"):
        nonempty_text(boundary[field], f"native boundary {field}")

    guarantees = proposal["guarantees"]
    require(type(guarantees) is list and len(guarantees) == 2, "require exactly the two proposed scoped guarantees")
    seen = set()
    for row in guarantees:
        exact_keys(row, {"id", "title", "jurisdiction", "interpretation", "status", "theorem", "property",
                         "formal_statement", "property_definition", "scope", "interface", "covered_properties",
                         "semantic_dependencies", "proof_chain"}, "proposed guarantee")
        identifier = row["id"]
        require(type(identifier) is str and identifier in ENTRIES and identifier not in seen,
                "unknown or duplicate proposed guarantee identifier")
        seen.add(identifier)
        entry = ENTRIES[identifier]
        require_fields({key: row[key] for key in ("jurisdiction", "interpretation", "status")},
                       dict(jurisdiction="QS", interpretation="QS-2026-01", status="proposed"), identifier)
        require_fields(row["theorem"], reference(entry["theorem_source"], entry["theorem"]), f"{identifier} theorem")
        require_fields(row["property"], reference(entry["predicate_source"], entry["predicate"]), f"{identifier} independent property")
        require(row["formal_statement"] == formal_statement(entry["predicate"]), f"{identifier}: actual checker/root/predicate statement changed")
        for field in ("title", "property_definition", "scope", "interface"):
            nonempty_text(row[field], f"{identifier} {field}")
        require(type(row["covered_properties"]) is list and bool(row["covered_properties"]), f"{identifier}: missing covered properties")
        for text in row["covered_properties"]:
            nonempty_text(text, f"{identifier} covered property")
        scope = identifier == "QS-QLV1-SCOPE-2026-01"
        for field, expected in (("semantic_dependencies", dependency_refs(entry, scope)), ("proof_chain", proof_refs(scope))):
            require(row[field] == expected, f"{identifier}: missing or substituted {field}")
            for ref in expected:
                check_declaration(root, ref["declaration"], ref["path"], "(?:def|structure|inductive|theorem|abbrev)", reader)

    limits = proposal["assumptions_and_limits"]
    exact_keys(limits, {"formal_logic", "independent_properties", "wire_and_native_correspondence", "host_correspondence",
                       "excluded_claims", "pending_obligations", "continuity"}, "assumptions and limits")
    for field in ("formal_logic", "independent_properties", "wire_and_native_correspondence", "host_correspondence", "continuity"):
        nonempty_text(limits[field], field)
    require(limits["pending_obligations"] == ["QS-2026-01", "PR-2026-01", "RS-2026-01"], "broader adopted obligations must remain pending")
    require(limits["excluded_claims"] == [
        "ordinary-root quantum EffectSound or CPTP semantics",
        "exact phase or requested algorithm correctness beyond the two stated structural predicates",
        "clean-workspace or dirty-workspace semantic discharge",
        "full source type/tuple/basis or source-preservation theorem", "runtime or exported-target correctness",
        "hierarchical or native-contract acceptance coverage", "Physical Realizability (PR)",
        "quantitative Resource Safety (RS)", "full QS-2026-01 discharge or production-wide constitutional certification"],
        "scope exclusions must remain explicit")
    evidence = proposal["evidence"]
    exact_keys(evidence, {"review_source", "printed_declarations", "review_stderr", "validation_record", "role"}, "proposal evidence")
    for field, path, expected_sha in (("review_source", REVIEW_PATH, REVIEW_SHA256),
                                     ("printed_declarations", REVIEW_STDOUT, REVIEW_OUTPUT_SHA256),
                                     ("review_stderr", REVIEW_STDERR, digest(b""))):
        require_fields(evidence[field], dict(path=path, sha256=expected_sha), f"proposal evidence {field}")
    exact_keys(evidence["validation_record"], {"path", "sha256"}, "validation record binding")
    require(evidence["validation_record"]["path"] == VALIDATION_PATH, "unexpected validation record path")
    nonempty_text(evidence["role"], "evidence role")


def validate_audit_record(data, revision, manifest_sha):
    record = json_object(data, "build/audit record")
    exact_keys(record, {"format", "version", "mode", "status", "commands", "source_revision", "manifest_sha256", "entries",
                        "externally_enabled"}, "build/audit record")
    require_fields({key: value for key, value in record.items() if key != "commands"},
                   dict(format="qleisli.schema-registry-validation", version=1, mode="rebuilt-types-and-audits", status="passed",
                        source_revision=revision["sha256"], manifest_sha256=manifest_sha, entries=3, externally_enabled=0), "build/audit record")
    expected = [("Qleisli", None), ("lean-kernel", ["lake", "build"]),
                ("lean-kernel", ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"]),
                ("lean", ["lake", "build"]), ("lean", ["lake", "env", "lean", "-DwarningAsError=true", "Audit.lean"]),
                ("lean-kernel", ["lake", "env", "leanchecker", "--fresh", "QleisliKernel"]),
                ("lean", ["lake", "env", "lean", "-DwarningAsError=true", "SchemaExport.lean"])]
    commands = record["commands"]
    require(type(commands) is list and len(commands) == len(expected), "incomplete recorded builds/audits")
    for command, (cwd, argv) in zip(commands, expected):
        exact_keys(command, {"argv", "cwd", "exit_code", "seconds", "stdout_sha256", "stderr_sha256", "diagnostics"}, "recorded audit command")
        if argv is None:
            require(type(command["argv"]) is list and len(command["argv"]) == 2
                    and type(command["argv"][0]) is str and bool(command["argv"][0])
                    and command["argv"][1] == "scripts/check_lean_kernel.py", "missing recorded Lean source-policy check")
            argv = command["argv"]
        require_fields({key: command[key] for key in ("argv", "cwd", "exit_code")},
                       dict(argv=argv, cwd=cwd, exit_code=0), "recorded audit command")
        duration(command["seconds"], "recorded audit command")
        for field in ("stdout_sha256", "stderr_sha256"):
            sha256(command[field], field)
        require(type(command["diagnostics"]) is str, "invalid recorded audit diagnostics")


def validate_evidence(root, proposal, *, record=None, archive=None):
    current_record = record is not None
    if record is None:
        evidence = proposal["evidence"]["validation_record"]
        record = json_object(checked_file(root, VALIDATION_PATH, evidence["sha256"]), "guarantee evidence")
    exact_keys(record, {"format", "version", "status", "edition", "lean_toolchain", "source_revision", "files", "commands",
                       "build_and_audit_record", "axioms", "scope", "native_binary_note", "observed_native_build"}, "guarantee evidence")
    audit_path = record["build_and_audit_record"]
    require(audit_path in ({AUDIT_PATH, CURRENT_AUDIT_PATH} if current_record else {AUDIT_PATH}), "unexpected build/audit record path")
    fixed = dict(format="qleisli.initial-guarantee-evidence", version=1,
                 status="checked-current-evidence" if current_record else "checked-candidate-evidence", edition="2026",
                 lean_toolchain=TOOLCHAIN, build_and_audit_record=audit_path, axioms=AXIOMS)
    require_fields({key: record[key] for key in fixed}, fixed, "guarantee evidence")
    for field in ("scope", "native_binary_note"):
        nonempty_text(record[field], field)
    observed = record["observed_native_build"]
    exact_keys(observed, {"path", "sha256", "product_version", "scope"}, "historical native build")
    require(observed["path"] == "lean-kernel/.lake/build/bin/qleisli-kernel"
            and observed["product_version"] == "0.3.0-alpha", "unexpected historical native build record")
    sha256(observed["sha256"], "historical native build")
    nonempty_text(observed["scope"], "historical native build scope")
    # The historical machine-specific executable is deliberately not a required
    # source artifact, nor does this check attest any currently selected binary.
    expected_files = {REVIEW_PATH, REGISTRY_PATH, audit_path, REVIEW_STDOUT, REVIEW_STDERR, REPLAY_STDOUT, REPLAY_STDERR}
    exact_keys(record["files"], expected_files, "evidence files")
    files = {name: checked_file(root, ARCHIVED_REGISTRY_PATH if archive is not None and name == REGISTRY_PATH else name, digest_)
             for name, digest_ in record["files"].items()}
    commands = record["commands"]
    require(type(commands) is list and len(commands) == 2, "require the two recorded Lean review/replay commands")
    for command, argv, cwd, stdout, stderr in zip(commands, (REVIEW_ARGV, REPLAY_ARGV), ("lean", "lean-kernel"),
                                                (REVIEW_STDOUT, REPLAY_STDOUT), (REVIEW_STDERR, REPLAY_STDERR)):
        exact_keys(command, {"argv", "cwd", "exit_code", "seconds", "stdout", "stderr"}, "recorded evidence command")
        require_fields({key: command[key] for key in ("argv", "cwd", "exit_code", "stdout", "stderr")},
                       dict(argv=argv, cwd=cwd, exit_code=0, stdout=stdout, stderr=stderr), "recorded evidence command")
        duration(command["seconds"], "recorded evidence command")
    if archive is None:
        revision = source_revision(root, record["source_revision"])
    else:
        revision = record["source_revision"]
        require(archive["revision"] == revision, "historical source archive differs from the reviewed source revision")
        require(proposal["source_binding"]["sha256"] == revision["sha256"], "proposal source binding is stale")
    manifest = json_object(files[REGISTRY_PATH], "schema registry")
    registry.verify_manifest(manifest, registry.manifest_export(manifest), revision)
    validate_audit_record(files[audit_path], revision, record["files"][REGISTRY_PATH])
    validate_review(root, read_file if archive is None else archive["reader"])
    return record


def historical_sources(root, proposal):
    record = json_object(checked_file(root, VALIDATION_PATH, proposal["evidence"]["validation_record"]["sha256"]), "historical evidence")
    revision = record["source_revision"]
    exact_keys(revision, {"algorithm", "sha256", "files"}, "historical source revision")
    require(revision["algorithm"] == "sha256-sorted-path-and-content-map-v1", "unknown historical source algorithm")
    require(type(revision["files"]) is dict and bool(revision["files"]), "missing historical source map")
    require(digest(registry.canonical(revision["files"])) == revision["sha256"], "invalid historical source map digest")
    data = checked_file(root, ARCHIVE_PATH, ARCHIVE_SHA256)
    sources = {}
    try:
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
            for member in archive:
                require(member.isfile() and member.name in revision["files"] and member.name not in sources
                        and 0 <= member.size <= 8 * 1024 * 1024, "unexpected/linked/duplicate historical source member")
                with archive.extractfile(member) as stream:
                    content = stream.read()
                require(digest(content) == revision["files"][member.name], f"historical source mismatch: {member.name}")
                sources[member.name] = content
    except (tarfile.TarError, OSError) as error:
        raise PacketError("cannot read historical source archive") from error
    require(set(sources) == set(revision["files"]), "historical source archive is incomplete")
    checked_file(root, ARCHIVED_REGISTRY_PATH, ARCHIVED_REGISTRY_SHA256)

    def reader(_root, name):
        require(name in sources, f"declaration source absent from historical archive: {name}")
        return sources[name]

    return {"revision": revision, "sources": sources, "reader": reader}


def expected_semantic_baseline(archive, proposal):
    roots = sorted({row["property"]["path"] for row in proposal["guarantees"]}
                   | {ref["path"] for row in proposal["guarantees"] for ref in row["semantic_dependencies"]}
                   | {"lean-kernel/QleisliKernel/Semantics/Qirf.lean"})
    pending, sources, external = list(roots), {}, set()
    while pending:
        path = pending.pop()
        if path in sources:
            continue
        data = archive["reader"](None, path)
        sources[path] = digest(data)
        for line in data.decode("utf-8").splitlines():
            if not line.startswith("import "):
                continue
            for module in line.removeprefix("import ").split():
                require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module) is not None,
                        "unsupported semantic import syntax; review the baseline generator")
                candidates = [f"{package}/{module.replace('.', '/')}.lean" for package in ("lean-kernel", "lean")]
                local = [name for name in candidates if name in archive["sources"]]
                require(len(local) <= 1, f"ambiguous semantic module {module}")
                if local:
                    pending.append(local[0])
                else:
                    external.add(module)
    return {"format": "qleisli.scoped-guarantee-semantic-baseline", "version": 1, "edition": "2026",
            "reviewed_proposal": {"path": PROPOSAL_PATH, "sha256": PROPOSAL_SHA256},
            "source_archive": {"path": ARCHIVE_PATH, "sha256": ARCHIVE_SHA256},
            "lean_toolchain": TOOLCHAIN, "roots": roots, "external_imports": sorted(external),
            "algorithm": "sha256-sorted-path-and-content-map-v1", "files": dict(sorted(sources.items())),
            "sha256": digest(registry.canonical(sources)),
            "binding_declarations": [{"path": NATIVE_SOURCE, "declaration": ACCEPTANCE,
                                      "source_sha256": digest(acceptance_declaration(archive["reader"](None, NATIVE_SOURCE)))}]}


def acceptance_declaration(data):
    """Conservative source guard, supplemented by elaborated field checks."""
    lines = data.decode("utf-8").splitlines(keepends=True)
    starts = [i for i, line in enumerate(lines) if re.match(r"^structure Acceptance\b", line)]
    require(len(starts) == 1, "require the one original Acceptance declaration")
    start = starts[0]
    end = start + 1
    while end < len(lines) and (not lines[end].strip() or lines[end][0].isspace()):
        end += 1
    return ("".join(lines[start:end]).rstrip() + "\n").encode("utf-8")


def validate_current(root, proposal, archive):
    current = json_object(read_file(root, CURRENT_PATH), "current guarantee evidence")
    exact_keys(current, {"format", "version", "edition", "reviewed_proposal", "semantic_baseline", "binding_review", "validation"}, "current guarantee evidence")
    require_fields({key: current[key] for key in ("format", "version", "edition", "reviewed_proposal")},
                   dict(format="qleisli.scoped-guarantee-current-evidence", version=1, edition="2026",
                        reviewed_proposal=dict(path=PROPOSAL_PATH, sha256=PROPOSAL_SHA256)), "current guarantee evidence")
    baseline = current["semantic_baseline"]
    exact_keys(baseline, {"path", "sha256"}, "semantic baseline binding")
    require(baseline["path"] == SEMANTIC_PATH, "unexpected semantic baseline path")
    data = checked_file(root, SEMANTIC_PATH, baseline["sha256"])
    expected = expected_semantic_baseline(archive, proposal)
    require(json_object(data, "semantic baseline") == expected, "semantic baseline differs from the admitted historical dependency closure")
    for name, sha in expected["files"].items():
        require(digest(read_file(root, name)) == sha,
                f"admitted semantic dependency changed: {name}; a checked current-artifact semantic transport is required and is not implemented by this schema")
    for declaration in expected["binding_declarations"]:
        require(digest(acceptance_declaration(read_file(root, declaration["path"]))) == declaration["source_sha256"],
                "admitted Acceptance binding fields changed; current-artifact semantic transport is required")
    for name in ("lean/lean-toolchain", "lean-kernel/lean-toolchain"):
        require(read_file(root, name).decode("utf-8").strip() == TOOLCHAIN,
                "the admitted semantic baseline requires the recorded Lean/Std toolchain; toolchain changes need reviewed transport support")
    binding_review = current["binding_review"]
    exact_keys(binding_review, {"source", "stdout", "stderr", "command"}, "elaborated binding review")
    for field, name, sha in (("source", BINDING_SOURCE, BINDING_SOURCE_SHA256),
                             ("stdout", BINDING_STDOUT, BINDING_STDOUT_SHA256),
                             ("stderr", BINDING_STDERR, digest(b""))):
        require_fields(binding_review[field], dict(path=name, sha256=sha), f"binding review {field}")
        checked_file(root, name, sha)
    command = binding_review["command"]
    exact_keys(command, {"argv", "cwd", "exit_code", "seconds", "stdout", "stderr"}, "binding review command")
    require_fields({key: command[key] for key in ("argv", "cwd", "exit_code", "stdout", "stderr")},
                   dict(argv=BINDING_ARGV, cwd="lean", exit_code=0, stdout=BINDING_STDOUT, stderr=BINDING_STDERR),
                   "binding review command")
    duration(command["seconds"], "binding review command")
    return validate_evidence(root, proposal, record=current["validation"])


def check(root=ROOT, *, verify_lean=False, require_adopted=False):
    root = Path(root)
    proposal = json_object(checked_file(root, PROPOSAL_PATH, PROPOSAL_SHA256), "historical guarantee proposal")
    archive = historical_sources(root, proposal)
    validate_proposal(root, proposal, archive["reader"])
    validate_evidence(root, proposal, archive=archive)
    record = validate_current(root, proposal, archive)
    if require_adopted:
        raise PacketError("this historical proposal checker cannot establish human admission; use check_constitution.py for the separately recorded event and live ledger")
    if verify_lean:
        replay_review(root)
        replay_review(root, BINDING_ARGV, BINDING_STDOUT, BINDING_STDERR)
        # Detect source/record changes while the external command was running.
        checked_file(root, PROPOSAL_PATH, PROPOSAL_SHA256)
        validate_current(root, proposal, archive)
    return {"mode": "current-Lean-review-output-and-source-identity" if verify_lean else "source-identity-only",
            "scoped_guarantees": 2, "admitted_by_this_check": 0, "source_revision": record["source_revision"]["sha256"]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--verify-lean", action="store_true", help="compare actual type/axiom output in the already-built Lean environment")
    parser.add_argument("--require-adopted", action="store_true", help="fail: use check_constitution.py to validate the separate human admission event")
    args = parser.parse_args(argv)
    try:
        result = check(args.root, verify_lean=args.verify_lean, require_adopted=args.require_adopted)
    except (PacketError, registry.RegistryError, OSError, UnicodeError, KeyError, TypeError, ValueError) as error:
        print(f"proposed guarantee evidence: {error}", file=sys.stderr)
        return 1
    print(f"Historical scoped-QS proposal and current evidence checked ({result['mode']}). "
          "This evidence check does not itself establish human authentication, adequacy, guarantee admission, "
          "broader QS/PR/RS discharge, or release approval.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
