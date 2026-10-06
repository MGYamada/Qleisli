#!/usr/bin/env python3
"""Checked current-artifact continuity for the two admitted QLV1 scopes.

Source-only validation checks saved identities; it does not claim to execute
Lean. The live path runs a fixed extractor against the already-built/audited
current environment. The explicit Basis extension also requires a fixed typed
representation transport proof and unchanged independent meanings/subject types.
Historical proof bodies are not compared; the closed types
still refer directly to the actual current checker and original-byte witness.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""

import gzip
import hashlib
import io
from pathlib import Path
import subprocess

from check_constitution import require_fields
from check_ratification_packet import PacketError, checked_file, exact_keys, json_object, read_file

FIXTURE = "tests/fixtures/constitution_v030/initial-guarantees-continuity"
BASELINE_PATH = f"{FIXTURE}/baseline.json"
BASELINE_SHA256 = "b188c3290182fea743b35aa1e79c1a6815fbfcbfbe7223c063bd7395786c7ad0"
EXTRACTOR_PATH = f"{FIXTURE}/Extract.lean"
EXTRACTOR_SHA256 = "6668a374da66c2e6ead95da7da5a7b367cc847c8e8a966654ec46433704e9a77"
REVIEWED_PATH = f"{FIXTURE}/reviewed-expressions.json.gz"
CURRENT_PATH = f"{FIXTURE}/current-expressions.json.gz"
STDERR_PATH = f"{FIXTURE}/empty.stderr.txt"
ARGV = ["lake", "env", "lean", "-DwarningAsError=true", f"../{EXTRACTOR_PATH}"]
MAX_SNAPSHOT_BYTES = 16 * 1024 * 1024


def require(condition, message):
    if not condition:
        raise PacketError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def decompressed(data):
    try:
        with gzip.GzipFile(fileobj=io.BytesIO(data)) as stream:
            result = stream.read(MAX_SNAPSHOT_BYTES + 1)
    except (OSError, EOFError) as error:
        raise PacketError("invalid compressed continuity expressions") from error
    require(len(result) <= MAX_SNAPSHOT_BYTES, "continuity expressions exceed the reviewed capacity")
    return result


def baseline(root, archive):
    result = json_object(checked_file(root, BASELINE_PATH, BASELINE_SHA256), "continuity baseline")
    require(result["historical_source_revision_sha256"] == archive["revision"]["sha256"],
            "continuity baseline does not bind the admitted historical source archive")
    require_fields(result["extractor"], dict(path=EXTRACTOR_PATH, sha256=EXTRACTOR_SHA256), "fixed continuity extractor")
    checked_file(root, EXTRACTOR_PATH, EXTRACTOR_SHA256)
    require(result["expressions"]["path"] == REVIEWED_PATH, "unexpected historical expression snapshot")
    data = decompressed(checked_file(root, REVIEWED_PATH, result["expressions"]["sha256"]))
    require(digest(data) == result["expressions"]["uncompressed_sha256"], "corrupt historical expression snapshot")
    for name, sha in result["generation_evidence"].items():
        checked_file(root, name, sha)
    for name, sha in result["external_dependency_manifests"].items():
        require(archive["revision"]["files"][name] == sha, "wrong historical external dependency manifest")
        require(digest(read_file(root, name)) == sha,
                "external dependency manifest changed; this identity transport requires the admitted Lean/Std dependency basis")
    return result


def validate_identity(root, binding, revision, archive):
    """Validate recorded continuity evidence only; do not invoke Lean here."""
    exact_keys(binding, {"format", "version", "baseline", "extractor", "source_revision_sha256", "command", "stdout", "stderr"},
               "current continuity evidence")
    require_fields({key: binding[key] for key in ("format", "version", "baseline", "extractor")},
                   dict(format="qleisli.current-artifact-identity-transport", version=1,
                        baseline=dict(path=BASELINE_PATH, sha256=BASELINE_SHA256),
                        extractor=dict(path=EXTRACTOR_PATH, sha256=EXTRACTOR_SHA256)), "current continuity evidence")
    require(binding["source_revision_sha256"] == revision["sha256"],
            "stale continuity extraction: current source revision differs")
    expected = baseline(root, archive)
    require_fields(binding["stdout"], dict(path=CURRENT_PATH, compression="gzip", sha256=expected["expressions"]["sha256"],
                                          uncompressed_sha256=expected["expressions"]["uncompressed_sha256"]),
                   "current continuity expression identity")
    checked_file(root, CURRENT_PATH, binding["stdout"]["sha256"])
    require_fields(binding["stderr"], dict(path=STDERR_PATH, sha256=digest(b"")), "continuity stderr")
    checked_file(root, STDERR_PATH, digest(b""))
    require_fields(binding["command"], dict(argv=ARGV, cwd="lean", exit_code=0), "fixed continuity extraction command")
    return expected


# Fixed independent meanings and original-subject binding templates. A record
# cannot choose roots. This projection is only one prerequisite for checked
# representation transport; it does not replace the existing identity profile.
SEMANTIC_ROOTS = (
    "QleisliKernel.Semantics.Ownership.OwnershipSafe",
    "QleisliKernel.Semantics.ClassicalScope.ScopeSafe",
    "QleisliKernel.Semantics.Observation.Program",
)
BINDING_PREFIXES = (
    "QleisliKernel.Qirf.Artifact", "QleisliKernel.Qirf.Entry",
    "QleisliKernel.Qirf.Validity.Request", "QleisliKernel.Protocol.Validity.Acceptance",
)
ACTUAL_ENDPOINTS = (
    "QleisliKernel.Protocol.Validity.check",
    "QleisliKernel.Protocol.Validity.check_acceptance",
    "QleisliKernel.Protocol.Validity.check_ownershipSafe",
    "Qleisli.NativeValidity.check_scopeSafe",
)


def expression_name(value):
    require(type(value) is list and bool(value), "invalid elaborated name")
    tag = value[0]
    if tag == "anonymous":
        require(len(value) == 1, "invalid anonymous name")
        return ""
    require(tag in {"str", "num"} and len(value) == 3, "invalid elaborated name")
    require((tag == "str" and type(value[2]) is str)
            or (tag == "num" and type(value[2]) is int and value[2] >= 0),
            "invalid elaborated name component")
    parent = expression_name(value[1])
    return parent + ("." if parent else "") + str(value[2])


def expression_index(data):
    require(len(data) <= MAX_SNAPSHOT_BYTES, "continuity expressions exceed capacity")
    snapshot = json_object(data, "elaborated continuity expressions")
    exact_keys(snapshot, {"format", "version", "roots", "declarations"}, "elaborated snapshot")
    require_fields({key: snapshot[key] for key in ("format", "version")},
                   dict(format="qleisli.elaborated-continuity", version=1), "elaborated snapshot")
    require(type(snapshot["version"]) is int, "invalid snapshot version type")
    declarations = snapshot["declarations"]
    require(type(declarations) is list and len(declarations) <= 20000,
            "invalid continuity declaration inventory")
    result = {}
    for entry in declarations:
        exact_keys(entry, {"name", "module", "project", "declaration"}, "elaborated declaration")
        require(type(entry["project"]) is bool, "invalid project origin flag")
        expression_name(entry["module"])
        name = expression_name(entry["name"])
        require(name not in result, "duplicate elaborated declaration")
        result[name] = entry
    return snapshot["roots"], result


def expression_references(value, known):
    result = set()
    if type(value) is list:
        if value and type(value[0]) is str and value[0] in {"str", "num", "anonymous"}:
            name = expression_name(value)
            if name in known:
                result.add(name)
        for child in value:
            result.update(expression_references(child, known))
    elif type(value) is dict:
        for child in value.values():
            result.update(expression_references(child, known))
    return result


def compare_protected_projection(output, reviewed):
    """Check fixed meanings/templates only; NOT full continuity or proof replay.

    A transport caller must separately verify the immutable baseline, actual
    representation transport and freshly built success proofs. The v1 route
    below continues to require the entire historical expression identity.
    """
    old_roots, old = expression_index(reviewed)
    current_roots, current = expression_index(output)
    require(current_roots == old_roots, "changed continuity root selection")
    protected = set()
    pending = list(SEMANTIC_ROOTS)
    while pending:
        name = pending.pop()
        if name in protected:
            continue
        require(name in old, "missing historical independent meaning")
        protected.add(name)
        pending.extend(expression_references(old[name]["declaration"], old) - protected)
    semantic_count = len(protected)
    protected.update(ACTUAL_ENDPOINTS)
    protected.update(name for name in old if any(
        name == prefix or name.startswith(prefix + ".") for prefix in BINDING_PREFIXES))
    for name in sorted(protected):
        require(name in old and current.get(name) == old[name],
                "changed protected meaning or original-subject binding: " + name)
    return {"independent_meaning_declarations": semantic_count,
            "protected_declarations": len(protected)}


BASIS_FORMAT = "qleisli.current-artifact-basis-transport"
TRANSPORT_SOURCE = "lean/Qleisli/FiniteBasisTransport.lean"
TRANSPORT_SHA256 = "15759fd1b7ba69728b663b42523fb6d5b941deb36b2ccc79f47aad49386cf845"
TRANSPORT_REVIEW = f"{FIXTURE}/BasisTransportReview.lean"
TRANSPORT_REVIEW_SHA256 = "fa907a0e7f43c2d507cae261eac81c8c97705e10e96a22decfb8d4a742bed95f"
TRANSPORT_STDOUT = f"{FIXTURE}/basis-transport.stdout.txt"
TRANSPORT_STDOUT_SHA256 = "b9c89e48a5afbe82cde1fd1ae948331e9fe7ed405f5106308850e757d101d336"
TRANSPORT_ARGV = ["lake", "env", "lean", "-DwarningAsError=true", f"../{TRANSPORT_REVIEW}"]
QIRF_SEMANTICS = "lean-kernel/QleisliKernel/Semantics/Qirf.lean"
QIRF_SEMANTICS_SHA256 = "25b5b7ec131c13d3c4e517fcd1b8a76742d7edac9f626f3c81c9a9425907db86"


def validate(root, binding, revision, archive):
    # Default identity keeps the entire historical expression comparison.
    # This explicit profile additionally requires a fixed typed transport proof.
    require(type(binding) is dict, "invalid continuity evidence")
    if binding.get("format") != BASIS_FORMAT:
        return validate_identity(root, binding, revision, archive)
    exact_keys(binding, {"format", "version", "baseline", "extractor", "source_revision_sha256",
                         "command", "stdout", "stderr", "transport"}, "basis transport evidence")
    require(type(binding["version"]) is int and binding["version"] == 1,
            "unsupported basis transport version")
    require_fields(binding["baseline"], dict(path=BASELINE_PATH, sha256=BASELINE_SHA256), "immutable baseline")
    require_fields(binding["extractor"], dict(path=EXTRACTOR_PATH, sha256=EXTRACTOR_SHA256), "fixed extractor")
    require(binding["source_revision_sha256"] == revision["sha256"], "stale continuity extraction")
    expected = baseline(root, archive)
    exact_keys(binding["stdout"], {"path", "compression", "sha256", "uncompressed_sha256"}, "basis snapshot")
    require_fields({k: binding["stdout"][k] for k in ("path", "compression")},
                   dict(path=CURRENT_PATH, compression="gzip"), "basis snapshot")
    current = decompressed(checked_file(root, CURRENT_PATH, binding["stdout"]["sha256"]))
    require(digest(current) == binding["stdout"]["uncompressed_sha256"], "corrupt basis snapshot")
    reviewed = decompressed(checked_file(root, REVIEWED_PATH, expected["expressions"]["sha256"]))
    compare_protected_projection(current, reviewed)
    require_fields(binding["stderr"], dict(path=STDERR_PATH, sha256=digest(b"")), "continuity stderr")
    checked_file(root, STDERR_PATH, digest(b""))
    require(type(binding["command"]) is dict
            and type(binding["command"].get("exit_code")) is int,
            "invalid extraction exit code type")
    require_fields(binding["command"], dict(argv=ARGV, cwd="lean", exit_code=0), "fixed extraction command")
    require(type(binding["transport"]) is dict
            and type(binding["transport"].get("command")) is dict
            and type(binding["transport"]["command"].get("exit_code")) is int,
            "invalid transport exit code type")
    require_fields(binding["transport"], dict(
        source=dict(path=TRANSPORT_SOURCE, sha256=TRANSPORT_SHA256),
        review=dict(path=TRANSPORT_REVIEW, sha256=TRANSPORT_REVIEW_SHA256),
        stdout=dict(path=TRANSPORT_STDOUT, sha256=TRANSPORT_STDOUT_SHA256),
        stderr=dict(path=STDERR_PATH, sha256=digest(b"")),
        command=dict(argv=TRANSPORT_ARGV, cwd="lean", exit_code=0)), "fixed checked basis transport")
    for path, sha in ((TRANSPORT_SOURCE, TRANSPORT_SHA256), (TRANSPORT_REVIEW, TRANSPORT_REVIEW_SHA256),
                      (TRANSPORT_STDOUT, TRANSPORT_STDOUT_SHA256), (QIRF_SEMANTICS, QIRF_SEMANTICS_SHA256)):
        checked_file(root, path, sha)
    require(revision["files"].get(TRANSPORT_SOURCE) == TRANSPORT_SHA256,
            "transport proof missing from current source closure")
    return expected


def replay_transport(root):
    try:
        result = subprocess.run(TRANSPORT_ARGV, cwd=Path(root) / "lean", capture_output=True, check=False)
    except OSError as error:
        raise PacketError("cannot run fixed Lean basis transport review") from error
    require(result.returncode == 0, "Lean basis transport review failed: " +
            (result.stdout + result.stderr).decode(errors="replace")[:2000])
    require(result.stdout == checked_file(root, TRANSPORT_STDOUT, TRANSPORT_STDOUT_SHA256)
            and result.stderr == b"", "basis transport type/axiom evidence differs")


def compare_extraction(output, expected):
    require(len(output) <= MAX_SNAPSHOT_BYTES, "current continuity extraction exceeds the reviewed capacity")
    require(digest(output) == expected["expressions"]["uncompressed_sha256"],
            "current elaborated meaning, witness, or checker theorem type differs from the admitted identity baseline; "
            "representation-changing semantic transport is not implemented")


def replay(root, binding, revision, archive):
    """Replay fixed extraction and required transport after package build/audit."""
    expected = validate(root, binding, revision, archive)
    if binding.get("format") == BASIS_FORMAT:
        replay_transport(root)
    try:
        result = subprocess.run(ARGV, cwd=Path(root) / "lean", capture_output=True, check=False)
    except OSError as error:
        raise PacketError("cannot run continuity extraction in the already-built Lean environment") from error
    require(result.returncode == 0,
            "Lean continuity extraction failed: " + (result.stdout + result.stderr).decode(errors="replace")[:2000])
    require(result.stderr == b"", "unexpected Lean continuity extraction diagnostics")
    if binding.get("format") == BASIS_FORMAT:
        require(digest(result.stdout) == binding["stdout"]["uncompressed_sha256"],
                "fresh basis extraction differs from recorded evidence")
        reviewed = decompressed(checked_file(root, REVIEWED_PATH, expected["expressions"]["sha256"]))
        compare_protected_projection(result.stdout, reviewed)
        validate(root, binding, revision, archive)
    else:
        compare_extraction(result.stdout, expected)
