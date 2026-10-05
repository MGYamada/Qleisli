#!/usr/bin/env python3
"""Prepare three untrusted width-two mutations after a real positive control.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
DESIGN = Path(__file__).resolve().parent
REPO = DESIGN.parents[4]
CANONICAL = DESIGN.parent / "canonical-label-design-01"
SESSION = REPO / "tests/fixtures/authoring_sessions/qft-exact-request-v030"
POSITIVE = SESSION / "canonical-label-preparation-01"
POSITIVE_CAPTURE = SESSION / "canonical-native-capture-01"
PREPARED = SESSION / "native-valid-negative-preparation-01"
LIMIT = 1 << 20
CASES = ("wrong-controlled-phase", "cancelled-real-reversal", "high-h-replaced-by-x")
TABLES = ("definitions", "meanings", "encodings", "proofs")
ORIGINAL_SHA = "daf3a59659d75ef19a543decb5061b2326b39bd2aff704e04a146470e5b89b70"
REQUEST_SHA = "b0468aee9db0078a20fec5eff0502a071da9d696cbcbaa8f4cf4478c878f2233"
CLIENT_SHA = "683b29749f752652b3ddb8dba7fac0ea2d832f848178963f3056d2f5c03d8294"
NATIVE_SHA = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def valid_sha(value):
    return type(value) is str and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def read(path):
    require(path.is_file() and path.stat().st_size <= LIMIT, "unbounded/non-file input: " + str(path))
    with path.open("rb") as stream:
        data = stream.read(LIMIT + 1)
    require(len(data) <= LIMIT, "input exceeded 1 MiB")
    return data


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    value = {}
    for key, item in items:
        require(key not in value, "duplicate JSON key")
        value[key] = item
    return value


def parse(data):
    return json.loads(data, object_pairs_hook=pairs,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError("non-JSON constant")))


def describe(path):
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": sha(read(path))}


def load(args):
    """Hash reviewed code before import; maps never select commands."""
    require(all(valid_sha(value) for value in vars(args).values()), "all explicit hashes must be lowercase SHA-256")
    own_map = DESIGN / "script-inputs.json"
    require(sha(read(own_map)) == args.negative_design_map_sha256, "reviewed negative script map changed")
    fixed = parse(read(own_map))
    require(fixed["format"] == "qleisli.unexecuted-negative-script-inputs" and fixed["version"] == 1,
            "unexpected negative script map")
    for row in fixed["files"]:
        path = (REPO / row["path"]).resolve()
        path.relative_to(REPO)
        require(path.stat().st_size == row["bytes"] and sha(read(path)) == row["sha256"]
                and path.stat().st_mode & 0o777 == row["mode"], "reviewed script input changed: " + row["path"])
    canonical_map = CANONICAL / "canonical-inputs.json"
    require(sha(read(canonical_map)) == args.canonical_design_map_sha256, "reviewed canonical map changed")
    canonical_fixed = parse(read(canonical_map))
    for row in canonical_fixed["files"]:
        path = (REPO / row["path"]).resolve()
        path.relative_to(REPO)
        require(path.stat().st_size == row["bytes"] and sha(read(path)) == row["sha256"]
                and path.stat().st_mode & 0o777 == row["mode"], "canonical reviewed input changed")
    spec = importlib.util.spec_from_file_location("qft_reviewed_canonical_generation", CANONICAL / "generate.py")
    require(spec is not None and spec.loader is not None, "cannot load reviewed canonical guards")
    canon = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(canon)
    old = canon.old_capture()
    return canon, old


def successful(event, folder, action, payload, old):
    """Require actual complete successful client/native records, not a summary."""
    if event.get("action") != action or event.get("width") != 2:
        return False, "action/width mismatch"
    expected = [str(old.CLIENT), action, str(old.FORWARDER), str(payload)]
    if action == "request":
        expected.append(str(SESSION / "requests/n2.json"))
    if event.get("argv") != expected or event.get("cwd") != str(REPO):
        return False, "fixed command mismatch"
    capture = event.get("client_capture", {})
    if not (capture.get("spawned") is True and capture.get("returncode") == 0
            and capture.get("reason") is None and capture.get("error") is None
            and capture.get("stdout_limited") is False and capture.get("stderr_limited") is False):
        return False, "client incomplete/operational failure"
    for label in ("stdout", "stderr"):
        if event.get("raw_" + label) != describe(folder / (label + ".bin")):
            return False, "client raw record mismatch"
    api = parse(read(folder / "stdout.bin"))
    if type(api) is not dict or event.get("api_record") != api or api.get("action") != action or api.get("status") != "ok":
        return False, "API not successful"
    if not (api.get("payload_bytes") == payload.stat().st_size
            and api.get("retained_payload_equal") is True and api.get("retained_request_equal") is True
            and api.get("request_bytes") == (1612 if action == "request" else None)):
        return False, "retained payload/request binding mismatch"
    if event.get("forwarder_attempts") != 1 or event.get("actual_native_calls") != 1:
        return False, "not exactly one observed native call"
    native_folder = folder / "native/call-01"
    if sorted(p.name for p in (folder / "native").iterdir()) != ["call-01"]:
        return False, "unexpected native attempt count"
    start = parse(read(native_folder / "process-started.json"))
    native = parse(read(native_folder / "result.json"))
    if type(start) is not dict or type(native) is not dict:
        return False, "native records are not objects"
    mode = "--hierarchy-pending" if action == "inspect" else "--hierarchy-fourier-pending"
    native_argv = [str(old.NATIVE), mode, "0.3.0-alpha"]
    if not (start.get("argv") == native_argv and start.get("native_sha256_before") == NATIVE_SHA
            and native.get("requested_native_argv") == native_argv
            and native.get("wrapper_argv") == [str(old.FORWARDER), mode, "0.3.0-alpha"]
            and native.get("ordinal") == 1 and native.get("actual_native_spawned") is True
            and native.get("actual_native_returncode") == 0 and native.get("wrapper_exit_code") == 0
            and "wrapper_rejection" not in native and native.get("stdin_limited_prefix") is False
            and native.get("native_sha256_before") == NATIVE_SHA and native.get("native_sha256_after") == NATIVE_SHA):
        return False, "native unsuccessful/identity mismatch"
    inner = native.get("capture", {})
    if not (inner.get("spawned") is True and inner.get("returncode") == 0
            and inner.get("reason") is None and inner.get("error") is None
            and inner.get("stdout_limited") is False and inner.get("stderr_limited") is False):
        return False, "native incomplete/operational failure"
    for label in ("stdin", "stdout", "stderr"):
        data = read(native_folder / (label + ".bin"))
        if native.get(label + "_bytes") != len(data) or native.get(label + "_sha256") != sha(data):
            return False, "native raw record mismatch"
    if inner.get("stdin_written") != native.get("stdin_bytes"):
        return False, "native stdin incomplete"
    if event.get("native_records") != [{"directory": str(native_folder), "process_started_record": True, "result": native}]:
        return False, "native event differs from actual record"
    if event.get("observed_stage") != "actual-native-process-observed":
        return False, "native observation stage mismatch"
    return True, "complete fresh success observed"


def barrier(args, canon, old):
    # The original guards retain source inventory, 233 FIRST identities,
    # original packet/helper hashes and both fixed binary file identities.
    canon.barrier(args.canonical_design_map_sha256, old)
    require(args.client_sha256 == CLIENT_SHA and old.digest(old.CLIENT) == CLIENT_SHA, "client identity changed")
    own_map = DESIGN / "script-inputs.json"
    require(sha(read(own_map)) == args.negative_design_map_sha256, "negative design map changed")
    for row in parse(read(own_map))["files"]:
        path = (REPO / row["path"]).resolve()
        path.relative_to(REPO)
        require(path.stat().st_size == row["bytes"] and sha(read(path)) == row["sha256"]
                and path.stat().st_mode & 0o777 == row["mode"], "negative design input changed")
    map_path = POSITIVE / "prepared-files.json"
    require(sha(read(map_path)) == args.canonical_prepared_map_sha256, "explicit reviewed canonical prepared map changed")
    fixed = parse(read(map_path))
    require(fixed["format"] == "qleisli.untrusted-canonical-label-prepared-files"
            and fixed["version"] == 1 and fixed["reviewed_design_map_sha256"] == args.canonical_design_map_sha256,
            "canonical prepared map/design mismatch")
    names = {"started.json", "summary.json"}
    names.update("n" + str(n) + "." + suffix for n in range(4) for suffix in ("proposal.json", "association.json"))
    require(len(fixed["files"]) == len(names) and {row["path"] for row in fixed["files"]} == names,
            "canonical prepared map must contain its exact ten files")
    for row in fixed["files"]:
        path = POSITIVE / row["path"]
        require(path.stat().st_size == row["bytes"] and sha(read(path)) == row["sha256"]
                and path.stat().st_mode & 0o777 == row["mode"], "canonical prepared file changed")
    payload = POSITIVE / "n2.proposal.json"
    association = parse(read(POSITIVE / "n2.association.json"))
    require(association["width"] == 2 and association["original_payload_sha256"] == ORIGINAL_SHA
            and association["adapted_payload_sha256"] == sha(read(payload)), "canonical n2 association binding changed")
    require(sha(read(SESSION / "requests/n2.json")) == REQUEST_SHA, "independent width-two request changed")
    for action, expected in (("inspect", args.positive_inspect_result_sha256), ("request", args.positive_request_result_sha256)):
        folder = POSITIVE_CAPTURE / ("n2-" + action)
        require(sha(read(folder / "result.json")) == expected, "explicit reviewed positive result changed")
        ok, reason = successful(parse(read(folder / "result.json")), folder, action, payload, old)
        require(ok, "canonical positive prerequisite failed: " + reason)
    return parse(read(payload)), association


def diffs(before, after, path=()):
    require(type(before) is type(after), "unexpected type-changing delta")
    if type(before) is dict:
        require(set(before) == set(after), "unexpected object field delta")
        return [p for key in before for p in diffs(before[key], after[key], (*path, key))]
    if type(before) is list:
        require(len(before) == len(after), "unexpected array cardinality delta")
        return [p for i in range(len(before)) for p in diffs(before[i], after[i], (*path, i))]
    return [] if before == after else [list(path)]


def targets(base, association, canon):
    di, mi, pi = canon.graph(base)
    require((di, mi, pi) == (association["root_definition"], association["root_meaning"], association["root_proof"]),
            "actual root differs from association")
    post = association["added_indices"]["post_DMP"]
    require(type(post) is list and len(post) == 3, "post-route typed cardinality mismatch")
    pd, pm, pp = (canon.index(i, len(base[t])) for i, t in zip(post, ("definitions", "meanings", "proofs")))
    dc, mc, pc = canon.sequence(base, di, mi, pi)
    require((dc[-1], mc[-1], pc[-1]) == (pd, pm, pp), "post-route does not bind exact last children")
    require([dc[1], mc[1], pc[1]] == association["added_indices"]["retained_child1_DMP"] == [24,24,24],
            "actual original recursive body moved")
    route = {"tag":"rewire","permutation":{"owners":[0],"axes":[0,1],"classical":[]}}
    require(base["definitions"][pd]["body"] == base["meanings"][pm]["body"] == route,
            "post-route is not the unchanged positional identity")
    p = base["proofs"][pp]
    require(p["implementation"] == pd and p["meaning"] == pm and p["rule"] == {"tag":"rewire"}
            and p["premises"] == [] and p["witness"] == canon.WITNESS, "post-route proof association differs")
    original = parse(read(SESSION / "first-emissions/n2.proposal.json"))
    require(sha(read(SESSION / "first-emissions/n2.proposal.json")) == ORIGINAL_SHA, "original n2 changed")
    for table in TABLES:
        for i, row in enumerate(original[table]):
            if table in ("definitions", "meanings", "proofs") and i == 31:
                continue
            require(base[table][i] == row, "canonical adapter changed an original nonroot row")
    require(base["definitions"][10]["body"] == {"j":1,"k":2,"tag":"dyadic_phase","target":123}
            and base["meanings"][10]["body"] == {"j":1,"k":2,"tag":"phase"}, "original phase changed")
    require(base["proofs"][10]["implementation"] == 10 and base["proofs"][10]["meaning"] == 10
            and base["proofs"][10]["rule"] == {"tag":"phase"}, "phase proof not bound")
    require(base["proofs"][3]["implementation"] == 3 and base["proofs"][3]["meaning"] == 3
            and base["proofs"][3]["rule"] == {"tag":"finite"}, "high finite leaf not bound")
    return pd, pm, pp


def expected_paths(case, post):
    pd, pm, _ = post
    if case == CASES[0]:
        return [["definitions",10,"body","j"],["meanings",10,"body","j"]]
    if case == CASES[1]:
        return [[t,i,"body","permutation","axes",j] for t,i in (("definitions",pd),("meanings",pm)) for j in (0,1)]
    if case == CASES[2]:
        return [["definitions",3,"body","program"],["meanings",3,"body","description"]]
    raise ValueError("unknown fixed case")


def mutant(base, case, post, canon):
    value = copy.deepcopy(base)
    pd, pm, _ = post
    if case == CASES[0]:
        value["definitions"][10]["body"]["j"] = 2
        value["meanings"][10]["body"]["j"] = 2
    elif case == CASES[1]:
        value["definitions"][pd]["body"]["permutation"]["axes"] = [1,0]
        value["meanings"][pm]["body"]["permutation"]["axes"] = [1,0]
    elif case == CASES[2]:
        source = base["definitions"][3]["body"]["program"]
        require(source.count('"gate":"h"') == 1, "embedded high H substring must occur once")
        changed = source.replace('"gate":"h"','"gate":"x"',1)
        require(diffs(parse(source),parse(changed)) == [["programs",0,"operations",0,"gate"]],
                "embedded QIRF changed beyond the actual gate")
        require(parse(source)["programs"][0]["operations"] == [{"gate":"h","input":125,"output":126,"tag":"gate"}],
                "high original gate/owner fields differ")
        value["definitions"][3]["body"]["program"] = changed
        description = base["meanings"][3]["body"]["description"]
        before = parse(description)
        require(description == json.dumps(before,separators=(",",":")) + "\n",
                "original description is not the frozen compact byte form")
        require(before["rows"] == before["cols"] == 2 and before["domain"] == "zeta8-dyadic-v1"
                and before["format"] == "qleisli.finite-matrix" and before["version"] == 1,
                "high finite description metadata differs")
        zero = [{"numerator":"0","denominator_bits":0} for _ in range(4)]
        one = [{"numerator":"1","denominator_bits":0}, *copy.deepcopy(zero[1:])]
        # X is authored independently as a row-major 2x2 permutation, not
        # extracted from the producer or used to define the frozen Fourier request.
        after = copy.deepcopy(before)
        after["entries"] = [copy.deepcopy(zero),copy.deepcopy(one),copy.deepcopy(one),copy.deepcopy(zero)]
        require({k:v for k,v in after.items() if k != "entries"} == {k:v for k,v in before.items() if k != "entries"},
                "finite description metadata changed")
        value["meanings"][3]["body"]["description"] = json.dumps(after,separators=(",",":")) + "\n"
    else:
        raise ValueError("unknown fixed case")
    actual = diffs(base,value)
    allowed = expected_paths(case,post)
    require(sorted(actual,key=str) == sorted(allowed,key=str), "mutation changed an unexpected field")
    require(value["proofs"] == base["proofs"] and value["encodings"] == base["encodings"], "P/E table changed")
    require(canon.graph(value) == canon.graph(base), "typed roots/reachability changed")
    encoded = (json.dumps(value,indent=2,ensure_ascii=False) + "\n").encode()
    require(len(encoded) <= LIMIT, "negative exceeds 1 MiB")
    finite = []
    for table, key in (("definitions","program"),("meanings","description")):
        for i,row in enumerate(base[table]):
            if key in row["body"]:
                original = row["body"][key].encode()
                current = value[table][i]["body"][key].encode()
                finite.append({"table":table,"index":i,"field":key,"changed":original != current,
                    "before_bytes":len(original),"after_bytes":len(current),"before_sha256":sha(original),"after_sha256":sha(current)})
    delta = {"case":case,"width":2,"status":"untrusted-negative-prepared-not-native-checked",
        "positive_payload_sha256":sha(read(POSITIVE / "n2.proposal.json")),"mutant_payload_sha256":sha(encoded),
        "frozen_request_sha256":REQUEST_SHA,"post_DMP_from_actual_association":list(post),
        "changed_field_paths":actual,"all_proofs_encodings_unchanged":True,"finite_strings":finite,
        "expected_fresh_inspect":"success-required-before-request","expected_frozen_request":"reject-contract",
        "source_meaning_verified":False,"native_checked":False,"claim_scope":"Local field/graph assertions only, not acceptance or a semantic proof."}
    return encoded, delta


def arguments(parser):
    for name in ("client", "negative-design-map", "canonical-design-map", "canonical-prepared-map",
                 "positive-inspect-result", "positive-request-result"):
        parser.add_argument("--" + name + "-sha256",required=True)


def main():
    require(sys.version_info >= (3,11), "Python 3.11 or newer required")
    parser = argparse.ArgumentParser(description=__doc__)
    arguments(parser)
    args = parser.parse_args()
    canon, old = load(args)
    base, association = barrier(args,canon,old)
    post = targets(base,association,canon)
    PREPARED.mkdir()  # One shot; no existing/partial attempt is replaced.
    old.write_json(PREPARED / "started.json",{"recorded_utc":old.timestamp(),"status":"untrusted-generation-started",
        "reviewed_prerequisites":vars(args),"width":2,"cases":list(CASES)})
    completed = []
    try:
        for case in CASES:
            base, association = barrier(args,canon,old)
            post = targets(base,association,canon)
            payload, delta = mutant(base,case,post,canon)
            with (PREPARED / (case + ".proposal.json")).open("xb") as stream:
                stream.write(payload)
            old.write_json(PREPARED / (case + ".delta.json"),delta)
            completed.append(case)
            barrier(args,canon,old)
        old.write_json(PREPARED / "summary.json",{"recorded_utc":old.timestamp(),"status":"three-untrusted-n2-negatives-prepared",
            "cases":completed,"native_checker_invoked_by_generator":False,"independent_request_unchanged":True,
            "source_meaning_verified":False,"scope":"Generation completion only; each later fresh inspection/request is still mandatory."})
        files = [{"path":p.name,"bytes":p.stat().st_size,"sha256":old.digest(p),"mode":p.stat().st_mode & 0o777}
                 for p in sorted(PREPARED.iterdir()) if p.is_file()]
        old.write_json(PREPARED / "prepared-files.json",{"format":"qleisli.untrusted-n2-negative-prepared-files","version":1,
            "reviewed_prerequisites":vars(args),"files":files,"scope":"Generated data identity only; no native acceptance/source proof."})
    except BaseException as error:
        old.write_json(PREPARED / "aborted.json",{"recorded_utc":old.timestamp(),"completed_cases":completed,
            "error_type":type(error).__name__,"message":str(error),"note":"Partial data retained; no retries or expectation repair."})
        raise


if __name__ == "__main__":
    main()
