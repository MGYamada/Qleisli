#!/usr/bin/env python3
"""Prepare one untrusted n2 reversal-cancellation after real positive controls.
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
FIRST = DESIGN.parent / "native-valid-negatives-design-01"
SESSION = REPO / "tests/fixtures/authoring_sessions/qft-exact-request-v030"
PREPARED = SESSION / "native-valid-reversal-preparation-02"
CASE = "cancelled-actual-reversal-by-structural-composition"
LIMIT = 1 << 20
TABLES = ("definitions", "meanings", "encodings", "proofs")
FIRST_GENERATOR_SHA = "ea80dd386daf7a63a88f78b76934b641a70d7020c2f1cbec8a798d9f9492c58c"
REQUEST_SHA = "b0468aee9db0078a20fec5eff0502a071da9d696cbcbaa8f4cf4478c878f2233"
NATIVE_SHA = "39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    require(path.is_file() and path.stat().st_size <= LIMIT, "unbounded/non-file input")
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


def own_barrier(args):
    require(all(type(v) is str and len(v) == 64 and all(c in "0123456789abcdef" for c in v)
                for v in vars(args).values()), "explicit lowercase SHA-256 prerequisites required")
    path = DESIGN / "script-inputs.json"
    require(sha(read(path)) == args.reversal_design_map_sha256, "reviewed reversal script map changed")
    fixed = parse(read(path))
    require(fixed["format"] == "qleisli.unexecuted-reversal-script-inputs" and fixed["version"] == 1,
            "unexpected reversal input map")
    for row in fixed["files"]:
        item = (REPO / row["path"]).resolve()
        item.relative_to(REPO)
        require(item.stat().st_size == row["bytes"] and sha(read(item)) == row["sha256"]
                and item.stat().st_mode & 0o777 == row["mode"], "reviewed reversal input changed: " + row["path"])


def load(args):
    # Only reviewed fixed paths select imports; data maps never select commands.
    own_barrier(args)
    source = FIRST / "generate_negatives.py"
    require(sha(read(source)) == FIRST_GENERATOR_SHA, "first reviewed guard module changed")
    spec = importlib.util.spec_from_file_location("qft_reversal_first_guards", source)
    require(spec is not None and spec.loader is not None, "cannot load first reviewed guards")
    first = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(first)
    canon, old = first.load(args)
    return first, canon, old


def barrier(args, first, canon, old):
    own_barrier(args)
    # Retains original packets, complete declared FIRST identities/inventories,
    # fixed binaries and the real canonical n2 raw inspect/request successes.
    base, association = first.barrier(args, canon, old)
    first.targets(base, association, canon)
    return base, association


def construct(base, association, first, canon):
    """Fixed data construction only; neither typing nor evidence acceptance."""
    di, mi, pi = canon.graph(base)
    dc, mc, pc = canon.sequence(base, di, mi, pi)
    require(len(dc) == 6, "canonical root cardinality changed")
    post = tuple(association["added_indices"]["post_DMP"])
    prefix = tuple(association["added_indices"]["prefix_DMP"])
    require(post == (dc[-1], mc[-1], pc[-1]), "last post binding changed")
    require((dc[1], mc[1], pc[1]) == tuple(association["added_indices"]["retained_child1_DMP"])
            == (24, 24, 24), "original qft body moved")
    for children, name in ((dc, "D"), (mc, "M"), (pc, "P")):
        require(children[2:-1] == association["added_indices"]["retained_suffix_" + name],
                "old suffix association changed")
    composed = tuple(association["added_indices"]["composed_enter_DMP"])
    require(composed == (dc[0], mc[0], pc[0]), "enter binding changed")
    enter_d, enter_m, enter_p = canon.sequence(base, *composed)
    require(len(enter_d) == 2 and prefix == (enter_d[0], enter_m[0], enter_p[0]),
            "actual prefix association changed")
    reversal = (dc[3], mc[3], pc[3])
    rd, rm, rp = canon.sequence(base, *reversal)
    require(len(rd) == 3, "old real reversal cardinality changed")
    operations = ({"tag": "take_bit", "width": 2, "position": 0},
                  {"tag": "put_bit", "width": 2, "position": 1})
    for ordinal, operation in enumerate(operations):
        require(base["definitions"][rd[ordinal]]["body"]
                == base["meanings"][rm[ordinal]]["body"]
                == {"tag": "structural", "operation": operation}, "actual take/put reversal changed")
        require(base["proofs"][rp[ordinal]]["rule"] == {"tag": "structural"},
                "take/put premise rule changed")
    route = {"tag": "rewire", "permutation": {"owners": [0], "axes": [0, 1], "classical": []}}
    require(base["definitions"][rd[2]]["body"] == base["meanings"][rm[2]]["body"] == route,
            "actual reversal final label route changed")
    before = canon.side(120, [1, 0], 2)
    canonical = canon.side(0, [0, 1], 2)
    original = canon.side(101, [0, 1], 2)
    require(base["definitions"][post[0]]["interface"] == canon.header(before, canonical)
            and base["definitions"][prefix[0]]["interface"] == canon.header(canonical, original)
            and base["definitions"][reversal[0]]["interface"] == canon.header(original, original),
            "complete typed boundary route changed")
    for triple in (post, prefix):
        d, m, p = (base[t][i] for t, i in zip(("definitions", "meanings", "proofs"), triple))
        require(d["body"] == m["body"] == route and p["rule"] == {"tag": "rewire"}
                and p["premises"] == [] and p["witness"] == canon.WITNESS,
                "existing legal boundary route association changed")
    # Independently resolve each exact encoding from actual associated proofs.
    post_p = base["proofs"][post[2]]
    prefix_p = base["proofs"][prefix[2]]
    reversal_p = base["proofs"][reversal[2]]
    ei, ec, eo = post_p["input_encoding"], post_p["output_encoding"], prefix_p["output_encoding"]
    require(prefix_p["input_encoding"] == ec
            and reversal_p["input_encoding"] == reversal_p["output_encoding"] == eo,
            "existing proof endpoints do not compose")
    for index, side in ((ei, before), (ec, canonical), (eo, original)):
        canon.identity_encoding(base, index, side)
    value = copy.deepcopy(base)
    returning = canon.append(value, original, canonical, route, route, "rewire", [], eo, ec)
    additional = canon.append(value, before, canonical,
        {"tag": "sequence", "children": [post[0], prefix[0], reversal[0], returning[0]]},
        {"tag": "sequence", "children": [post[1], prefix[1], reversal[1], returning[1]]},
        "sequence", [post[2], prefix[2], reversal[2], returning[2]], ei, ec)
    value["definitions"][di]["body"]["children"][-1] = additional[0]
    value["meanings"][mi]["body"]["children"][-1] = additional[1]
    value["proofs"][pi]["premises"][-1] = additional[2]
    require(value["encodings"] == base["encodings"] and value["entry"] == base["entry"],
            "entry/encoding changed")
    allowed = [["definitions", di, "body", "children", len(dc) - 1],
               ["meanings", mi, "body", "children", len(mc) - 1],
               ["proofs", pi, "premises", len(pc) - 1]]
    retained = {key: value[key][:len(base[key])] if key in TABLES else value[key] for key in base}
    changes = first.diffs(base, retained)
    require(sorted(changes, key=str) == sorted(allowed, key=str), "unexpected old row delta")
    require(all(len(value[t]) == len(base[t]) + (0 if t == "encodings" else 2) for t in TABLES),
            "unexpected appended table cardinality")
    require(canon.graph(value) == (di, mi, pi), "entry/reachability graph changed")
    final_dc, final_mc, final_pc = canon.sequence(value, di, mi, pi)
    canon.sequence(value, *additional)
    require((final_dc[1], final_mc[1], final_pc[1]) == (dc[1], mc[1], pc[1]),
            "original shell body no longer at position1")
    finite, rows = [], []
    for table in TABLES:
        for index, prior in enumerate(base[table]):
            current = value[table][index]
            rows.append({"table": table, "index": index, "changed": current != prior,
                         "before_sha256": canon.row_digest(prior), "after_sha256": canon.row_digest(current)})
            key = "program" if table == "definitions" else "description" if table == "meanings" else None
            if key and key in prior["body"]:
                raw = prior["body"][key].encode()
                require(raw == current["body"][key].encode(), "finite bytes changed")
                finite.append({"table": table, "index": index, "field": key, "bytes": len(raw), "sha256": sha(raw)})
    encoded = (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()
    require(len(encoded) <= LIMIT, "proposal exceeded 1 MiB")
    delta = {"case": CASE, "width": 2, "status": "untrusted-prepared-not-native-checked",
        "positive_payload_sha256": sha(read(first.POSITIVE / "n2.proposal.json")),
        "mutant_payload_sha256": sha(encoded), "frozen_request_sha256": REQUEST_SHA,
        "entry": value["entry"], "root_DMP": [di, mi, pi], "post_DMP": list(post),
        "prefix_DMP": list(prefix), "reused_actual_reversal_DMP": list(reversal),
        "added_return_DMP": list(returning), "added_post_sequence_DMP": list(additional),
        "encodings_input_canonical_original": [ei, ec, eo], "changed_original_field_paths": changes,
        "original_row_digests": rows, "retained_finite_strings": finite,
        "table_lengths_before": {t: len(base[t]) for t in TABLES},
        "table_lengths_after": {t: len(value[t]) for t in TABLES},
        "expected_fresh_inspect": "success-required-before-request",
        "expected_frozen_request": "reject-contract", "expected_suffix_coordinates": [0, 1],
        "native_checked": False, "source_meaning_verified": False,
        "scope": "Local graph/delta checks only; actual bounded gates, source preservation and Fourier proof remain separate."}
    return encoded, delta


def arguments(parser):
    for name in ("client", "negative-design-map", "canonical-design-map", "canonical-prepared-map",
                 "positive-inspect-result", "positive-request-result", "reversal-design-map"):
        parser.add_argument("--" + name + "-sha256", required=True)


def main():
    require(sys.version_info >= (3, 11), "Python 3.11 or newer required")
    parser = argparse.ArgumentParser(description=__doc__)
    arguments(parser)
    args = parser.parse_args()
    first, canon, old = load(args)
    base, association = barrier(args, first, canon, old)
    PREPARED.mkdir()  # One shot; no old/partial result may be replaced.
    old.write_json(PREPARED / "started.json", {"recorded_utc": old.timestamp(), "reviewed_prerequisites": vars(args),
        "case": CASE, "width": 2, "status": "untrusted-generation-started"})
    try:
        encoded, delta = construct(base, association, first, canon)
        with (PREPARED / (CASE + ".proposal.json")).open("xb") as stream:
            stream.write(encoded)
        old.write_json(PREPARED / (CASE + ".delta.json"), delta)
        barrier(args, first, canon, old)
        old.write_json(PREPARED / "summary.json", {"recorded_utc": old.timestamp(), "case": CASE,
            "status": "one-untrusted-n2-structural-reversal-prepared", "native_checker_invoked_by_generator": False,
            "independent_request_unchanged": True, "scope": "Generation completion only; fresh inspect/request required."})
        files = [{"path": p.name, "bytes": p.stat().st_size, "sha256": old.digest(p), "mode": p.stat().st_mode & 0o777}
                 for p in sorted(PREPARED.iterdir()) if p.is_file()]
        old.write_json(PREPARED / "prepared-files.json", {"format": "qleisli.untrusted-reversal02-prepared-files",
            "version": 1, "reviewed_prerequisites": vars(args), "files": files,
            "scope": "Four generated data files only; no acceptance or source/general Fourier proof."})
    except BaseException as error:
        old.write_json(PREPARED / "aborted.json", {"recorded_utc": old.timestamp(), "error_type": type(error).__name__,
            "message": str(error), "note": "Partial data retained; no retry/input/expectation repair."})
        raise


if __name__ == "__main__":
    main()
