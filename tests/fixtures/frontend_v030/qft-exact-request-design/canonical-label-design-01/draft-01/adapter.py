"""Untrusted bounded label-only adapter for four exact retained packets.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import copy
import hashlib
import json

LIMIT = 1 << 20
TABLES = ("definitions", "meanings", "encodings", "proofs")
ORIGINAL_SHA256 = (
    "01e914469e7b8a02992e706476b425452962dc5f871a026ba6362e447852502a",
    "eee8e5ca2114e8ff9c7983ad502041a8bf232fd41b092c8dec005384eab09043",
    "daf3a59659d75ef19a543decb5061b2326b39bd2aff704e04a146470e5b89b70",
    "b5859d46ed14d3e9250350020fc11fca603ecf4b4372f490c1f40dff6ebcd768",
)
REQUEST_SHA256 = (
    "011aba8f38b9b668f0f45bd1fda0ef0a5a4db2c156c43f8a6f9d1cd7bde52971",
    "be2842f16dd8d2a17c06071392d1ad621aefb206eef6fccf7a4e0f885a91a72d",
    "b0468aee9db0078a20fec5eff0502a071da9d696cbcbaa8f4cf4478c878f2233",
    "4d407efd1dd4d0c621440310ccaa0f67c0af8db69da0fafc5a0517a9c60b015d",
)
COUNTS = ((1, 1, 1, 1), (15, 15, 7, 15), (32, 32, 13, 32), (52, 52, 22, 52))
OUTPUT_OWNERS = (101, 105, 120, 134)
WITNESS = {"template_version": 1, "parameters": [], "references": []}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(value, names):
    require(type(value) is dict and set(value) == set(names), "unexpected object fields")


def index(value, size):
    require(type(value) is int and 0 <= value < size, "invalid typed table index")
    return value


def side(owner, axes, width):
    return {"quantum": [{"owner": owner, "axes": list(axes),
                         "basis": [{"tag": "bits", "width": width}]}], "classical": []}


def header(before, after):
    return {"inputs": copy.deepcopy(before), "outputs": copy.deepcopy(after)}


def row_digest(row):
    data = json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    return hashlib.sha256(data).hexdigest()


def duplicate_free(pairs):
    value = {}
    for key, item in pairs:
        require(key not in value, "duplicate JSON key")
        value[key] = item
    return value


def references(table, row):
    """Typed references for only the retained constructors; not a verifier."""
    if table == "proofs":
        fields(row, ("kind", "rule", "premises", "implementation", "meaning",
                     "input_encoding", "output_encoding", "witness"))
        require(row["kind"] == "equation" and row["witness"] == WITNESS,
                "unsupported proof kind or witness")
        fields(row["rule"], ("tag",))
        require(row["rule"]["tag"] in {"rewire", "structural", "finite", "sequence",
                "tensor", "phase", "control", "repeat"}, "unsupported proof rule")
        require(type(row["premises"]) is list and len(row["premises"]) <= 16,
                "unsupported premise arity")
        return [("proofs", i) for i in row["premises"]] + [
            ("definitions", row["implementation"]), ("meanings", row["meaning"]),
            ("encodings", row["input_encoding"]), ("encodings", row["output_encoding"]),
        ]
    if table == "encodings":
        fields(row, ("logical", "physical", "body"))
        require(row["body"] == {"tag": "identity"} and row["logical"] == row["physical"],
                "only existing exact identity encodings are supported")
        return []
    fields(row, ("interface", "effect", "body") if table == "definitions" else ("interface", "body"))
    if table == "definitions":
        require(row["effect"] == "unitary", "non-unitary definition")
    fields(row["interface"], ("inputs", "outputs"))
    for endpoint in ("inputs", "outputs"):
        fields(row["interface"][endpoint], ("quantum", "classical"))
        require(row["interface"][endpoint]["classical"] == [], "classical boundary unsupported")
    body = row["body"]
    tag = body["tag"]
    if tag == "sequence":
        fields(body, ("tag", "children"))
        require(type(body["children"]) is list and 1 <= len(body["children"]) <= 16,
                "unsupported sequence arity")
        return [(table, i) for i in body["children"]]
    if tag == "tensor":
        fields(body, ("tag", "left", "right"))
        return [(table, body["left"]), (table, body["right"])]
    if table == "definitions" and tag in ("control", "repeat"):
        fields(body, ("tag", "definition", "polarity" if tag == "control" else "count"))
        return [(table, body["definition"])]
    if table == "meanings" and tag in ("control", "power"):
        fields(body, ("tag", "child", "polarity" if tag == "control" else "count"))
        return [(table, body["child"])]
    leaf_fields = {
        "rewire": ("tag", "permutation"), "structural": ("tag", "operation"),
        "leaf": ("tag", "program"), "finite": ("tag", "description"),
        "dyadic_phase": ("tag", "target", "j", "k"), "phase": ("tag", "j", "k"),
    }
    require(tag in leaf_fields, "unsupported retained constructor")
    require(tag not in ({"finite", "phase"} if table == "definitions" else {"leaf", "dyadic_phase"}),
            "constructor in wrong table")
    fields(body, leaf_fields[tag])
    return []


def graph(value):
    fields(value, ("format", "version", "profile", *TABLES, "entry"))
    require(value["format"] == "qleisli.hierarchical-ir" and value["version"] == 1
            and value["profile"] == "qpe-dyadic8-v1", "unexpected artifact schema")
    fields(value["entry"], ("implementation", "proof"))
    require(all(type(value[t]) is list and 1 <= len(value[t]) <= 60 for t in TABLES),
            "bounded table cardinality exceeded")
    edges = {}
    for table in TABLES:
        for ordinal in range(len(value[table])):
            refs = references(table, value[table][ordinal])
            for target, child in refs:
                index(child, len(value[target]))
            edges[(table, ordinal)] = refs
    require(sum(len(refs) for refs in edges.values()) <= 2000, "reference bound exceeded")
    di = index(value["entry"]["implementation"], len(value["definitions"]))
    pi = index(value["entry"]["proof"], len(value["proofs"]))
    proof = value["proofs"][pi]
    require(proof["implementation"] == di, "entry proof/implementation mismatch")
    mi = index(proof["meaning"], len(value["meanings"]))
    reached, pending = set(), [("definitions", di), ("proofs", pi)]
    while pending:
        current = pending.pop()
        if current not in reached:
            reached.add(current)
            pending.extend(edges[current])
    require(reached == set(edges), "unreachable typed table row")
    # No table may use the outer root as a child/provider. Only the root proof
    # has the required implementation/meaning references to the entry rows.
    roots = {("definitions", di), ("meanings", mi), ("proofs", pi)}
    for source, refs in edges.items():
        for target in refs:
            if target in roots:
                require(source == ("proofs", pi) and target in {("definitions", di), ("meanings", mi)},
                        "outer root has an incoming table reference")
    return di, mi, pi


def identity_encoding(value, ei, endpoint):
    encoding = value["encodings"][index(ei, len(value["encodings"]))]
    require(encoding == {"logical": endpoint, "physical": endpoint, "body": {"tag": "identity"}},
            "encoding does not bind the exact endpoint")


def sequence(value, di, mi, pi):
    definition, meaning, proof = value["definitions"][di], value["meanings"][mi], value["proofs"][pi]
    require(definition["body"]["tag"] == meaning["body"]["tag"] == "sequence"
            and proof["rule"] == {"tag": "sequence"}, "root sequence association mismatch")
    dc, mc, pc = definition["body"]["children"], meaning["body"]["children"], proof["premises"]
    require(len(dc) == len(mc) == len(pc), "sequence association cardinality mismatch")
    require(meaning["interface"] == definition["interface"], "sequence root headers differ")
    previous = definition["interface"]["inputs"]
    for ordinal in range(len(dc)):
        d = value["definitions"][index(dc[ordinal], len(value["definitions"]))]
        m = value["meanings"][index(mc[ordinal], len(value["meanings"]))]
        p = value["proofs"][index(pc[ordinal], len(value["proofs"]))]
        require(p["implementation"] == dc[ordinal] and p["meaning"] == mc[ordinal],
                "child proof does not bind corresponding definition/meaning")
        require(d["interface"] == m["interface"] and d["interface"]["inputs"] == previous,
                "sequence child endpoints mismatch")
        identity_encoding(value, p["input_encoding"], d["interface"]["inputs"])
        identity_encoding(value, p["output_encoding"], d["interface"]["outputs"])
        previous = d["interface"]["outputs"]
    require(previous == definition["interface"]["outputs"], "sequence final endpoint mismatch")
    return list(dc), list(mc), list(pc)


def append(value, before, after, db, mb, rule, premises, input_encoding, output_encoding):
    di, mi, pi = (len(value[t]) for t in ("definitions", "meanings", "proofs"))
    value["definitions"].append({"interface": header(before, after), "effect": "unitary", "body": copy.deepcopy(db)})
    value["meanings"].append({"interface": header(before, after), "body": copy.deepcopy(mb)})
    value["proofs"].append({"kind": "equation", "rule": {"tag": rule}, "premises": list(premises),
                            "implementation": di, "meaning": mi, "input_encoding": input_encoding,
                            "output_encoding": output_encoding, "witness": copy.deepcopy(WITNESS)})
    return di, mi, pi


def adapt(data, width):
    require(type(width) is int and width in (0, 1, 2, 3), "only fixed widths 0..3")
    require(len(data) <= LIMIT and hashlib.sha256(data).hexdigest() == ORIGINAL_SHA256[width],
            "original proposal hash/byte barrier failed")
    old = json.loads(data, object_pairs_hook=duplicate_free,
                     parse_constant=lambda _: (_ for _ in ()).throw(ValueError("non-JSON constant")))
    require(tuple(len(old[t]) for t in TABLES) == COUNTS[width], "unexpected original table counts")
    di, mi, pi = graph(old)
    d, m, p = old["definitions"][di], old["meanings"][mi], old["proofs"][pi]
    before = side(101, range(width), width)
    after = side(OUTPUT_OWNERS[width], reversed(range(width)), width)
    require(d["interface"] == m["interface"] == header(before, after), "unexpected frozen root labels/type/axis order")
    identity_encoding(old, p["input_encoding"], before)
    identity_encoding(old, p["output_encoding"], after)
    canonical = side(0, range(width), width)
    value = copy.deepcopy(old)
    added = {}
    if width == 0:
        body = {"tag": "rewire", "permutation": {"owners": [0], "axes": [], "classical": []}}
        require(d["body"] == m["body"] == body and p["rule"] == {"tag": "rewire"}
                and p["premises"] == [] and p["input_encoding"] == p["output_encoding"],
                "zero must be the single original identity rewire")
        value["definitions"][di]["interface"] = header(canonical, canonical)
        value["meanings"][mi]["interface"] = header(canonical, canonical)
        ei = p["input_encoding"]
        value["encodings"][ei] = {"logical": copy.deepcopy(canonical), "physical": copy.deepcopy(canonical), "body": {"tag": "identity"}}
        changed = {"definitions": {di}, "meanings": {mi}, "proofs": set(), "encodings": {ei}}
        require(value["definitions"][di]["body"] == d["body"] and value["meanings"][mi]["body"] == m["body"], "zero rewire body changed")
    else:
        dc, mc, pc = sequence(old, di, mi, pi)
        require(len(dc) == 5, "unexpected original outer-shell cardinality")
        ei = len(value["encodings"])
        value["encodings"].append({"logical": copy.deepcopy(canonical), "physical": copy.deepcopy(canonical), "body": {"tag": "identity"}})
        route = {"tag": "rewire", "permutation": {"owners": [0], "axes": list(range(width)), "classical": []}}
        prefix = append(value, canonical, before, route, route, "rewire", [], ei, p["input_encoding"])
        post = append(value, after, canonical, route, route, "rewire", [], p["output_encoding"], ei)
        enter_output = old["definitions"][dc[0]]["interface"]["outputs"]
        enter_output_encoding = old["proofs"][pc[0]]["output_encoding"]
        composed = append(value, canonical, enter_output,
                          {"tag": "sequence", "children": [prefix[0], dc[0]]},
                          {"tag": "sequence", "children": [prefix[1], mc[0]]},
                          "sequence", [prefix[2], pc[0]], ei, enter_output_encoding)
        value["definitions"][di]["interface"] = header(canonical, canonical)
        value["definitions"][di]["body"] = {"tag": "sequence", "children": [composed[0], *dc[1:], post[0]]}
        value["meanings"][mi]["interface"] = header(canonical, canonical)
        value["meanings"][mi]["body"] = {"tag": "sequence", "children": [composed[1], *mc[1:], post[1]]}
        value["proofs"][pi]["premises"] = [composed[2], *pc[1:], post[2]]
        value["proofs"][pi]["input_encoding"] = ei
        value["proofs"][pi]["output_encoding"] = ei
        added = {"canonical_encoding": ei, "prefix_DMP": list(prefix), "post_DMP": list(post), "composed_enter_DMP": list(composed),
                 "retained_child1_DMP": [dc[1], mc[1], pc[1]], "retained_suffix_D": dc[2:], "retained_suffix_M": mc[2:], "retained_suffix_P": pc[2:]}
        changed = {"definitions": {di}, "meanings": {mi}, "proofs": {pi}, "encodings": set()}
        require(sequence(value, di, mi, pi)[0][1:-1] == dc[1:], "old body/suffix ordering changed")
        sequence(value, composed[0], composed[1], composed[2])
    require(graph(value) == (di, mi, pi) and value["entry"] == old["entry"], "root pointers changed")
    preservation = []
    finite = []
    for table in TABLES:
        for ordinal in range(len(old[table])):
            first, current = old[table][ordinal], value[table][ordinal]
            if ordinal not in changed[table]:
                require(first == current, "existing nonroot row changed")
            preservation.append({"table": table, "index": ordinal, "changed": ordinal in changed[table],
                                 "before_row_sha256": row_digest(first), "after_row_sha256": row_digest(current)})
            key = "program" if table == "definitions" else "description" if table == "meanings" else None
            if key and key in first["body"]:
                require(first["body"][key].encode() == current["body"][key].encode(), "finite bytes changed")
                finite.append({"table": table, "index": ordinal, "field": key, "bytes": len(first["body"][key].encode()),
                               "sha256": hashlib.sha256(first["body"][key].encode()).hexdigest()})
    encoded = (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()
    require(len(encoded) <= LIMIT, "adapted output exceeds 1 MiB")
    association = {"width": width, "status": "untrusted-label-adapted-proposal", "entry": copy.deepcopy(old["entry"]),
                   "root_definition": di, "root_meaning": mi, "root_proof": pi,
                   "root_before": {"definition": d, "meaning": m, "proof": p},
                   "root_after": {"definition": value["definitions"][di], "meaning": value["meanings"][mi], "proof": value["proofs"][pi]},
                   "table_lengths_before": {t: len(old[t]) for t in TABLES}, "table_lengths_after": {t: len(value[t]) for t in TABLES},
                   "added_indices": added, "original_rows": preservation, "retained_finite_strings": finite,
                   "before_encoding_rows": [{"index": i, "row": old["encodings"][i]} for i in sorted({p["input_encoding"], p["output_encoding"]})],
                   "canonical_encoding_index": ei, "canonical_encoding_row": value["encodings"][ei],
                   "input_label_association": {"old_owner": 101, "canonical_owner": 0, "old_axes": list(range(width)), "canonical_axes": list(range(width))},
                   "output_label_association": {"old_owner": OUTPUT_OWNERS[width], "canonical_owner": 0, "old_axes": list(reversed(range(width))), "canonical_axes": list(range(width))},
                   "row_digest_scope": "Deterministic JSON of parsed row objects, not original raw transport slices; finite string UTF-8 bytes preserved exactly.",
                   "original_payload_sha256": hashlib.sha256(data).hexdigest(), "adapted_payload_sha256": hashlib.sha256(encoded).hexdigest(),
                   "local_graph_scope": "Typed reference/reachability and fixed structural assertions only, not native acceptance or a preservation theorem.",
                   "native_checked": False, "source_meaning_verified": False, "adapter_preservation_proved": False}
    return encoded, association
