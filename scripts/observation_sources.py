"""Lossless bounded QIRF projection for independent observing test drivers.

This adapter grants no acceptance. The Rust/native comparison separately checks
the complete original bytes. Component checks receive original bodies, type
trees and source identities, with only dependency indices topologically renamed.
Unsupported evidence fails explicitly rather than dropping a dependency.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import copy


def require(condition, message):
    if not condition:
        raise ValueError(message)


def index(values, position):
    require(type(position) is int and 0 <= position < len(values),
            "source graph reference outside table")
    return values[position]


def basis(value, depth=0):
    require(depth <= 64 and isinstance(value, dict), "source basis depth/shape")
    tag = value.get("tag")
    if tag in {"unit", "bit"} and set(value) == {"tag"}:
        return [tag]
    if tag == "bits" and set(value) == {"tag", "width"}:
        require(type(value["width"]) is int and 0 <= value["width"] <= 255,
                "source basis width")
        return ["bits:" + str(value["width"])]
    if tag == "pair" and set(value) == {"tag", "left", "right"}:
        return ["pair"] + basis(value["left"], depth + 1) + basis(value["right"], depth + 1)
    if tag == "tuple" and set(value) == {"tag", "fields"}:
        require(isinstance(value["fields"], list) and len(value["fields"]) >= 3,
                "source basis tuple arity")
        return ["tuple:" + str(len(value["fields"]))] + [
            token for child in value["fields"] for token in basis(child, depth + 1)]
    raise ValueError("unsupported source basis")


def calls(value):
    """Visit every original branch and nested circuit, including unused arms."""
    if isinstance(value, dict):
        if value.get("tag") == "contract":
            yield value
        for child in value.values():
            yield from calls(child)
    elif isinstance(value, list):
        for child in value:
            yield from calls(child)


def component(artifact):
    require(isinstance(artifact, dict) and set(artifact) == {
        "format", "version", "profile", "programs", "evidence", "sources", "root", "root_interface"
    }, "unsupported source envelope")
    require(artifact["format"] == "qleisli.finite-ir" and type(artifact["version"]) is int
            and (artifact["version"], artifact["profile"]) in {
                (1, "finite-v0"), (2, "finite-meaning-v1")}, "unsupported source profile")
    programs, entries, sources = (artifact[k] for k in ("programs", "evidence", "sources"))
    require(all(isinstance(v, list) for v in (programs, entries, sources)), "source graph tables")
    require(len(programs) + len(entries) <= 65536, "source graph table limit")
    root = index(programs, artifact["root"])
    order, active, done = [], set(), set()

    def visit(position):
        entry = index(entries, position)
        require(position not in active and len(active) < 32, "source dependency cycle/depth")
        if position in done:
            return
        require(isinstance(entry, dict) and set(entry) == {
            "signature", "implementation", "specification", "identity"
        } | ({"tag"} if artifact["version"] == 2 else set())
                and entry.get("tag", "circuit") == "circuit", "unsupported source evidence")
        active.add(position)
        for key in ("implementation", "specification"):
            for call in calls(index(programs, entry[key])):
                visit(call["evidence"])
        active.remove(position)
        done.add(position)
        order.append(position)

    for position in range(len(entries)):
        visit(position)
    for call in calls(root):
        index(entries, call["evidence"])
    renamed = {old: new for new, old in enumerate(order)}

    def body(value):
        result = copy.deepcopy(value)
        for call in calls(result):
            call["evidence"] = renamed[call["evidence"]]
        return result

    dependencies = []
    for position in order:
        entry = entries[position]
        identity = entry["identity"]
        require(isinstance(identity, dict) and set(identity) == {
            "implementation", "specification", "sources"}, "source identity fields")
        attached = []
        for source_id in identity["sources"]:
            source = index(sources, source_id)
            require(set(source) == {"path", "text"}, "source identity snapshot")
            attached.append(dict(name=source["path"], source=source["text"]))
        dependencies.append(dict(signature=basis(entry["signature"]),
            implementation=body(index(programs, entry["implementation"])),
            specification=body(index(programs, entry["specification"])),
            identity=dict(implementation=identity["implementation"],
                          specification=identity["specification"], sources=attached)))
    return dict(format="qleisli.raw-observing-component", version=1,
                dependencies=dependencies, bindings=copy.deepcopy(dependencies), program=body(root))
