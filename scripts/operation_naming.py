"""Fixed source migration for the operation names adopted in Issue #45.

This checks migration provenance only; it is not an acceptance rule or oracle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import re


def canonical_operation_names(source):
    """Rename capabilities and constructed operations, preserving all other bytes."""
    tokens = []
    token_pattern = re.compile(rb"[A-Za-z_][A-Za-z_0-9]*|[^\s]")
    position = 0
    while position < len(source):
        if source[position:position + 2] == b"//":
            end = source.find(b"\n", position)
            position = len(source) if end < 0 else end
        elif source[position:position + 2] == b"/*":
            depth = 1
            position += 2
            while depth and position < len(source):
                pair = source[position:position + 2]
                if pair == b"/*":
                    depth += 1; position += 2
                elif pair == b"*/":
                    depth -= 1; position += 2
                else:
                    position += 1
        elif source[position:position + 1] == b'"':
            position += 1
            while position < len(source):
                if source[position:position + 1] == b"\\":
                    position += 2
                elif source[position:position + 1] == b'"':
                    position += 1; break
                else:
                    position += 1
        else:
            match = token_pattern.match(source, position)
            if match:
                end = match.end()
                tokens.append((match[0], position, end))
                position = end
            else:
                position += 1

    pairs, opened = {}, []
    for index, (token, _, _) in enumerate(tokens):
        if token == b"(":
            opened.append(index)
        elif token == b")" and opened:
            pairs[opened.pop()] = index
    predicates = {b"Apply": b"Applicable", b"Adjoint": b"Adjointable",
                  b"Controlled": b"Controllable"}
    descriptions = {b"inverse_op": b"adjoint", b"controlled_op": b"controlled"}
    replacements, requires = [], False
    for index, (token, start, end) in enumerate(tokens):
        if token == b"requires":
            requires = True
        elif token in (b"{", b";"):
            requires = False
        following = tokens[index + 1][0] if index + 1 < len(tokens) else None
        replacement = None
        if following == b"(":
            if requires and token in predicates:
                replacement = predicates[token]
            elif token in descriptions:
                replacement = descriptions[token]
            elif token == b"inverse":
                closing = pairs.get(index + 1)
                if closing is not None and closing + 1 < len(tokens) and tokens[closing + 1][0] == b"(":
                    replacement = b"adjoint"
        if replacement:
            replacements.append((start, end, replacement))
    for start, end, replacement in reversed(replacements):
        source = source[:start] + replacement + source[end:]
    return source
