"""Check the fixed source-only translation of retained corpus counterexamples.

This provenance rule supplies no source typing, semantic oracle or acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
from primitive_source_migration import migrate_qli, tokens

BIT_IDENTITY_PROJECTS = frozenset({
    'semantic_faults/graph_edge_erased',
    'semantic_faults/controlled_reflection_missing_phase',
    'semantic_faults/reflection_zero2_fault',
    'semantic_faults/basis_reflection_wrong_label',
})
IDENTITY = ('\n/// Identity on the one-Bit target of a coherent branch.\n'
            'unitary fn id(q: Q<Bit>) -> Q<Bit> { q }\n')
MODIFICATION = '// Primitive-source migration: Copyright 2026 Qleisli Project Contributors\n'


def canonical_counterexample_primitives(source, project):
    """Preserve fault bodies; only four reviewed branches gain a closed Bit id.

    Unknown imports, uninstantiated providers, possible capture and other
    ambiguities reject. An updated hash cannot legalize unrelated source edits.
    The ordinary checker and independent fault oracle must still run afterward.
    """
    original = source.decode('utf-8')
    text = original
    old_id = 'use std::quantum::id;'
    code = [token for token in tokens(text) if token.kind != 'comment']
    depth, imports = 0, []
    for i, token in enumerate(code):
        if depth == 0 and [item.text for item in code[i:i + 7]] == ['use', 'std', '::', 'quantum', '::', 'id', ';']:
            imports.append((token.start, code[i + 6].end))
        depth += (token.text == '{') - (token.text == '}')
    if imports:
        if len(imports) != 1:
            raise ValueError('ambiguous counterexample identity import')
        start, end = imports[0]
        if text[start:end] != old_id:
            raise ValueError('counterexample identity import needs explicit lexical review')
        text = text[:start] + text[end:]
        code = [token for token in tokens(text) if token.kind != 'comment']
        refs = [i for i, token in enumerate(code) if token.text == 'id']
        if refs:
            if project not in BIT_IDENTITY_PROJECTS or not all(
                    i > 1 and i + 1 < len(code) and code[i - 1].text == '>'
                    and code[i - 2].text == '=' and code[i + 1].text in {',', '}'} for i in refs):
                raise ValueError('counterexample identity needs explicit interface review')
            text += IDENTITY
    result = migrate_qli(text)
    if result['issues']:
        raise ValueError('ambiguous counterexample primitive translation: ' + '; '.join(result['issues']))
    text = result['source']
    if text != original:
        end = text.find('\n') + 1
        text = text[:end] + MODIFICATION + text[end:]
    return text.encode('utf-8')
