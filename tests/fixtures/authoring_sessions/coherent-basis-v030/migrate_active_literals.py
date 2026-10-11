"""One reviewed source-spelling migration, outside compilation/acceptance.

Only active inline Rust source literals (excluding parser tests) and three live
examples are inputs. Historical snapshots and capacity constants are untouched.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
BASE = Path(__file__).resolve().parent
FILES = '''tuple_shapes static_semantics source_semantics review_v027 compile function_contracts operation_parameters quantum_unit_maps frontend_types source_judgments specification_boundaries certified_source source_scope source_ir_correspondence source_soundness static_operations repair_diagnostics project'''.split()
START = re.compile(r'\bdo\s+')
WORD = re.compile(r'[A-Za-z_][A-Za-z_0-9]*|[01]')


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def literals(text):
    i = 0
    while i < len(text):
        if text.startswith('//', i):
            end = text.find('\n', i)
            i = len(text) if end == -1 else end + 1
            continue
        if text.startswith('/*', i):
            depth = 1
            i += 2
            while depth:
                if text.startswith('/*', i):
                    depth += 1
                    i += 2
                elif text.startswith('*/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        raw = re.match(r'r(#{0,16})"', text[i:])
        if raw:
            begin = i + raw.end()
            end = text.index('"' + raw[1], begin)
            yield begin, end, bool(re.search(r'format!\(\s*$', text[max(0, i-100):i]))
            i = end + 1 + len(raw[1])
            continue
        if text[i] == '"':
            begin = i + 1
            i = begin
            while text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            yield begin, i, bool(re.search(r'format!\(\s*$', text[max(0, begin-101):begin-1]))
            i += 1
            continue
        char = re.match(r"'(?:\\.|[^'\\\n])'", text[i:])
        i += char.end() if char else 1


def whitespace(text, i):
    while i < len(text) and text[i].isspace():
        i += 1
    return i


def basis(text, i):
    def atom(i):
        i = whitespace(text, i)
        if text[i] == '(':
            i = whitespace(text, i + 1)
            if text[i] == ')':
                return i + 1
            while True:
                i = whitespace(text, basis(text, i))
                if text[i] == ')':
                    return i + 1
                assert text[i] == ',', ('basis tuple', text[i:i+60])
                i = whitespace(text, i + 1)
                if text[i] == ')':
                    return i + 1
        if text[i] == '{':
            end = text.index('}', i + 1)
            assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', text[i+1:end]), text[i:end+1]
            i = end + 1
        else:
            name = WORD.match(text, i)
            assert name, ('basis atom', text[i:i+100])
            i = name.end()
            if name[0] == 'not':
                return atom(i)
        current = whitespace(text, i)
        if current < len(text) and text[current] == '(':
            current = whitespace(text, current + 1)
            if text[current] == ')':
                return current + 1
            while True:
                current = whitespace(text, basis(text, current))
                if text[current] == ')':
                    return current + 1
                assert text[current] == ',', ('basis call', text[current:current+60])
                current = whitespace(text, current + 1)
        return i
    i = atom(i)
    while True:
        next_token = whitespace(text, i)
        op = WORD.match(text, next_token)
        if not op or op[0] not in ('xor', 'and'):
            return i
        i = atom(op.end())


def migrate(text, formatted):
    edits = []
    offset = 0
    while match := START.search(text, offset):
        arrow = text.index('<-', match.end())
        pattern = text[match.end():arrow].strip()
        assert ';' not in pattern and '\n' not in pattern, pattern
        at = arrow + 2
        nesting = []
        begin_input = whitespace(text, at)
        while at < len(text):
            char = text[at]
            if char in '([{':
                nesting.append(char)
            elif char in ')]}':
                assert nesting, ('input delimiter', text[match.start():at+1])
                assert '([{'.index(nesting.pop()) == ')]}'.index(char)
            elif char == ';' and not nesting:
                break
            at += 1
        assert not nesting and text.startswith('pure', whitespace(text, at + 1)), text[match.start():at+80]
        quantum = text[begin_input:at].strip()
        pure = whitespace(text, at + 1)
        begin = whitespace(text, pure + 4)
        end = basis(text, begin)
        body = text[begin:end]
        left, right = ('{{', '}}') if formatted else ('{', '}')
        replacement = f'basis {quantum} as {pattern} {left} {body} {right}'
        edits.append((match.start(), end, replacement))
        offset = end
    for start, end, replacement in reversed(edits):
        text = text[:start] + replacement + text[end:]
    return text, len(edits)


def main():
    touched = []
    for name in FILES:
        path = ROOT / 'tests' / (name + '.rs')
        before = path.read_text()
        after = before
        changes = 0
        spans = list(literals(before))
        for start, end, formatted in reversed(spans):
            old = before[start:end]
            if not START.search(old):
                continue
            new, count = migrate(old, formatted)
            after = after[:start] + new + after[end:]
            changes += count
        assert changes, 'expected active source spelling in ' + name
        assert '<-' not in after, 'unmigrated inline source ' + name
        path.write_text(after)
        touched.append({'path':str(path.relative_to(ROOT)), 'before_sha256':digest(before), 'after_sha256':digest(after), 'source_forms':changes})
    for relative in ('examples/bell/bell.qli','examples/bit_flip_code/code.qli','examples/semantic_contracts/main.qli'):
        path=ROOT/relative
        before=path.read_text()
        after,count=migrate(before,False)
        assert count and '<-' not in after
        path.write_text(after)
        touched.append({'path':relative,'before_sha256':digest(before),'after_sha256':digest(after),'source_forms':count})
    result={'format':'qleisli.coherent-basis-active-source-migration','version':1,
            'baseline_commit':'73355382a3db94893982e5954e9400fffcd7f48e','files':touched,
            'scope':'Only source spelling is rewritten. Test logic/assertions/capacities, lowering/checking, original fixtures and first captures are unchanged. Existing repeat(8192)/stress sources were neither expanded nor run.'}
    (BASE/'active-source-migration-01.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'touched_files':len(touched),'source_forms':sum(x['source_forms'] for x in touched),'files':[x['path'] for x in touched]},indent=2))


if __name__=='__main__':
    main()
