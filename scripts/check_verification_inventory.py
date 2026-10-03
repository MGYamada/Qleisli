#!/usr/bin/env python3
"""Check the VM-22 freeze, not semantic correctness or Lean coverage.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import hashlib
import ast
import json
import re
import sys

sys.dont_write_bytecode = True
from check_docs import rust_code, rust_references

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = 'tests/fixtures/verification_v022/inventory.json'
PACKETS = {'VM-23', 'VM-24', 'VM-25', 'VM-26', 'VM-27', 'VM-28', 'VM-29'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def balanced(code, start):
    depth = 0
    for i in range(start, len(code)):
        if code[i] == '{':
            depth += 1
        elif code[i] == '}':
            depth -= 1
            if depth == 0:
                return i
    raise ValueError('unterminated Rust declaration')


def variants(text, name):
    code = rust_code(text)
    match = re.search(r'\bpub\s+enum\s+' + re.escape(name) + r'\s*(?:<[^{}]*>)?\s*\{', code)
    if match is None:
        raise ValueError('missing public enum ' + name)
    start = code.index('{', match.start())
    body = code[start+1:balanced(code, start)]
    entries, stack, offset = {}, [], 0
    pairs = {'}': '{', ')': '(', ']': '[', '>': '<'}
    for i, ch in enumerate(body + ','):
        if ch in '{([<':
            stack.append(ch)
        elif ch in pairs:
            if not stack or stack.pop() != pairs[ch]:
                raise ValueError('unsupported enum syntax: ' + name)
        elif ch == ',' and not stack:
            entry = body[offset:i].strip()
            offset = i + 1
            if entry:
                tag = re.match(r'[A-Za-z_]\w*', entry)
                if tag is None or tag[0] in entries:
                    raise ValueError('unsupported/duplicate enum member: ' + name)
                entries[tag[0]] = re.sub(r'\s+', ' ', entry)
    return entries


def public_functions(code):
    """Read signatures through balanced type delimiters, excluding the body.

    In particular, an array's semicolon does not terminate a signature. Braced
    const expressions nested in types are retained; their operators are not
    interpreted as generic delimiters. This remains a bounded source scanner.
    """
    methods = []
    pairs = {')': '(', ']': '[', '>': '<', '}': '{'}
    for match in re.finditer(r'\bpub\s+(?:const\s+)?fn\s+[A-Za-z_]\w*', code):
        stack = []
        for i in range(match.end(), len(code)):
            ch = code[i]
            if not stack and ch in '{;':
                methods.append(re.sub(r'\s+', ' ', code[match.start():i]).strip())
                break
            if ch in '([{':
                stack.append(ch)
            elif ch == '<' and '{' not in stack:
                stack.append(ch)
            elif ch == '>' and (code[i-1] == '-' or '{' in stack):
                continue
            elif ch in pairs:
                if not stack or stack.pop() != pairs[ch]:
                    raise ValueError('unsupported public function signature')
        else:
            raise ValueError('unterminated public function signature')
    return methods


def public_surface(text):
    """Freeze public declaration/signature spelling; private bodies are hashed.

    This bounded source inventory is not a Rust parser. Comments/string examples
    cannot invent declarations. Unsupported enum syntax fails explicitly.
    """
    code = rust_code(text)
    declarations = re.findall(r'^\s*pub\s+(?:struct|enum|type|trait|mod)\s+([A-Za-z_]\w*)', code, re.M)
    methods = public_functions(code)
    constants = [re.sub(r'\s+', ' ', m[0]).strip() for m in re.finditer(
        r'\b(?:pub(?:\([^)]*\))?\s+)?const\s+(?:MAX_|DEFAULT_)[A-Za-z_]\w*\s*:[^;]+;', code)]
    return {'declarations': sorted(declarations), 'functions': sorted(methods), 'capacity_constants': sorted(constants)}


def test_names(path):
    if path.suffix == '.py':
        return {n.name for n in ast.walk(ast.parse(path.read_text()))
                if isinstance(n, ast.FunctionDef) and n.name.startswith('test_')}
    return rust_references(path.read_text())[1]


def check(root=ROOT, data=None):
    try:
        if data is None:
            data = json.loads((root / INVENTORY).read_text())
        expected = {'format','version','packet','release','authority','groups','enums','sources','boundaries','capacities','corpus','native_packaging','comparison'}
        if set(data) != expected or data['format'] != 'qleisli.verification-inventory' or data['version'] != 1 or data['packet'] != 'VM-22':
            raise ValueError('unknown inventory format/fields')
        if data['authority'] != 'Lean production under approved v0.2.9 exception #276; external schemas disabled':
            raise ValueError('inventory cannot change production authority')
        groups = data['groups']
        if not groups or len({g['id'] for g in groups}) != len(groups):
            raise ValueError('missing/duplicate coverage group')
        for group in groups:
            if set(group) != {'id','producer','consumer','obligation','reference','replacement','positive','negative'}:
                raise ValueError('coverage group has missing/unknown fields')
            for key in ['producer','consumer','obligation','reference']:
                if not isinstance(group[key],str) or not group[key].strip():
                    raise ValueError('empty ' + key)
            if not group['replacement'] or not set(group['replacement']) <= PACKETS:
                raise ValueError('unknown replacement packet')
            for polarity in ['positive','negative']:
                reference = group[polarity]
                if set(reference) != {'path','test'}:
                    raise ValueError('missing test reference')
                path = root / reference['path']
                if not path.is_file():
                    raise ValueError('missing test source ' + reference['path'])
                if reference['test'] not in test_names(path):
                    raise ValueError('missing test ' + reference['test'])
        group_ids = {g['id'] for g in groups}
        covered = set()
        for enum in data['enums']:
            if set(enum) != {'path','name','members'} or (enum['path'],enum['name']) in covered:
                raise ValueError('missing/duplicate enum inventory')
            covered.add((enum['path'],enum['name']))
            actual = variants((root/enum['path']).read_text(),enum['name'])
            recorded = enum['members']
            if set(recorded) != set(actual):
                raise ValueError('constructor coverage drift: ' + enum['name'])
            for tag, member in recorded.items():
                if set(member) != {'declaration','group'} or member['group'] not in group_ids:
                    raise ValueError('unmapped constructor ' + tag)
                if member['declaration'] != actual[tag]:
                    raise ValueError('constructor field drift: ' + enum['name'] + '.' + tag)
        required = {'Effect','SingleGate','ScalarPhase','UnitaryStep','CircuitAction','ProtectedRegion','ProtectedUse','RawOp'}
        if not required <= {n for p,n in covered if p == 'src/ir.rs'} or ('src/contract/mod.rs','BasisType') not in covered:
            raise ValueError('missing published constructor family')
        if len({s['path'] for s in data['sources']}) != len(data['sources']):
            raise ValueError('duplicate source snapshot')
        paths = {s['path'] for s in data['sources']}
        for source in data['sources']:
            if set(source) != {'path','sha256','group','surface'} or source['group'] not in group_ids:
                raise ValueError('unmapped source snapshot')
            path = root/source['path']
            if digest(path) != source['sha256']:
                raise ValueError('frozen source changed; review inventory/fixtures: ' + source['path'])
            actual = public_surface(path.read_text()) if path.suffix == '.rs' else None
            if actual != source['surface']:
                raise ValueError('public API/capacity drift: ' + source['path'])
            if path.suffix == '.rs':
                for name in re.findall(r'\bpub\s+enum\s+(\w+)',rust_code(path.read_text())):
                    if (source['path'],name) not in covered:
                        raise ValueError('unlisted public constructor family: ' + name)
        # Discover new checking files as well as edits to existing ones.
        discovered = {str(p.relative_to(root)) for base in ['src','python/qleisli','stdlib/src'] for p in (root/base).rglob('*') if p.suffix in {'.rs','.py','.qli'}}
        discovered |= {str(p.relative_to(root)) for p in (root/'lean-kernel').rglob('*.lean') if '.lake' not in p.parts}
        if not discovered <= paths:
            raise ValueError('unlisted checking source: ' + ', '.join(sorted(discovered-paths)))
        for boundary in data['boundaries']:
            required_fields = {'id','group','entry_points','status','request','binding','encoding','domain','limits','failure','replacement'}
            if set(boundary) != required_fields or boundary['group'] not in group_ids:
                raise ValueError('incomplete boundary contract')
            if not boundary['entry_points'] or not boundary['replacement'] or not set(boundary['replacement']) <= PACKETS:
                raise ValueError('incomplete boundary replacement/entry')
            for key in ['status','request','binding','encoding','domain','limits','failure']:
                if not isinstance(boundary[key],str) or not boundary[key].strip():
                    raise ValueError('empty boundary field: ' + key)
        if len({b['id'] for b in data['boundaries']}) != len(data['boundaries']):
            raise ValueError('duplicate boundary')
        for capacity in data['capacities']:
            if set(capacity) != {'id','scope','value','source','test','replacement'} or capacity['source'] not in paths:
                raise ValueError('incomplete capacity scope')
            if not set(capacity['replacement']) <= PACKETS or not capacity['replacement']:
                raise ValueError('incomplete capacity replacement')
            if not capacity['value'] or not capacity['scope']:
                raise ValueError('unspecified capacity')
            path, name = capacity['test'].split('#',1)
            if name not in test_names(root/path):
                raise ValueError('missing capacity test ' + capacity['test'])
        corpus = data['corpus']
        if set(corpus) != {'cases','semantic_faults','pinned_files'} or corpus['cases'] != 36 or corpus['semantic_faults'] != 12:
            raise ValueError('finite corpus baseline drift')
        for path,sha in corpus['pinned_files'].items():
            if digest(root/path) != sha:
                raise ValueError('corpus baseline changed: ' + path)
        # Current corpus additions do not rewrite the original VM-22 census.
        frozen_corpus = root/Path(INVENTORY).parent
        baseline = json.loads((frozen_corpus/'corpus-manifest.json').read_text())
        current = json.loads((root/'corpus/manifest.json').read_text())
        if (baseline['sources'] != current['sources'] or
                baseline['policy'] != current['policy'] or
                current['cases'][:36] != baseline['cases']):
            raise ValueError('original corpus census changed')
        baseline_faults = json.loads((frozen_corpus/'corpus-semantic-faults.json').read_text())
        current_faults = json.loads((root/'corpus/semantic_faults/manifest.json').read_text())
        if current_faults['cases'][:12] != baseline_faults['cases']:
            raise ValueError('original corpus fault census changed')
        registry = json.loads((root/'lean/schema-registry.json').read_text())
        entries = registry['schemas'] if 'schemas' in registry else registry['entries']
        if not entries or any(e.get('external_enabled') is not False for e in entries):
            raise ValueError('external schema enabled; new acceptance review required')
        if not data['native_packaging'] or any(set(o) != {'option','current','selected_for_dual'} or o['selected_for_dual'] is not False or not o['option'] or not o['current'] for o in data['native_packaging']):
            raise ValueError('native-only inventory forbids dual packaging')
        comparison=data['comparison']
        if set(comparison) != {'pinned_files','reference','commands','scopes'} or not all(comparison.values()):
            raise ValueError('incomplete comparison baseline')
        for name,sha in comparison['pinned_files'].items():
            if digest(root/name)!=sha:
                raise ValueError('comparison fixture changed: ' + name)
        return []
    except (ValueError,KeyError,TypeError,OSError,SyntaxError) as e:
        return [str(e)]


def main():
    errors = check()
    if errors:
        for error in errors: print(error,file=sys.stderr)
        return 1
    data = json.loads((ROOT/INVENTORY).read_text())
    print(f"VM-22: {sum(len(e['members']) for e in data['enums'])} constructors, {len(data['sources'])} source snapshots, {len(data['boundaries'])} boundaries; native authority selected by #276; full Soundness remains open.")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
