#!/usr/bin/env python3
"""Check the VM-22 freeze, not semantic correctness or Lean coverage.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
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

# Reviewed metadata for this separate engineering route. Identity checks do not
# prove these claims; changing the route's contract requires explicit review.
ENGINEERING_INSTRUMENT_BOUNDARY = {
    'id': 'engineering-instrument',
    'group': 'engineering-instrument',
    'entry_points': [
        'interchange::engineering_instrument::EngineeringInstrumentRequest',
        'interchange::engineering_instrument::{check,check_with_kernel,check_serialized_with_kernel}',
        'EngineeringInstrumentReport original-artifact/request/profile accessors',
        'qleisli engineering compare-instrument ACTUAL --against=REQUEST',
    ],
    'status': 'Separate native engineering instrument check only; no exact cross-body or constitutional acceptance',
    'request': (
        'Strict 14-field qleisli.engineering-instrument-request v1: engineering-instrument-bound claim, '
        'complete-adjoint-euclidean-operator-norm-v1 metric, choi-l1-r8-instrument-v1 checker, '
        'qirf-r8-instrument-v1 IR profile, single-component-v1 composition and implementation-distance category; '
        'complete actual/expected input and result signature trees, source identity, closed nonnegative '
        'canonical dyadic epsilon and ordered coefficient majorants in unsquared norm units, original expected '
        'QIRF text. No supplied outcome labels, matrices, probabilities or success flags.'
    ),
    'binding': (
        'One execution-only QLV2 invocation retains original actual QIRF and request bytes, freshly decodes '
        'both original graphs, checks both full interfaces and complete Kraus reconstructions, then checks '
        'the coefficient bound and exact typed QDV1 equality for the full request and both retained graphs. '
        'Private allocation-bound report has no exact accepted-program/Meaning, pure-phase, inverse/control, '
        'cleanup or resource conversion; epsilon zero retains the same engineering claim kind.'
    ),
    'encoding': (
        'QLV2 execution scope with QLV1 original body/request and independently walked QDV1 '
        'engineering-instrument-request/engineering-instrument records; distinct '
        'qleisli.engineering-instrument-native 1 / engineering-checked / execution response. '
        'Inspection/caller scope, old outer QLV1 and other native response kinds reject.'
    ),
    'domain': (
        'Existing bounded R8 observing instruments with one quantum input owner, empty classical inputs, '
        'complete signature trees including zero-width owners, original dependencies, ordered public results, '
        'all unnormalized hidden histories and arbitrary finite references. qirf-r8-instrument-v1 names an '
        'IR profile, not hardware realization. Independent feed-forward/tensor and pure-to-instrument '
        'lemmas do not certify original source/QIRF composition or a native composed request.'
    ),
    'limits': (
        'Unchanged 16 MiB per-file/request and 64 MiB QLV2 envelope/view limits, existing six-bit dense '
        'reconstruction, i128 canonical dyadics with denominator exponent at most 126, one shared 10M '
        'native checker-work budget and 60s process timeout. Checker work is not emitted resource cost.'
    ),
    'failure': (
        'Reject missing/unknown/cross-kind context, noncanonical/negative/open budgets, incomplete/extra/reordered '
        'majorants, incorrect full signature/effect/owner/dependency/public projection, tight bounds, changed '
        'original graphs or typed view, wrong scope/version/response and exceeded capacity. '
        'Missing/failed/timed-out checker has no fallback; exact InstrumentContract remains unchanged.'
    ),
    'replacement': ['VM-23', 'VM-24', 'VM-28', 'VM-29'],
}

ENGINEERING_PURE_TENSOR_BOUNDARY = {
    'id': 'engineering-pure-tensor',
    'group': 'engineering-pure-tensor',
    'entry_points': [
        'interchange::engineering_pure_tensor::EngineeringPureTensorRequest',
        'interchange::engineering_pure_tensor::{check,check_with_kernel,check_serialized_with_kernel}',
        'EngineeringPureTensorReport original-artifact/request/profile accessors',
        'qleisli engineering compare-pure-tensor ACTUAL --against=REQUEST',
    ],
    'status': 'Separate native ordered-tensor engineering check only; no exact cross-body or constitutional acceptance',
    'request': (
        'Strict 14-field qleisli.engineering-pure-tensor-request v1: engineering-pure-tensor-bound claim, '
        'pure-euclidean-operator-norm-v1 metric, tensor-additive-r8-pure-leaf-v1 checker, qirf-r8-pure-v1 '
        'IR profile, ordered-tensor-two-v1 composition and implementation-distance category. Parent '
        'actual/ideal leaf requests, original ideal parent text, two ordered seven-field components '
        '(full domain/codomain, actual/ideal leaves, epsilon and both original texts), and a closed '
        'canonical nonnegative total epsilon exactly equal to the checked component sum.'
    ),
    'binding': (
        'One execution-only QLV2 invocation freshly decodes six original artifacts and checks each '
        'dependency order, full ordered interface, body matrix and exact Gram equation. Both parent '
        'matrices must equal independently computed low-first tensors. Component inequalities and '
        'exact budget addition share one work chain; no whole-parent Frobenius substitution. QDV1 '
        'compares the complete typed request and all six retained graphs. The private allocation-bound '
        'report grants no exact accepted-program/Meaning, inverse/control, cleanup or resource conversion, '
        'including epsilon zero.'
    ),
    'encoding': (
        'QLV2 execution scope with original QLV1 parent body/request; QDV1 engineering-pure-tensor '
        'record contains typed request and parent actual/ideal, left actual/ideal, right actual/ideal '
        'graphs in that order. Distinct qleisli.engineering-pure-tensor-native 1 / engineering-checked '
        '/ execution response; old outer frames, inspection/caller scope and cross-kind replies reject.'
    ),
    'domain': (
        'Exactly two bounded rectangular R8 pure comparisons with exact phase, original dependencies, '
        'complete product type trees and zero-width owners retained. The additive parent bound covers '
        'arbitrary finite references under freshly checked exact isometry premises. The IR profile '
        'is not hardware; recursive/sequential/control/instrument native composition and source/target '
        'preservation remain separate.'
    ),
    'limits': (
        'Unchanged 16 MiB per-file/request, 64 MiB QLV2 envelope/view, dimension-64 exact matrices, '
        'i128 canonical dyadics with denominator exponent at most 126, one shared 10M checker-work '
        'budget and 60s process timeout. Checker work is not program/target execution-resource cost.'
    ),
    'failure': (
        'Reject missing/extra components or context, changed profiles, open/noncanonical/negative '
        'budgets, stale total sum, false original-body matrices/Gram, altered dependencies/full type '
        'trees/ports/axes, incorrect parent tensor equations, changed typed request or any graph, '
        'wrong frame/scope/version/response and exceeded capacity. Missing/failed/timed-out checker '
        'has no fallback; exact native contracts remain unchanged.'
    ),
    'replacement': ['VM-23', 'VM-24', 'VM-28', 'VM-29'],
}


ENGINEERING_OPENQASM_BOUNDARY = {'id': 'engineering-openqasm',
 'group': 'engineering-openqasm',
 'entry_points': ['interchange::engineering_openqasm::EngineeringOpenQasmRequest',
                  'interchange::engineering_openqasm::{check,check_with_kernel,check_serialized_with_kernel}',
                  'EngineeringOpenQasmReport original-target/ideal/request/profile accessors',
                  'qleisli engineering compare-openqasm3 TARGET --against=REQUEST'],
 'status': 'Separate native target-bound engineering instrument check only; no exact source/export or '
           'constitutional acceptance',
 'request': 'Strict 14-field qleisli.engineering-openqasm-request v1: engineering-target-instrument-bound '
            'claim, complete-adjoint-euclidean-operator-norm-v1 metric, canonical-target-choi-l1-r8-v1 '
            'checker, openqasm3-canonical-one-qubit-terminal-r8-v1 target profile, single-component-v1 '
            'composition and implementation-distance category. Both full signature trees must be exactly '
            'Unit -> classical Bit. Original independent ideal QIRF text, source identity, canonical '
            'nonnegative closed dyadic epsilon and ordered unsquared coefficient majorants remain explicit; '
            'no producer matrices or success flags.',
 'binding': 'The original QLV1 body contains literal target bytes. One execution-only QLV2 invocation '
            'independently decodes that canonical byte sequence, constructs its actual Raw graph with an '
            'explicit zero-width Unit input owner consumed before preparation, freshly reads/checks the '
            'original ideal and dependencies, and checks both complete Kraus instruments and the coefficient '
            'bound in one work chain. QDV1 compares the full typed request, literal target bytes, ordered '
            'gate word, generated actual graph and original ideal graph. A private allocation-bound report '
            'grants no exact accepted-program, source/export, control/inverse, cleanup, resource or '
            'constitutional conversion, including epsilon zero.',
 'encoding': 'QLV2 execution scope with original QLV1 literal target body/request and QDV1 '
             'engineering-openqasm record containing typed request, literal byte array, ordered gate-name '
             'array, generated actual graph and original ideal graph. Distinct '
             'qleisli.engineering-openqasm-native 1 / engineering-checked / execution response; '
             'inspection/caller scope, old outer frames and cross-kind replies reject.',
 'domain': 'Canonical closed one-qubit OpenQASM 3.0: fixed stdgates.inc declaration, one qubit and one '
           'classical Bit, explicit reset, at most eight h/x/y/z/s/sdg/t/tdg gates and one terminal ordered '
           'measurement. The decoder loads no includes. Independent word-to-Raw meaning data reuse existing '
           'exact gates; literal complex phase equations are checked before observation. The declared '
           'standard-gate mathematical meaning is a specification assumption, not general OpenQASM or '
           'hardware certification. Complete-adjoint bounds cover every finite reference to this closed Unit '
           '-> Bit profile, not an arbitrary-input pure operation.',
 'limits': 'Separate fixed target profile: at most 1024 ASCII bytes, eight gates, one physical qubit and one '
           'terminal Bit; precharge precedes byte traversal. Existing 16 MiB ideal/request, 64 MiB '
           'envelope/view, six-bit dense R8 reconstruction, canonical i128 dyadics, one shared 10M '
           'checker-work budget and 60s process timeout are unchanged. Checker work is not a program or '
           'target resource certificate.',
 'failure': 'Reject unsupported or noncanonical target bytes, includes, statements, gates, operands, missing '
            'reset, post-readout gates, extra readouts, exceeded target-profile capacity, substituted full '
            'signatures, noncanonical/open/negative budgets, missing/extra/reordered majorants, false '
            'original ideal/dependencies/Gram, tight bounds, changed literal bytes/word/typed '
            'context/generated or ideal graph, wrong framing/scope/version/reply and '
            'missing/failed/timed-out checker. No fallback or epsilon-zero promotion; ordinary exact and '
            'instrument contracts remain unchanged.',
 'replacement': ['VM-23', 'VM-24', 'VM-28', 'VM-29']}


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
            if boundary['id'] == 'engineering-instrument' and boundary != ENGINEERING_INSTRUMENT_BOUNDARY:
                raise ValueError('unreviewed engineering-instrument boundary contract')
            if boundary['id'] == 'engineering-openqasm' and boundary != ENGINEERING_OPENQASM_BOUNDARY:
                raise ValueError('unreviewed engineering-openqasm boundary contract')
            if boundary['id'] == 'engineering-pure-tensor' and boundary != ENGINEERING_PURE_TENSOR_BOUNDARY:
                raise ValueError('unreviewed engineering-pure-tensor boundary contract')
        if len({b['id'] for b in data['boundaries']}) != len(data['boundaries']):
            raise ValueError('duplicate boundary')
        if ('src/interchange/engineering_instrument.rs' in paths and
                'engineering-instrument' not in {b['id'] for b in data['boundaries']}):
            raise ValueError('missing engineering-instrument public boundary')
        if ('src/interchange/engineering_openqasm.rs' in paths and
                'engineering-openqasm' not in {b['id'] for b in data['boundaries']}):
            raise ValueError('missing engineering-openqasm public boundary')
        if ('src/interchange/engineering_pure_tensor.rs' in paths and
                'engineering-pure-tensor' not in {b['id'] for b in data['boundaries']}):
            raise ValueError('missing engineering-pure-tensor public boundary')
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
