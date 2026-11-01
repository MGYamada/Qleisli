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
from check_docs import rust_code
from current_metadata import INVENTORY, read_json

ROOT = Path(__file__).resolve().parents[1]
PACKETS = {'VM-23', 'VM-24', 'VM-25', 'VM-26', 'VM-27', 'VM-28', 'VM-29'}

# Reviewed source identities, not a theorem of minimality or a new admission.
# Keep internal selected/backend tags separate from this language-owned set.
LANGUAGE_PRIMITIVE_PATH = 'src/frontend/primitive.rs'
LANGUAGE_PRIMITIVES = {
    'H': 'h', 'Phase': 'phase', 'GlobalPhaseEighth': 'global_phase_eighth',
    'Unit': 'unit', 'Finish': 'finish', 'Split': 'split', 'Join': 'join',
    'MeasureZ': 'measure_z', 'Discard': 'discard', 'TakeBit': 'take_bit',
    'PutBit': 'put_bit', 'EmptyBits': 'empty_bits', 'PrependBit': 'prepend_bit',
}


def primitive_method(text, name):
    """Borrow one bounded method body; comments/literals cannot invent braces."""
    code = rust_code(text)
    match = re.search(r'\bpub\s+fn\s+' + re.escape(name) + r'\b[^{}]*\{', code)
    if match is None:
        raise ValueError('missing typed primitive method: ' + name)
    depth, end = 1, match.end()
    while end < len(code) and depth:
        depth += (code[end] == '{') - (code[end] == '}')
        end += 1
    if depth:
        raise ValueError('unclosed typed primitive method: ' + name)
    return text[match.end():end - 1]


def check_language_primitives(root):
    """Detect source catalog growth even after its digest/enum row is refreshed.

    This intentionally recognizes the current explicit catalog, not arbitrary
    Rust semantics. A new catalog representation requires reviewed guard changes.
    """
    text = (root/LANGUAGE_PRIMITIVE_PATH).read_text()
    actual = variants(text, 'PrimitiveId')
    if actual != {name: name for name in LANGUAGE_PRIMITIVES}:
        raise ValueError('unreviewed typed language primitive identity set')
    code = rust_code(text)
    match = re.search(r'\bpub\s+const\s+ALL\s*:[^=;]*=\s*&\[([^]]*)\]', code, re.S)
    if match is None or re.findall(r'\bSelf::(\w+)', match[1]) != list(LANGUAGE_PRIMITIVES):
        raise ValueError('typed language primitive ALL drift')
    body = primitive_method(text, 'spelling')
    masked = rust_code(body)
    expected_body = 'matchself{' + ''.join('Self::' + name + '=>,' for name in LANGUAGE_PRIMITIVES) + '}'
    if re.sub(r'\s+', '', masked) != expected_body:
        raise ValueError('typed language primitive spelling body must remain canonical')
    spellings = {}
    for row in re.finditer(r'Self::(\w+)\s*=>\s*("[a-z_]+")\s*,', body):
        if not masked[row.start():].startswith('Self::'):
            continue
        if row[1] in spellings:
            raise ValueError('duplicate typed language primitive spelling')
        spellings[row[1]] = json.loads(row[2])
    if spellings != LANGUAGE_PRIMITIVES:
        raise ValueError('typed language primitive spelling drift')
    lookup = re.sub(r'\s+', '', rust_code(primitive_method(text, 'lookup_unbound')))
    if lookup != 'Self::ALL.iter().copied().find(|id|id.spelling()==name)':
        raise ValueError('typed language primitive lookup must remain canonical unbound-only')


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
        'One explicit-edition execution-only QLV3 invocation retains original actual QIRF and request bytes, freshly decodes '
        'both original graphs, checks both full interfaces and complete Kraus reconstructions, then checks '
        'the coefficient bound and exact typed QDV1 equality for the full request and both retained graphs. '
        'Private allocation-bound report has no exact accepted-program/Meaning, pure-phase, inverse/control, '
        'cleanup or resource conversion; epsilon zero retains the same engineering claim kind.'
    ),
    'encoding': (
        'QLV3 execution scope and explicit edition with QLV1 original body/request and independently walked QDV1 '
        'engineering-instrument-request/engineering-instrument records; distinct '
        'qleisli.native-result 3 / engineering-checked / --qirf-engineering-instrument-native / execution response, '
        'matching the invoked edition and complete product version. Inspection/caller scope, old outer '
        'QLV1/QLV2 and other native modes or claim kinds reject.'
    ),
    'domain': (
        'Existing bounded R8 observing instruments with one quantum input owner, empty classical inputs, '
        'complete signature trees including zero-width owners, original dependencies, ordered public results, '
        'all unnormalized hidden histories and arbitrary finite references. qirf-r8-instrument-v1 names an '
        'IR profile, not hardware realization. Independent feed-forward/tensor and pure-to-instrument '
        'lemmas do not certify original source/QIRF composition or a native composed request.'
    ),
    'limits': (
        'Unchanged 16 MiB per-file/request and 64 MiB QLV3 envelope/view limits, existing six-bit dense '
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
        'One explicit-edition execution-only QLV3 invocation freshly decodes six original artifacts and checks each '
        'dependency order, full ordered interface, body matrix and exact Gram equation. Both parent '
        'matrices must equal independently computed low-first tensors. Component inequalities and '
        'exact budget addition share one work chain; no whole-parent Frobenius substitution. QDV1 '
        'compares the complete typed request and all six retained graphs. The private allocation-bound '
        'report grants no exact accepted-program/Meaning, inverse/control, cleanup or resource conversion, '
        'including epsilon zero.'
    ),
    'encoding': (
        'QLV3 execution scope and explicit edition with original QLV1 parent body/request; QDV1 engineering-pure-tensor '
        'record contains typed request and parent actual/ideal, left actual/ideal, right actual/ideal '
        'graphs in that order. Distinct qleisli.native-result 3 / engineering-checked / --engineering-pure-tensor-check '
        '/ execution response, matching the invoked edition and complete product version; old outer '
        'frames, inspection/caller scope and cross-mode or cross-kind replies reject.'
    ),
    'domain': (
        'Exactly two bounded rectangular R8 pure comparisons with exact phase, original dependencies, '
        'complete product type trees and zero-width owners retained. The additive parent bound covers '
        'arbitrary finite references under freshly checked exact isometry premises. The IR profile '
        'is not hardware; recursive/sequential/control/instrument native composition and source/target '
        'preservation remain separate.'
    ),
    'limits': (
        'Unchanged 16 MiB per-file/request, 64 MiB QLV3 envelope/view, dimension-64 exact matrices, '
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
 'binding': 'The original QLV1 body contains literal target bytes. One explicit-edition execution-only QLV3 invocation '
            'independently decodes that canonical byte sequence, constructs its actual Raw graph with an '
            'explicit zero-width Unit input owner consumed before preparation, freshly reads/checks the '
            'original ideal and dependencies, and checks both complete Kraus instruments and the coefficient '
            'bound in one work chain. QDV1 compares the full typed request, literal target bytes, ordered '
            'gate word, generated actual graph and original ideal graph. A private allocation-bound report '
            'grants no exact accepted-program, source/export, control/inverse, cleanup, resource or '
            'constitutional conversion, including epsilon zero.',
 'encoding': 'QLV3 execution scope and explicit edition with original QLV1 literal target body/request and QDV1 '
             'engineering-openqasm record containing typed request, literal byte array, ordered gate-name '
             'array, generated actual graph and original ideal graph. Distinct '
             'qleisli.native-result 3 / engineering-checked / --engineering-openqasm-check / execution response, '
             'matching the invoked edition and complete product version; inspection/caller scope, old '
             'outer frames and cross-mode or cross-kind replies reject.',
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


# Existing #64 bounded component only; descriptions and source preparation do
# not inherit the fresh native decision or establish original-source meaning.
FINITE_CARRIER_BOUNDARY = {
    'id': 'finite-carrier', 'group': 'finite-carrier',
    'entry_points': [
        'interchange::carrier::{Origin,Atom,Owner,Interface,Request}; Request::{encode,decode}',
        'BasisBinding::carrier_description (untrusted description)',
        'interchange::native::Kernel::check_carrier',
        'CarrierChecked::{artifact,request_bytes,request,native} (read-only retained binding)',
        'Instantiation::check_carrier',
        'CheckedSourceCarrier::{artifact,request_bytes,request,native,entry,source_meaning_verified}',
    ],
    'status': 'Bounded fresh native pure code/body equation; explicit source adapter remains check-only',
    'request': (
        'Strict six-field qleisli.carrier-request version 1 / finite-carrier-pure-v1: '
        'complete attached and independently required ordered input/output owner forests, public effect '
        'and independent exact logical matrix. Nominal atoms retain original module/declaration/source '
        'identity and full member/field order; Unit, Bits<0>, singleton, empty and product trees remain distinct.'
    ),
    'binding': (
        'Freshly decode original QIRF and request bytes, independently check original type/import/Nat '
        'declarations, dependencies and full interfaces, reconstruct code matrices and the actual pure '
        'body, and check physical * inputCode = outputCode * logical plus the logical Gram identity. '
        'Extra source rows require exact nominal references in the four owner forests; ordinary root '
        'checking retains strict source use. The explicit source adapter uses the common judgment/Builder, '
        'an independent caller matrix and retained-step replay against the same fresh decoded root. '
        'Sealed handles expose no Raw/AcceptedProgram conversion; source_meaning_verified is always false.'
    ),
    'encoding': (
        'Execution-only explicit-edition QLV3 containing original QLV1 body/request and a QDV1 '
        'finite-carrier-pure-v1 record over the complete graph, both interfaces and logical matrix. '
        'Distinct --carrier-pure-check / qleisli.native-result 3 / accepted / execution context must '
        'match the invoked edition and complete product version; inspection/caller and old frames reject.'
    ),
    'domain': (
        'Bounded exact pure finite enums/records and structural trees with complete ordered logical '
        'owners, including zero-width owners and exact scalar phase. Public Observe and actual '
        'observation/reset/discard refuse. Public Isometry is not sharpened to Unitary by a square body. '
        'Ordinary nominal execution, match/qmatch and original AST-to-step/source-function preservation '
        'remain pending; no inverse/control, cleanup, target/resource or constitutional admission follows.'
    ),
    'limits': (
        'Existing six-physical-bit/dimension-64 exact domain, 128-node forests, zero-based prefix '
        'depth at most 32, at most 128 owners/members, canonical i128 dyadics and shared 10M native '
        'work/60s process limits. Existing 16 MiB original body/request and 64 MiB envelope/view '
        'limits remain; source host preparation keeps its separate existing budgets. No capacity is raised.'
    ),
    'failure': (
        'Reject wrong full trees/ports/member order/nominal identity/source/dependencies, false code/body '
        'or Gram/phase equations, observation under pure labels, unsupported source helper-only rows, '
        'stale graph/request/view, wrong mode/scope/edition/version and exceeded limits. Missing, failed '
        'or timed-out native checker has no fallback or imported-success route.'
    ),
    'replacement': ['VM-23', 'VM-24', 'VM-25', 'VM-28', 'VM-29'],
}


ORDINARY_RESULT_BOUNDARY = {
    'id': 'ordinary-result', 'group': 'ordinary-result',
    'entry_points': [
        'interchange::ordinary_root::{Selection,Storage,Request}; Request::{encode,decode}',
        'interchange::native::Kernel::check_ordinary_root',
        'AcceptedProgram::{ordinary_result,portable_artifact}',
        'ordinary project check/run with a closed ordinary result',
        'ParsedProgram::{requires_typed_ordinary_transport,instantiate_ordinary_with_types}',
        'Instantiation::compile_ordinary_with_kernel',
        'SelectedOrdinaryProgram::{source,program,runtime_parameters}',
        'selected-source CLI check/run/sample through ordinary-v2',
    ],
    'status': 'Complete ordinary-input/result native checking and closed source execution; general source preservation remains open',
    'request': 'Strict qleisli.ordinary-root-request version2 / finite-ordinary-root-v2: original project/exported/Internal selection, module/function, ordered parameter basis forest, complete input storage and proposed rows, full result basis/storage and public effect. Lean independently enumerates the whole canonical input domain and requires exact row equality. No independent algorithm specification is inferred.',
    'binding': 'Fresh original signature/type/byte-envelope read, original Raw root/dependencies/ownership/effect/scope gate, typed input reading and exact complete instrument reconstruction for every independently enumerated canonical input, including all zero-probability hidden histories. Storage flattens to exact original input/output SSA lists. QDV compares the retained graph, selection, parameter/result forests, input rows, storage and effect; AcceptedProgram clones retain those same typed objects.',
    'encoding': 'Execution-only explicit-edition QLV3 with original QLV1 body/request, finite-ordinary-root-v2 QDV1 description and paired --ordinary-root-check / qleisli.native-result3 context. Internalv1, inspection/caller and old-mode fallback refuse. Portable export refuses until complete typed transport exists.',
    'domain': 'Finite ordinary enum/record parameters/results, construction, projection and exhaustive match through common original-body lowering. Nongeneric public selected runtime/classical roots and their eligible ordinary Basis/Nat dependency closure use the same emitter and native gate, borrowing complete original AST/text for a fresh common judgment with its associated indices. The immutable selected wrapper retains that instantiation and actual accepted request; small quantum temporaries use the same Raw emitter and all-history checks. Project main, selected run/sample and simulation APIs remain closed-only, including zero-width logical parameters. Ordinary Basis/Nat calls retain original nominal actuals, binder identities, public effects and closed partial siblings. Operation-formal closure, full qmatch and nominal finite-table consumers remain pending; selected Basis/Nat ordinary roots use the runtime-result gate; mixed quantum interfaces have the separately inventoried runtime-result gate. No source-pattern/body, decoder/native compiler/runtime/target preservation, inverse/control grant or new guarantee admission.',
    'limits': 'Existing six-bit/64-row native finite profile, 64 parameters and128 total parameter nodes; each complete input forest and result storage has128 nodes/depth32. The selected producer separately retains word width8,1024 function calls,depth16,10000 Raw instructions and100000 conservative source-work units; dormant quantum/control obligations continue through existing finite evidence checks. Existing original source, exact arithmetic,10M native work,60s process, body/request and envelope capacities remain unchanged. No maximum-size quantum case is introduced.',
    'failure': 'Reject stale original identity/type/member order, missing/duplicate/permuted/padding/wrong-width input rows, altered input/output SSA maps, invalid enum codes on any input/history, zero-width argument loss, hidden observation under pure labels, missing public effects, wrong scope/mode/edition/version and exceeded limits. Missing/failed native checker never falls back.',
    'replacement': ['VM-23', 'VM-24', 'VM-25', 'VM-28', 'VM-29'],
}


RUNTIME_RESULT_BOUNDARY = {
    'id': 'runtime-result', 'group': 'runtime-result',
    'entry_points': ['interchange::runtime_root::{Atom,Storage,Request}; Request::{encode,decode}',
        'interchange::native::Kernel::check_runtime_root',
        'AcceptedProgram::{runtime_result,portable_artifact}',
        'ParsedProgram::instantiate_runtime_with_types', 'Instantiation::compile_runtime_with_kernel',
        'SelectedRuntimeProgram::{source,program,runtime_parameters}',
        'project and selected mixed runtime source interfaces; selected Basis/Nat roots'],
    'status': 'Bounded mixed runtime source/native checking; source preservation remains open',
    'request': 'Strict internal qleisli.runtime-root-request version2 / finite-runtime-root-v2. Original selection/module/declaration, complete named Basis/Nat actuals, complete parameter/result prefixes including Q and tuple nodes, actual ordinary/owner storage, canonical input rows and public effect. No external algorithm specification.',
    'binding': 'Fresh original StaticRuntimeSignature read with complete Basis/Nat actuals and original ordered premises and shared Raw root/dependency checks. Independently enumerate ordinary inputs and reconstruct every hidden history; check ordinary result codes, physical * inputCode = outputCode * logical and complete logical Gram sum. Public effects retain observation and logical dimensions. Exact QDV compares the same graph/request objects retained by AcceptedProgram and fresh rechecking.',
    'encoding': 'Execution-only explicit-edition QLV3, original QLV1 packet and finite-runtime-root-v2 QDV. Paired --runtime-root-check / native-result3 context. Old modes, inspection/caller scopes and missing native checking never fall back. Portable export cannot erase the typed frame.',
    'domain': 'Nongeneric mixed finite interfaces, Q<enum>/Q<record>, nested tuples, zero-width owners, structural split/join and small observing bodies through the shared original-source emitter. Original declarations remain common checked. Snapshot actual inputs before expansion consumes them. Selected Basis/Nat roots reuse the same emitter with complete original-header/actual binding. Ordinary Basis/Nat calls retain original nominal actuals, binder identities, public effects and closed partial siblings. Operation-formal closure, nominal coherent-table/Meaning and wider qmatch integration remain pending. No AST/body, complex-denotation, native/runtime/target preservation, inverse/control grant or new guarantee admission.',
    'limits': 'Existing dense six-bit code/instrument components, 64 parameters and rows, 384 full type/storage prefix nodes, finite subtrees128/depth32 and ordinary storage128/depth32. Existing source, arithmetic,10M native work,60s process and envelope caps remain. Selected producer retains eight-bit words,1024 calls,depth16,10000 instructions,100000 work. No maximum-size quantum case is introduced.',
    'failure': 'Reject type/nominal/tuple/Q erasure, stale graph or source, wrong axis/owner identity, missing input rows, padding leakage, invalid classical values even on zero-probability histories, false public effects, missing explicit public quantum annotations, incompatible native scope/version and limits. Zero-width parameters still prevent closed execution.',
    'replacement': ['VM-23', 'VM-24', 'VM-25', 'VM-28', 'VM-29'],
}


QMATCH_BOUNDARY = {
    'id': 'qmatch-component', 'group': 'qmatch-component',
    'entry_points': [
        'interchange::qmatch::{SourceSite,Position,Site,Arm,Request}; Request::{encode,decode}',
        'interchange::native::Kernel::check_qmatch_source',
        'QmatchChecked::{artifact,request_bytes,request,native} (read-only component binding)',
    ],
    'status': 'Bounded original structural source-frame and exact Raw sector component, connected to the shared compiler; no ordinary-program conversion',
    'request': 'Strict qleisli.qmatch-request version4 / finite-source-qmatch-context-v4: original module/function, every literal event position and ordered sites, each retaining attached/required ordered quantum owner forests, original UTF8 byte offset, literal Raw start/count and actual evidence/control indices. Labels, logical matrices, graph roots and success flags are not supplied. Parsing and public data constructors issue no acceptance.',
    'binding': 'Fresh original source/header/operand/arm-name reads derive complete types, canonical labels, public effects, exact source rows and actual evidence subjects. The complete structural source function retains every quantum parameter and result, logical owner identities, basis trees and returned order. The local pair remains in selector/target order independently of the complete function interface. Additional zero-width owners remain in the original frame, and its public effect cannot be sharpened by the pure local contract. Independent transport through original Raw joins/splits and owner-moving operations must return those exact source roles; equal/empty wire lists do not supply identity. Matching source/Raw zero-width permutations succeed. Opaque-owner refinements and allocation/release need their checked source/representation rules. Unknown suffixes and ignored observation/discard refuse. Every original selection and supported direct h/global_phase_eighth/phase call appears once in evaluation order; arguments precede their enclosing call. Original closed Nat syntax and lexical static bindings determine phase parameters. Every initializer and ordinary caller intermediate is checked, including unused initializers and ignored helper actuals; original static helper bodies retain their checked signed-affine rules. Retained checked values preserve each initializer and its earlier helper/name interpretation without repeated evaluation. Existing canonical dyadic/eighth-root restrictions remain exact; no producer parameter values or success receipts supply those facts. Original callee-token/qmatch-keyword coordinates survive grouping; source name resolution checks lexical/module/prelude absence before primitive classification. Literal intervals exhaust the complete Raw body in order without gaps/overlaps and bind actual owner frames; each passes its own exact equations even if successive operators cancel. One original graph supplies fresh receipts with complete input/dependency provenance and actual U/CU/main equations. Rust proposes joint roots from actual requested entries/control programs; Lean independently derives relevance. QDV compares the same retained graph/caches, every typed site interface, original function, source occurrence, literal interval and arm indices. A private component handle retains the same allocations, without ordinary-program conversion or inverse/control access.',
    'encoding': 'Explicit-edition execution-only QLV3 wraps exact original QLV1 body/request and finite-source-qmatch-context-v4 QDV1 graph/source-function/ordered event-position/ordered qmatch-site records, including both interfaces, source-interval and arms. --qmatch-source-check requires matching native-result3 accepted/execution context, complete product version and actual request-presence flag. Inspection/caller, old frames and cross-mode replies refuse without fallback.',
    'domain': 'Bounded ordered pure primitive/selection literal intervals in a complete original structural function, with exact named-arm source association, finite builtin/nominal ordered type trees and preserved zero-width identities/phase. The shared compiler retains all quantum arguments and a flat quantum-owner result. Grouped/nested direct supported primitive calls, closed body-local static Nat aliases and named-arm selections share this boundary. Generic caller-actual binding remains separate. General expressions/call frames, mixed ordinary/quantum parameters, constructed/static/generic arms, the full twelve-bit/64-label source contract and source-body lowering remain unfinished. No new guarantee, source/runtime/target preservation or full QS/PR/RS/EXACT discharge is claimed.',
    'limits': 'Existing finite carrier/Raw/dependency/exact arithmetic and 10M native work limits remain. At most128 ordered selections (no separate128-event position cap),64 requested arms per selection,128 source rows and1MiB aggregate source identity; source names1..4096 UTF8 bytes and indicesu32. Shared carrier forests/ports retain their configured bounds and u8 port-width representation. Existing16MiB body/request,64MiB envelope/view and60s process bounds remain. No maximum-size quantum case is generated or capacity raised.',
    'failure': 'Reject stale types/ports/owner identity, false source occurrence/name/evidence association, overlapping/incomplete labels, observation in the pure selected interval, wrong public effect, phase/axis/dependency/body/control/Gram equations, unrelated nodes/rows, stale retained graph/request/caches and wrong context/scope. Source headers alone are not a source-body preservation theorem. A missing, failed, incompatible or timed-out checker grants no handle and never retries an old mode.',
    'replacement': ['VM-23', 'VM-24', 'VM-25', 'VM-28', 'VM-29'],
}


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
    # Native tests may put a multi-line cfg_attr between #[test] and fn.
    # Mask comments/literals first, so prose cannot invent a test attribute.
    code = rust_code(path.read_text())
    return set(re.findall(
        r'#\[\s*test\s*\]\s*(?:#\[[^]]*\]\s*)*'
        r'(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+([A-Za-z_]\w*)\s*\(', code))


def check(root=ROOT, data=None):
    try:
        check_language_primitives(root)
        if data is None:
            data = read_json(root, INVENTORY)
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
        if (LANGUAGE_PRIMITIVE_PATH, 'PrimitiveId') not in covered:
            raise ValueError('missing typed language primitive constructor family')
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
            if boundary['id'] == 'finite-carrier' and boundary != FINITE_CARRIER_BOUNDARY:
                raise ValueError('unreviewed finite-carrier boundary contract')
            if boundary['id'] == 'ordinary-result' and boundary != ORDINARY_RESULT_BOUNDARY:
                raise ValueError('unreviewed ordinary-result boundary contract')
            if boundary['id'] == 'runtime-result' and boundary != RUNTIME_RESULT_BOUNDARY:
                raise ValueError('unreviewed runtime-result boundary contract')
            if boundary['id'] == 'qmatch-component' and boundary != QMATCH_BOUNDARY:
                raise ValueError('unreviewed qmatch-component boundary contract')
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
        if ('src/interchange/carrier.rs' in paths and
                'finite-carrier' not in {b['id'] for b in data['boundaries']}):
            raise ValueError('missing finite-carrier public boundary')
        if ('src/interchange/ordinary_root.rs' in paths and
                'ordinary-result' not in {b['id'] for b in data['boundaries']}):
            raise ValueError('missing ordinary-result public boundary')
        if ('src/interchange/native/qmatch.rs' in paths and
                'qmatch-component' not in {b['id'] for b in data['boundaries']}):
            raise ValueError('missing qmatch-component public boundary')
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
    data = read_json(ROOT, INVENTORY)
    print(f"VM-22: {sum(len(e['members']) for e in data['enums'])} constructors, {len(data['sources'])} source snapshots, {len(data['boundaries'])} boundaries; native authority selected by #276; full Soundness remains open.")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
