#!/usr/bin/env python3
"""Fresh original-QIRF tests for the unwired observing contract component.

The driver is experimental, not a public request schema or accepted handle.
It uses the existing native harness and independent full-history oracle.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import argparse
import copy
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

import check as experiment

ROOT = experiment.ROOT
finite, raw, observation = experiment.finite, experiment.raw, experiment.observation
native_harness = experiment.native_harness
PREAMBLE = finite.LEAN[:finite.LEAN.index('def execute')].replace(
    'set_option maxRecDepth 20000\n', '').replace('set_option maxHeartbeats 4000000\n', '')
DRIVER = 'import QleisliKernel.Qirf.InstrumentContract\nimport Protocol.Qirf\n' + PREAMBLE + '''
open QleisliKernel.Semantics.InstrumentContract
def atom (value : Json) : Except String ResultAtom := do
  match ← (← value.getObjVal? "tag").getStr? with
  | "unit" => pure .unit
  | "bit" => pure .bit
  | "bits" => pure (.bits (← (← value.getObjVal? "width").getNat?))
  | "quantum" => pure (.quantum (← QleisliKernel.Protocol.Qirf.basis 65 (← value.getObjVal? "basis")))
  | "pair" => pure .pair
  | "tuple" => pure (.tuple (← (← value.getObjVal? "arity").getNat?))
  | _ => throw "unknown experimental result atom"
def signature (value : Json) : Except String Signature := do
  return ⟨← QleisliKernel.Protocol.Qirf.basis 65 (← value.getObjVal? "input"),
    ← (← (← value.getObjVal? "result").getArr?).toList.mapM atom⟩
def execute (value : Json) : WorkM Json := do
  let actualBytes ← adapt ((← adapt (value.getObjVal? "actual")).getStr?)
  let expectedBytes ← adapt ((← adapt (value.getObjVal? "expected")).getStr?)
  let (actual,actualOrder) ← QleisliKernel.Protocol.Qirf.read actualBytes.toUTF8
  let (expected,expectedOrder) ← QleisliKernel.Protocol.Qirf.read expectedBytes.toUTF8
  let actualSignature ← adapt (signature (← adapt (value.getObjVal? "actual_signature")))
  let expectedSignature ← adapt (signature (← adapt (value.getObjVal? "expected_signature")))
  let source ← adapt (value.getObjVal? "identity")
  let names ← adapt ((← adapt (source.getObjVal? "sources")).getArr?)
  let sources ← names.toList.mapM fun (source : Json) => do
    pure (← adapt ((← adapt (source.getObjVal? "path")).getStr?),
      ← adapt ((← adapt (source.getObjVal? "text")).getStr?))
  let identity : QleisliKernel.Semantics.Function.Identity :=
    ⟨← adapt ((← adapt (source.getObjVal? "implementation")).getStr?),
      ← adapt ((← adapt (source.getObjVal? "specification")).getStr?),sources⟩
  let _ ← QleisliKernel.Qirf.InstrumentContract.check actual actualOrder expected expectedOrder
    actualSignature expectedSignature identity
  return Json.mkObj [("equal",toJson true)]
''' + observation.LEAN[observation.LEAN.index('def main'):]


def artifact(program):
    return dict(format='qleisli.finite-ir', version=1, profile='finite-v0', sources=[],
                programs=[program], evidence=[], root=0, root_interface=None)


def sig(result, basis=None):
    return dict(input=basis or dict(tag='bit'), result=result)


def cases():
    programs = experiment.programs()
    bit, unit = dict(tag='bit'), dict(tag='unit')
    qbit, qunit = dict(tag='quantum', basis=bit), dict(tag='quantum', basis=unit)
    paired = lambda a, b: [dict(tag='pair'), a, b]
    rows = []

    def add(name, actual, expected, signature, accepted, error='request', expected_signature=None):
        rows.append(dict(name=name, accepted=accepted, error=None if accepted else error,
            actual=finite.dumps(actual), expected=finite.dumps(expected), budget=10000000,
            actual_signature=copy.deepcopy(signature),
            expected_signature=copy.deepcopy(expected_signature or signature),
            identity=dict(implementation='implementation', specification='expected',
                          sources=[dict(path='experiment.qli', text='frozen experimental identity data')])) )

    for comparison in experiment.comparisons({n: observation.oracle(p) for n, p in programs.items()}):
        left, right = comparison['left'], comparison['right']
        signature = sig([bit] if left in {'z', 'ordered'} else [unit])
        if left == 'nondestructive': signature = sig(paired(qbit, bit))
        if left == 'identity': signature = sig([qbit])
        if left == 'ordered': signature = sig(paired(bit, bit))
        principal = programs[left]['declared_effect'] == 'observe'
        add(comparison['name'], artifact(programs[left]), artifact(programs[right]), signature,
            principal and comparison['expected'], error='equation' if principal else 'request')

    z = artifact(programs['z'])
    add('same_width_different_input_basis', z, z, sig([bit]), False,
        expected_signature=sig([bit], dict(tag='bits', width=1)))
    add('same_width_different_result_type', z, z, sig([bit]), False,
        expected_signature=sig([dict(tag='bits', width=1)]))
    ordered = artifact(programs['ordered'])
    add('same_width_different_result_tree', ordered, ordered, sig(paired(bit, bit)), False,
        expected_signature=sig([dict(tag='bits', width=2)]))
    discard = artifact(programs['discard'])
    add('ordinary_zero_bits', discard, discard, sig([dict(tag='bits', width=0)]), True)
    add('ordinary_unit_not_zero_bits', discard, discard, sig([unit]), False,
        expected_signature=sig([dict(tag='bits', width=0)]))
    empty = artifact(observation.p([raw.port(0, [])], operations=[raw.op('discard', input=0)]))
    add('zero_width_input_owner', empty, empty, sig([unit], unit), True)
    zero_owner = artifact(observation.p([raw.port(0, [0])], operations=[
        raw.op('measure_z', input=0, output=0), raw.op('pack_unit', output=1)], outputs=[1], results=[0]))
    add('zero_width_result_owner', zero_owner, zero_owner, sig(paired(qunit, bit)), True)
    add('missing_zero_width_result_owner', z, zero_owner, sig(paired(qunit, bit)), False)
    add('extra_zero_width_result_owner', zero_owner, z, sig([bit]), False)
    false_observe = artifact(dict(programs['identity'], declared_effect='observe'))
    add('annotation_does_not_supply_principal_observe', false_observe, false_observe, sig([qbit]), False)
    add('empty_result_prefix', z, z, sig([]), False, error='invalid')
    add('incomplete_result_prefix', z, z, sig([dict(tag='pair'), bit]), False, error='invalid')
    add('extra_result_prefix', z, z, sig([bit, unit]), False, error='invalid')
    add('noncanonical_tuple_arity', z, z, sig([dict(tag='tuple', arity=2), bit, unit]), False, error='limit')
    add('insufficient_pending_children', discard, discard,
        sig([dict(tag='tuple', arity=3), dict(tag='tuple', arity=3), unit, unit, unit, unit]),
        False, error='invalid')
    add('complete_nested_unit_tree', discard, discard,
        sig([dict(tag='pair'), unit, dict(tag='pair'), unit, unit]), True)
    add('wrong_classical_arity', z, z, sig([unit]), False)
    add('wrong_input_width', z, z, sig([bit], unit), False)
    with_classical = artifact(dict(programs['z'], classical_inputs=[7]))
    add('runtime_classical_input', with_classical, with_classical, sig([bit]), False)
    # Original root selection is authoritative, never a producer's matrix cache.
    alternate_root = copy.deepcopy(z)
    alternate_root['programs'].append(programs['flipped'])
    alternate_root['root'] = 1
    # The old root is now unreachable, so the existing complete-graph check
    # rejects this substitution before coefficient comparison.
    add('selected_wrong_original_root', alternate_root, z, sig([bit]), False, error='invalid')
    invalid_root = copy.deepcopy(z); invalid_root['root'] = 9
    add('root_outside_graph', invalid_root, z, sig([bit]), False, error='invalid')
    dependency = artifact(observation.p([raw.port(0, [0])], operations=[
        raw.op('apply_unitary', input=0, output=1, steps=[finite.call([0], 0)]),
        raw.op('measure_z', input=1, output=0)], results=[0]))
    pure_identity = programs['identity']
    dependency['programs'] = [pure_identity, pure_identity, dependency['programs'][0]]
    dependency['root'] = 2
    dependency['sources'] = [dict(path='dependency.qli', text='retained identity attachment')]
    dependency['evidence'] = [dict(signature=bit, implementation=0, specification=1,
        identity=dict(implementation='id', specification='id_spec', sources=[0]))]
    add('fresh_original_dependency', dependency, z, sig([bit]), True)
    changed = copy.deepcopy(dependency); changed['programs'][0] = programs['phase']
    add('dependency_substitution', changed, z, sig([bit]), False, error='equation')
    changed_pair = copy.deepcopy(dependency)
    hadamard = observation.p([raw.port(0, [0])], operations=[raw.op('gate', gate='h', input=0, output=1)],
                            outputs=[1], effect='unitary')
    changed_pair['programs'][0] = hadamard; changed_pair['programs'][1] = hadamard
    assert experiment.choi(observation.oracle(programs['z'])) != experiment.choi(observation.oracle(
        observation.p([raw.port(0, [0])], operations=[raw.op('gate', gate='h', input=0, output=1),
                      raw.op('measure_z', input=1, output=0)], results=[0])))
    add('fresh_valid_dependency_changes_whole_instrument', changed_pair, z, sig([bit]), False, error='equation')
    supplied_receipt = copy.deepcopy(z); supplied_receipt['accepted'] = True
    add('producer_supplied_acceptance', supplied_receipt, z, sig([bit]), False, error='invalid')
    bad_source = copy.deepcopy(dependency); bad_source['evidence'][0]['identity']['sources'] = [1]
    add('source_index_outside_snapshot', bad_source, z, sig([bit]), False, error='invalid')
    two = observation.p([raw.port(0, [0, 1])], operations=[
        raw.op('split', input=0, left=1, right=2, left_bits=1),
        raw.op('measure_z', input=1, output=0), raw.op('init0', output=3, wire=2)],
        outputs=[2, 3], results=[0])
    reverse = dict(two, quantum_outputs=[3, 2])
    assert experiment.choi(observation.oracle(two)) != experiment.choi(observation.oracle(reverse))
    two_sig = sig([dict(tag='tuple', arity=3), qbit, qbit, bit], dict(tag='bits', width=2))
    add('ordered_residual_axes', artifact(two), artifact(reverse), two_sig, False, error='equation')
    add('ordered_residual_axes_self', artifact(two), artifact(two), two_sig, True)
    bad_identity = copy.deepcopy(rows[0]); bad_identity.update(name='empty_identity', accepted=False, error='limit')
    bad_identity['identity']['implementation'] = ''; rows.append(bad_identity)
    bad_path = copy.deepcopy(rows[0]); bad_path.update(name='invalid_source_path', accepted=False, error='limit')
    bad_path['identity']['sources'][0]['path'] = ''; rows.append(bad_path)
    budget = copy.deepcopy(rows[0]); budget.update(name='zero_work_budget', accepted=False,
        error='arithmetic (QleisliKernel.Exact.Error.workLimit)', budget=0)
    rows.append(budget)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, required=True)
    args = parser.parse_args()
    before = native_harness.source_identity()
    rows, commands = cases(), []
    payload = '\n'.join(finite.dumps(row) for row in rows) + '\n'
    with tempfile.TemporaryDirectory(prefix='qleisli-instrument-qirf-gate-') as directory:
        project = Path(directory); (project / 'Main.lean').write_text(DRIVER)
        binary = native_harness.build(project, commands)
        started = time.monotonic()
        run = subprocess.run([str(binary)], input=payload, text=True, capture_output=True, timeout=60, check=True)
        commands.append(dict(command=[str(binary)], cwd=str(Path.cwd()), exit=run.returncode,
                             seconds=time.monotonic()-started, stderr=run.stderr))
        observed = [json.loads(line) for line in run.stdout.splitlines()]
        assert len(observed) == len(rows)
        for row, actual in zip(rows, observed):
            assert actual['accepted'] == row['accepted'], (row['name'], actual)
            if not row['accepted']:
                assert actual['error'] == 'QleisliKernel.Finite.Error.' + row['error'], (row['name'], actual)
        assert before == native_harness.source_identity(), 'kernel source changed'
        report = dict(format=1, status='passed', kind='unwired-original-qirf-instrument-gate',
            baseline_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
            recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), command=[sys.executable, *sys.argv],
            max_live_qubits=2, cases=[dict(name=r['name'], expected=r['accepted'], observed=o) for r, o in zip(rows, observed)],
            driver_sha256=hashlib.sha256(DRIVER.encode()).hexdigest(), binary_sha256=native_harness.digest(binary),
            inputs_sha256=hashlib.sha256(payload.encode()).hexdigest(), stdout_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),
            kernel_source_sha256=hashlib.sha256(json.dumps(before, sort_keys=True).encode()).hexdigest(),
            kernel_library_sha256=native_harness.digest(native_harness.LIBRARY), commands=commands,
            source_sha256={str(p.relative_to(ROOT)): native_harness.digest(p) for p in [Path(__file__), Path(experiment.__file__)]},
            limits=['experimental driver; public protocol and private handle not enabled',
                    'full signatures are checked request data; no source-to-IR type preservation proof',
                    'no full QS/PR/RS discharge, new guarantee or release claim'])
    args.record.write_text(json.dumps(report, indent=2)+'\n')
    print(f'{len(rows)} fresh original-QIRF instrument gate checks passed; max 2 live qubits')


if __name__ == '__main__':
    main()
