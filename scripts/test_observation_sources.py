#!/usr/bin/env python3
"""Regression tests for lossless source projection and exact comparisons.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import copy
from fractions import Fraction
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from observation_sources import basis, component
import test_lean_finite as finite
import test_lean_raw as raw
from test_lean_observation import component_oracle, oracle, p, pure_live, cases as observing_cases


class UnitOracleTests(unittest.TestCase):
    def test_work_boundaries_keep_the_original_hadamard_subject(self):
        cases=raw.cases()
        original=next(c for c in cases if c['name']=='gate_h')
        for budget in [0,1,23]:
            case=next(c for c in cases if c['name']=='exhausted_work_'+str(budget))
            self.assertEqual(case['artifact'],original['artifact'])
            self.assertEqual(case['required'],original['required'])
            self.assertEqual(case['budget'],budget)
            self.assertFalse(case['expected'])
        cases=observing_cases()
        original=next(c for c in cases if c['name']=='pure_gate_h')
        for name in ['producer_success_flag','unknown_profile']:
            case=next(c for c in cases if c['name']==name)
            expected=original['artifact']['program']
            if name=='producer_success_flag': expected=dict(expected,accepted=True)
            self.assertEqual(case['artifact']['program'],expected)
            self.assertFalse(case['expected'])

    def test_closed_unit_roundtrip_keeps_exact_scalar_phase(self):
        phase=[Fraction(0),Fraction(1,2),Fraction(0),Fraction(1,2)]
        for steps,wanted in [([],finite.ONE),([finite.mono([], [0],[1])],phase)]:
            operations=[raw.op('pack_unit',output=0),
                raw.op('apply_unitary',input=0,output=1,steps=steps),
                raw.op('unpack_unit',input=1)]
            program=p(operations=operations,effect='unitary')
            self.assertEqual(raw.raw_oracle(program),[[wanted]])
            self.assertEqual(oracle(program),[dict(hidden=[],results=[],operator=[[wanted]])])

    def test_unit_maps_keep_reference_axes_and_readout_histories(self):
        operations=[raw.op('pack_unit',output=2),raw.op('unpack_unit',input=2)]
        inputs=[raw.port(0,[7]),raw.port(1,[3])]
        program=p(inputs,operations=operations,outputs=[1,0],effect='unitary')
        z,o=finite.ZERO,finite.ONE
        swapped=[[o,z,z,z],[z,z,o,z],[z,o,z,z],[z,z,z,o]]
        self.assertEqual(raw.raw_oracle(program),swapped)
        self.assertEqual(oracle(program)[0]['operator'],swapped)
        program=p(inputs,operations=[raw.op('measure_z',input=0,output=0)]+operations,
                  outputs=[1],results=[0])
        self.assertEqual(oracle(program),[
            dict(hidden=[0],results=[False],operator=[[o,z,z,z],[z,z,o,z]]),
            dict(hidden=[1],results=[True],operator=[[z,o,z,z],[z,z,z,o]])])

    def test_unit_maps_do_not_coerce_or_overwrite_live_owners(self):
        for operation in [raw.op('pack_unit',output=0),raw.op('unpack_unit',input=0)]:
            with self.subTest(operation=operation):
                original={0:[7]}
                with self.assertRaises(ValueError): pure_live(original,operation)
                self.assertEqual(original,{0:[7]})
                with self.assertRaises(ValueError):
                    raw.raw_oracle(p([raw.port(0,[7])],operations=[operation]))
        with self.assertRaises(KeyError): pure_live({},raw.op('unpack_unit',input=0))


def artifact():
    leaf = raw.program(1, [raw.op('gate', gate='t', input=0, output=1)], 1)
    caller = raw.program(1, [raw.op('apply_unitary', input=0, output=1,
                                  steps=[finite.call([0], 1)])], 1)
    root = raw.program(1, [raw.op('apply_unitary', input=0, output=1,
                                steps=[finite.call([0], 0)])], 1)
    def entry(program):
        return dict(tag='circuit', signature=dict(tag='bit'), implementation=program,
                    specification=program, identity=dict(implementation='f', specification='f', sources=[0]))
    return dict(format='qleisli.finite-ir', version=2, profile='finite-meaning-v1',
                root=0, root_interface=None, programs=[root, caller, leaf], evidence=[entry(1), entry(2)],
                sources=[dict(path='original.qli', text='unaltered source')])


def observing_artifact():
    value = artifact()
    root = copy.deepcopy(value['programs'][0])
    root['operations'].append(raw.op('measure_z', input=1, output=0))
    root.update(quantum_outputs=[], classical_outputs=[0], declared_effect='observe')
    value['root'] = len(value['programs'])
    value['programs'].append(root)
    return value


class SourceProjectionTests(unittest.TestCase):
    def test_out_of_order_shared_dependencies_keep_bodies_and_identities(self):
        original = artifact()
        before = copy.deepcopy(original)
        projected = component(original)
        self.assertEqual(original, before)
        self.assertEqual(projected['dependencies'][0]['implementation'], original['programs'][2])
        self.assertEqual(projected['dependencies'][0]['identity']['sources'],
                         [dict(name='original.qli', source='unaltered source')])
        self.assertEqual(projected['program']['operations'][0]['steps'][0]['action']['evidence'], 1)
        self.assertEqual(projected['dependencies'][1]['implementation']['operations'][0]['steps'][0]['action']['evidence'], 0)
        self.assertEqual(component_oracle(projected)[0]['operator'], raw.raw_oracle(original['programs'][2]))
        projected['dependencies'][0]['identity']['sources'][0]['source'] = 'changed'
        self.assertEqual(projected['bindings'][0]['identity']['sources'][0]['source'], 'unaltered source')

    def test_missing_dependencies_invalid_roots_and_cycles_fail(self):
        for mutate in [lambda a: a.update(root=-1), lambda a: a.update(root=True),
                       lambda a: a.update(root=99), lambda a: a['evidence'].pop(),
                       lambda a: a['evidence'][1].update(implementation=1)]:
            with self.subTest(mutation=mutate):
                value = artifact(); mutate(value)
                with self.assertRaises(ValueError): component(value)

    def test_unsupported_evidence_is_not_silently_omitted(self):
        value = artifact(); value['evidence'][0]['tag'] = 'meaning'
        with self.assertRaisesRegex(ValueError, 'unsupported source evidence'):
            component(value)

    def test_different_equal_width_shapes_keep_their_type_tree(self):
        self.assertEqual(basis(dict(tag='bits', width=0)), ['bits:0'])
        self.assertNotEqual(basis(dict(tag='bit')), basis(dict(tag='bits', width=1)))
        self.assertEqual(basis(dict(tag='pair', left=dict(tag='unit'), right=dict(tag='bit'))),
                         ['pair', 'unit', 'bit'])

    def test_dependency_substitution_and_scalar_phase_are_detected(self):
        value = artifact()
        projected = component(value)
        expected = component_oracle(projected)
        changed = copy.deepcopy(projected)
        changed['dependencies'][0]['implementation']['operations'][0]['gate'] = 'z'
        with self.assertRaisesRegex(AssertionError, 'implementation/specification'):
            component_oracle(changed)
        changed['dependencies'][0]['specification'] = copy.deepcopy(changed['dependencies'][0]['implementation'])
        self.assertNotEqual(component_oracle(changed), expected)
        changed = copy.deepcopy(projected)
        changed['program']['operations'][0]['steps'].append(finite.mono([], [0], [1]))
        self.assertNotEqual(component_oracle(changed), expected)

    def test_pure_prefix_retains_selected_root_and_all_dependency_bodies(self):
        original = observing_artifact()
        before = copy.deepcopy(original)
        projected = raw.pure_source_prefix(original)
        self.assertEqual(original, before)
        self.assertEqual(len(projected['evidence']), 2)
        self.assertEqual(projected['evidence'][0]['implementation'], original['programs'][2])
        self.assertEqual(projected['program']['quantum_outputs'], [1])
        self.assertEqual(projected['program']['classical_outputs'], [])
        self.assertEqual(projected['program']['operations'][0]['steps'][0]['action']['evidence'], 1)
        self.assertEqual(raw.pure_component_oracle(projected), raw.raw_oracle(original['programs'][2]))
        original['root'] = 0
        with self.assertRaisesRegex(ValueError, 'terminal destructive measurements'):
            raw.pure_source_prefix(original)

    def test_pure_prefix_checks_dependency_substitution_and_phase(self):
        projected = raw.pure_source_prefix(observing_artifact())
        expected = raw.pure_component_oracle(projected)
        changed = copy.deepcopy(projected)
        changed['evidence'][0]['implementation']['operations'][0]['gate'] = 'z'
        with self.assertRaisesRegex(AssertionError, 'implementation/specification'):
            raw.pure_component_oracle(changed)
        changed['evidence'][0]['specification'] = copy.deepcopy(changed['evidence'][0]['implementation'])
        self.assertNotEqual(raw.pure_component_oracle(changed), expected)
        changed = copy.deepcopy(projected)
        changed['program']['operations'][0]['steps'].append(finite.mono([], [0], [1]))
        self.assertNotEqual(raw.pure_component_oracle(changed), expected)
        # Unused evidence is still checked, rather than trimmed from the graph.
        changed['program']['operations'][0]['steps'] = []
        changed['evidence'][0]['implementation']['operations'][0]['gate'] = 'z'
        with self.assertRaisesRegex(AssertionError, 'implementation/specification'):
            raw.pure_component_oracle(changed)

    def test_pure_prefix_preserves_output_axis_order_and_rejects_nonterminal_readout(self):
        value = observing_artifact()
        value['programs'][value['root']] = raw.program(2, [
            raw.op('apply_unitary', input=0, output=1, steps=[finite.call([0], 0)]),
            raw.op('split', input=1, left=2, right=3, left_bits=1),
            raw.op('measure_z', input=2, output=0), raw.op('measure_z', input=3, output=1)])
        value['programs'][value['root']].update(quantum_outputs=[], classical_outputs=[0, 1], declared_effect='observe')
        expected = raw.pure_component_oracle(raw.pure_source_prefix(value))
        root = value['programs'][value['root']]
        root['operations'][-2:] = root['operations'][-2:][::-1]
        changed = raw.pure_source_prefix(value)
        self.assertEqual(changed['program']['quantum_outputs'], [3, 2])
        self.assertNotEqual(raw.pure_component_oracle(changed), expected)
        root['operations'].append(raw.op('gate', gate='x', input=2, output=4))
        with self.assertRaisesRegex(ValueError, 'terminal destructive measurements'):
            raw.pure_source_prefix(value)

    def test_raw_source_reader_selects_current_projects_and_retains_original_bytes(self):
        with tempfile.TemporaryDirectory(prefix='qleisli-raw-reader-test-') as directory:
            root = Path(directory)
            for name in ['corpus', 'stdlib/src']:
                (root/name).mkdir(parents=True)
            for name in ['corpus/Qargo.toml', 'stdlib/Qargo.toml']:
                (root/name).write_text('schema-version = 2\n[qrate]\nedition = "2026"\n')
            compiler = root/'compiler'; compiler.write_bytes(b'fake compiler identity')
            original = json.dumps(observing_artifact()).encode('utf-8')
            selected = []

            def select(item):
                project = root/'corpus/migrations/current'/item['project']
                project.mkdir(parents=True)
                (project/'kernel.qli').write_text('current source snapshot')
                selected.append(project)
                return project

            def emit(command, cwd, log):
                self.assertEqual(Path(command[2]), selected[-1])
                Path(command[3].removeprefix('--output=')).write_bytes(original)

            with patch.object(raw, 'ROOT', root), patch.object(raw, 'current_corpus_project', side_effect=select), \
                    patch.object(raw.exact, 'command', side_effect=emit):
                cases = raw.source_cases([], compiler=compiler)
            self.assertEqual(len(cases), 6)
            for case, project in zip(cases, selected):
                self.assertEqual(case['original_qirf'].encode('utf-8'), original)
                self.assertEqual(case['provenance']['source_root'], str(project.relative_to(root)))
                self.assertIn(str((project/'kernel.qli').relative_to(root)), case['provenance']['sources'])
                self.assertEqual(len(case['artifact']['evidence']), 2)

    def test_explicit_missing_raw_compiler_does_not_build_a_different_binary(self):
        with tempfile.TemporaryDirectory(prefix='qleisli-missing-compiler-test-') as directory:
            with patch.object(raw.exact, 'command') as command:
                with self.assertRaises(FileNotFoundError):
                    raw.source_cases([], compiler=Path(directory)/'absent-compiler')
                command.assert_not_called()


if __name__ == '__main__':
    unittest.main()
