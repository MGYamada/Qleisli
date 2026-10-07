#!/usr/bin/env python3
"""Regression tests for lossless source projection and exact comparisons.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import copy
import unittest

from observation_sources import basis, component
import test_lean_finite as finite
import test_lean_raw as raw
from test_lean_observation import component_oracle


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


if __name__ == '__main__':
    unittest.main()
