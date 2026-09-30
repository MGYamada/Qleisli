#!/usr/bin/env python3
"""Calibrate the independent VM-22 oracle and process failure behavior.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import json
from pathlib import Path
import sys
import tempfile
import unittest

from test_verification_baseline import FIXTURES, agrees, finite_comparisons, matrix, native_comparisons, oracle, unique, word_oracle


class OracleTests(unittest.TestCase):
    def artifact(self,name):
        return json.loads((FIXTURES/f'finite/{name}.v2.qirf').read_text())

    def required(self,name):
        return matrix(json.loads((FIXTURES/f'finite/{name}.matrix.json').read_text()))

    def test_all_frozen_columns_and_global_phase_faults(self):
        self.assertEqual(len(finite_comparisons()),12)

    def test_gate_change_is_detected_without_probability_comparison(self):
        data=self.artifact('t')
        data['programs'][0]['operations'][0]['gate']='z'
        self.assertFalse(agrees(oracle(data),self.required('t')))

    def test_scalar_on_unit_is_observable_in_equation(self):
        expected=self.required('unit_phase')
        self.assertFalse(agrees([1j*x for x in expected],expected))
        self.assertFalse(agrees([1+0j],expected))

    def test_alias_and_axis_faults_are_rejected(self):
        data=self.artifact('toffoli')
        data['programs'][0]['operations'][2]['control_b']=1
        with self.assertRaises((KeyError,ValueError)): oracle(data)
        data=self.artifact('raw_computed_target')
        last=data['programs'][0]['operations'][-1]
        last['left'],last['right']=last['right'],last['left']
        with self.assertRaisesRegex(ValueError,'output axes'): oracle(data)

    def test_no_claimed_matrix_or_unsupported_constructor_can_define_oracle(self):
        data=self.artifact('h')
        data['programs'][0]['operations'][0]['tag']='measure_z'
        with self.assertRaisesRegex(ValueError,'outside oracle'): oracle(data)
        data=self.artifact('h');data['evidence']=[{'claimed':'accepted'}]
        with self.assertRaisesRegex(ValueError,'outside bounded'): oracle(data)

    def test_domain_and_duplicate_native_fields_reject(self):
        description=json.loads((FIXTURES/'finite/t.matrix.json').read_text())
        description['domain']='phase256-word-v1'
        with self.assertRaisesRegex(ValueError,'domain'): matrix(description)
        with self.assertRaisesRegex(ValueError,'duplicate'): json.loads('{"accepted":true,"accepted":false}',object_pairs_hook=unique)

    def test_word_reference_retains_both_column_phases_and_claim(self):
        root=FIXTURES/'native'
        self.assertTrue(word_oracle((root/'t.qpk').read_text(),(root/'t.qpr').read_text()))
        for name in ['t_wrong_phase','t_forged_claim','t_wrong_domain','t_bad_count']:
            self.assertFalse(word_oracle((root/(name+'.qpk')).read_text(),(root/(name+'.qpr')).read_text()))

    def test_native_crash_and_bad_protocol_cannot_fall_back(self):
        with tempfile.TemporaryDirectory(prefix='qleisli-vm22-process-') as directory:
            binary=Path(directory)/'fake-kernel'
            for body in ['raise SystemExit(37)','print("{}")']:
                binary.write_text('#!'+sys.executable+'\n'+body+'\n'); binary.chmod(0o700)
                with self.assertRaisesRegex(ValueError,'process exit|protocol disagreement'): native_comparisons(binary,False)


if __name__=='__main__': unittest.main()
