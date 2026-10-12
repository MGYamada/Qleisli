#!/usr/bin/env python3
"""Retain original #362 observations; do not execute their recorded commands.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent.parent
BASELINE = 'tests/fixtures/verification_v030/execution-view-binding/baseline.json'
VECTORS = 'tests/fixtures/verification_v030/execution-view-binding/canonical-vectors.json'
FINITE_VECTORS = 'tests/fixtures/verification_v030/execution-view-binding/finite-walker-vectors.json'
FUNCTION_VECTORS = 'tests/fixtures/verification_v030/execution-view-binding/function-cache-vectors.json'
GRAPH_VECTORS = 'tests/fixtures/verification_v030/execution-view-binding/finite-graph-vectors.json'


class ExecutionViewEncodingTests(unittest.TestCase):
    def test_original_sources_packets_and_raw_diagnostics_are_unchanged(self):
        manifest = ROOT / BASELINE
        record = json.loads(manifest.read_text())
        self.assertEqual(record['source_commit'],
                         'e1816954b64aaf399dc29aeb69299f14be4815a4')
        self.assertEqual(len(record['files']), 86)
        for relative, digest in record['files'].items():
            path = manifest.parent / relative
            self.assertFalse(path.is_symlink())
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), digest,
                             relative)
        before = manifest.parent / 'before'
        for name in ('observations-before.json', 'unicode/observations-before.json'):
            rows = json.loads((before / name).read_text())
            self.assertEqual(len(rows), 16 if name.startswith('observations') else 14)
            for row in rows:
                for stream in ('stdout', 'stderr'):
                    output = before / Path(name).parent / row[stream]['path']
                    self.assertEqual(hashlib.sha256(output.read_bytes()).hexdigest(),
                                     row[stream]['sha256'])

    def test_unicode_controls_distinguish_refusal_from_execution_divergence(self):
        before = (ROOT / BASELINE).parent / 'before/unicode'
        rows = json.loads((before / 'observations-before.json').read_text())
        for row in rows:
            expected = 1 if row['kind'] == 'host' and row['case'] in {
                'lone-high', 'lone-low'} else 0
            self.assertEqual(row['exit_code'], expected, (row['case'], row['kind']))
        for case in ('ascii', 'valid-pair', 'literal-nonbmp',
                     'escaped-replacement', 'literal-replacement'):
            self.assertIn('accepted', (before / f'{case}-native.stdout').read_text())

    def test_shared_vectors_are_distinct_where_type_order_or_unicode_differs(self):
        rows = json.loads((ROOT / VECTORS).read_text())
        self.assertEqual(len(rows), 18)
        names = {row['name']: row['hex'] for row in rows}
        self.assertEqual(len(names), len(rows))
        self.assertEqual(len(set(names.values())), len(rows))
        for row in rows:
            self.assertTrue(bytes.fromhex(row['hex']).startswith(b'QDV1'))
        self.assertNotEqual(names['zero'], names['false'])
        self.assertNotEqual(names['empty-text'], names['empty-array'])
        self.assertNotEqual(names['precomposed'], names['decomposed'])
        self.assertNotEqual(names['ordered-booleans'], names['reverse-booleans'])

    def test_finite_vectors_cover_original_sources_and_all_raw_constructors(self):
        rows = json.loads((ROOT / FINITE_VECTORS).read_text())
        self.assertEqual(len(rows), 11)
        self.assertEqual(len({row['name'] for row in rows}), len(rows))
        self.assertEqual([row['source'] for row in rows if row['kind'] == 'raw-source'],
                         ['before/bell.qirf', 'before/phase.qirf',
                          'before/hidden-discard.qirf'])
        transport = next(row for row in rows if row['kind'] == 'raw')
        operations = transport['program']['operations']
        self.assertEqual(len(operations), 21)
        self.assertEqual(len({op['tag'] for op in operations}), 21)
        # This intentionally combines all constructors as transport data. It
        # is not a claim that their concatenation is a well-typed program.
        branch = operations[-1]
        self.assertTrue(branch['then_ops'] and branch['else_ops'])
        self.assertEqual(branch['quantum_phis'][1]['output_wires'], [])
        self.assertEqual(transport['program']['quantum_inputs'][1]['shape']['bits'], 0)

    def test_function_vectors_retain_independent_cache_expectations(self):
        rows = json.loads((ROOT / FUNCTION_VECTORS).read_text())
        self.assertEqual(len(rows), 10)
        cases = {row['name']: row for row in rows}
        self.assertEqual(len(cases), len(rows))
        unit = cases['unit-owner']['view']
        self.assertEqual(unit[1], [['unit']])
        self.assertEqual(unit[5], ['circuit', [['unit']], []])
        self.assertEqual(unit[7:], [1, 1])
        cancel = cases['branch-routes-cancel']['view']
        self.assertEqual(cancel[5][2], [])
        routed = cases['branch-route-then-h']['view'][5][2]
        self.assertEqual(routed[0], ['step', [], ['hadamard', 1]])
        self.assertEqual(routed[1][2][2], [0, 2, 1, 3])
        dependency = cases['original-index-adjoint-dependency']['view']
        self.assertEqual(dependency[5][2], [['step', [], ['contract', [0], 0, True]]])
        self.assertEqual(dependency[7:], [2, 1])

    def test_graph_vectors_bind_original_indices_and_metadata_distinctions(self):
        rows = json.loads((ROOT / GRAPH_VECTORS).read_text())
        self.assertEqual(len(rows), 7)
        cases = {row['name']: row for row in rows}
        self.assertEqual(len(cases), len(rows))
        unit = cases['unit-interface']['view']
        self.assertEqual(unit[2], ['root-interface', [['unit']], [['unit']]])
        self.assertEqual(unit[-1], [['port', 7, [], 0]])
        order = cases['output-order-with-unit']['view']
        self.assertEqual(order[-1], [['port', 9, [4], 1], ['port', 7, [], 0]])
        conservative = cases['conservative-observe']['view']
        self.assertEqual(conservative[6][-1], 2)
        self.assertEqual(conservative[-2], 0)
        dependency = cases['non-topological-evidence-indices']
        self.assertEqual(dependency['artifact']['root'], 4)
        self.assertEqual(dependency['artifact']['evidence'][0]['implementation'], 2)
        self.assertEqual(dependency['view'][5][0][5][2],
                         [['step', [], ['contract', [0], 1, True]]])
        self.assertEqual(dependency['view'][6][3][0][3],
                         [['step', [], ['contract', [0], 0, False]]])


if __name__ == '__main__':
    unittest.main()
