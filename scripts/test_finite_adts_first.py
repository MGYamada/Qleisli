"""Passive history preservation; never execute or extract saved sources.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
"""
# Scope notes: "tests/fixtures/authoring_sessions/finite-adts-v030/README.md".
# Original bytes: "tests/fixtures/authoring_sessions/finite-adts-v030/first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/index.json".
# Body history: "tests/fixtures/authoring_sessions/finite-adts-v030/body-index.json"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/body-first.tar.xz".
# Body checks: "tests/fixtures/authoring_sessions/finite-adts-v030/body-validation.json".
# Declaration history: "tests/fixtures/authoring_sessions/finite-adts-v030/declarations-first.tar.xz"
# and "tests/fixtures/authoring_sessions/finite-adts-v030/declarations-index.json".
# Declaration checks: "tests/fixtures/authoring_sessions/finite-adts-v030/declarations-validation.json".
# Current checks: "tests/fixtures/authoring_sessions/finite-adts-v030/validation.json".
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tests/fixtures/authoring_sessions/finite-adts-v030'


def read_history(index_name, archive_name, index_hash, stored_size, archive_hash, expanded):
    index_bytes = (FIXTURES / index_name).read_bytes()
    if hashlib.sha256(index_bytes).hexdigest() != index_hash:
        raise AssertionError('first index changed')
    index = json.loads(index_bytes)
    stored = (FIXTURES / archive_name).read_bytes()
    if (len(stored), hashlib.sha256(stored).hexdigest()) != (stored_size, archive_hash):
        raise AssertionError('first archive changed')
    data = {}
    total = 0
    with tarfile.open(fileobj=io.BytesIO(stored), mode='r:xz') as archive:
        for member in archive:
            path = PurePosixPath(member.name)
            if (not member.isfile() or member.mode != 0o644 or path.is_absolute()
                    or '..' in path.parts or str(path) != member.name
                    or member.name in data or member.name not in index['records']):
                raise AssertionError('noncanonical historical record')
            row = index['records'][member.name]
            if member.size != row['bytes'] or member.size > 8_000_000 or row['original_mode'] != 0o644:
                raise AssertionError('historical record exceeds declared bounds')
            total += member.size
            if total > expanded:
                raise AssertionError('historical expansion exceeds bounds')
            value = archive.extractfile(member).read(member.size + 1)
            if (len(value), hashlib.sha256(value).hexdigest()) != (row['bytes'], row['sha256']):
                raise AssertionError('historical bytes changed')
            data[member.name] = value
    if set(data) != set(index['records']) or total != expanded:
        raise AssertionError('first history is incomplete')
    return data


class FirstFiniteADTs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('index.json', 'first.tar.xz',
            '1c2f1e7dd7364157ecdf2f7b49068c11b872868b85104066353d64d1aa34fefc',
            862696, 'f3857707618584c552821edc5b207bf461a94913815108c77b55306695385f72', 30_807_429)

    def test_source_predictions_and_actual_refusals_remain_distinct(self):
        self.assertEqual(len(self.data), 60)
        plan = json.loads(self.data['source/plan.json'])
        report = json.loads(self.data['source/report.json'])
        self.assertEqual((len(plan['cases']), len(plan['sources'])), (10, 20))
        self.assertEqual(len(report['commands']), 12)
        self.assertEqual(report['prediction_mismatches'], [])
        self.assertTrue(report['source_unchanged'])
        self.assertTrue(report['first_source_unchanged'])
        self.assertEqual(report['before'], report['after'])
        self.assertEqual(sum(row['exit_code'] == 0 for row in report['commands']), 4)
        self.assertEqual(sum(row['exit_code'] == 1 for row in report['commands']), 8)
        for i, row in enumerate(report['commands'], 1):
            self.assertEqual(json.loads(self.data[f'source/observation-{i:02}.json']), row)
        refusals = [json.loads(row['stdout'])['diagnostics'][0]['code']
                    for row in report['commands'] if row['exit_code'] == 1]
        self.assertEqual(refusals.count('parse'), 7)
        self.assertEqual(refusals.count('type_mismatch'), 1)

    def test_failed_lean_attempt_is_not_promoted_to_a_proof(self):
        first = json.loads(self.data['encoding/observation-01/report.json'])
        self.assertEqual([row['exit_code'] for row in first['commands']], [0, 1])
        self.assertTrue(first['source_unchanged'])
        self.assertEqual(first['before'], first['after'])
        output = self.data['encoding/observation-01/proof.stdout']
        self.assertIn(b'failed to synthesize', output)
        self.assertIn(b'sorryAx', output)
        self.assertEqual(self.data['encoding/FiniteTagStudy.lean'],
                         self.data['encoding/observation-01/FiniteTagStudy.lean.txt'])

    def test_separate_repair_retains_the_actual_standard_axiom_scope(self):
        current = json.loads(self.data['encoding/observation-02/report.json'])
        self.assertEqual([row['exit_code'] for row in current['commands']], [0, 0])
        self.assertTrue(current['source_unchanged'])
        self.assertEqual(current['before'], current['after'])
        output = self.data['encoding/observation-02/proof.stdout'].decode()
        lines = output.splitlines()
        self.assertEqual(len(lines), 15)
        self.assertTrue(all(line.endswith('depends on axioms: [propext]') for line in lines))
        self.assertNotIn('sorryAx', output)
        self.assertEqual(self.data['encoding/observation-02/proof.stderr'], b'')
        self.assertEqual(self.data['encoding/FiniteTagStudy-v2.lean'],
                         self.data['encoding/observation-02/FiniteTagStudy-v2.lean.txt'])


class FirstCarrierBody(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('body-index.json', 'body-first.tar.xz',
            '7f3bc4ede17b2745a58e2280435d13e4df35585fb1cbf55d3135003d8e84be5b',
            594608, 'e9af41b1dcc609b267e90614a5351613a3cfca9bb9d55799dec2ee57f5778e56', 7_089_180)

    def test_observer_path_error_does_not_claim_a_lean_run(self):
        self.assertEqual(len(self.data), 38)
        failure = json.loads(self.data['observer-error/failure-summary.json'])
        self.assertEqual(failure['stage'], 'observer preflight, before Lean commands')
        self.assertEqual(failure['actual_companion'], '/Users/masa/git/qlirgo')
        self.assertIn('no validation command ran', failure['result'])

    def test_first_shadowed_postcondition_remains_a_failed_compile(self):
        first = json.loads(self.data['compile-first/report.json'])
        self.assertTrue(first['source_unchanged'])
        self.assertEqual(first['before'], first['after'])
        self.assertEqual([row['exit_code'] for row in first['commands']], [1])
        self.assertFalse(first['pass'])
        self.assertIn(b'Invalid field `cols`', self.data['compile-first/module.stdout'])
        self.assertIn(b'logical : checked.logical = logical', self.data['compile-first/Qirf-Carrier.lean.txt'])

    def test_successful_reductions_cannot_override_a_failed_compiled_audit(self):
        reductions = json.loads(self.data['recursive-owner-reading/observation-summary.json'])
        self.assertTrue(reductions['pass'])
        self.assertEqual([row['exit_code'] for row in reductions['commands']], [0, 0])
        audit = json.loads(self.data['compiled-audit-refusal/observation-summary.json'])
        self.assertFalse(audit['pass'])
        self.assertEqual([row['exit_code'] for row in audit['commands']], [1])
        self.assertEqual(audit['changed_source_files'], [])
        self.assertIn(b'readOwners._unsafe_rec: partial project declaration',
                      self.data['compiled-audit-refusal/registry.stdout'])
        fold = json.loads(self.data['fold-first/observation-summary.json'])
        self.assertFalse(fold['pass'])
        self.assertIn(b'unexpected token', self.data['fold-first/module.stdout'])


class FirstFiniteDeclarations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = read_history('declarations-index.json', 'declarations-first.tar.xz',
            'd0997f0a9c821eeecc559ab9f6a6f5aceddc450437e352ff0c0679635c73aa5d',
            638664, '92683f7179c3c8c270186a199b89bbfcfab3cb492c48ba548bdb68f94aa59387', 7_227_062)

    def test_failed_documentation_expectation_preserves_original_sources_and_spaces(self):
        self.assertEqual(len(self.data), 23)
        first = json.loads(self.data['first/report.json'])
        self.assertTrue(first['source_unchanged'])
        self.assertEqual(first['before'], first['after'])
        self.assertEqual([row['exit_code'] for row in first['commands']], [0, 101])
        self.assertIn(b'199 passed; 0 failed; 115 ignored', self.data['first/unit.stdout'])
        self.assertIn(b'finite_type_and_member_docs_keep_original_targets_without_verification_claims ... FAILED',
                      self.data['first/integration.stdout'])
        self.assertIn(b'rendered.contains("```text\\nSecond.\\n```")',
                      self.data['first-source/tests/documentation.rs.txt'])
        self.assertIn(b'rendered.contains("```text\\nSecond. \\n```")',
                      self.data['repair-01/documentation.rs.txt'])

    def test_successful_integration_does_not_hide_the_separate_strict_lint_refusal(self):
        repair = json.loads(self.data['repair-01/observation-summary.json'])
        self.assertFalse(repair['pass'])
        self.assertEqual([row['exit_code'] for row in repair['commands']], [0, 101])
        self.assertIn(b'needlessly taken reference of left operand', self.data['repair-01/lint.stderr'])
        self.assertIn(b'35 passed; 0 failed', self.data['repair-01/integration.stdout'])
        self.assertIn(b'4 passed; 0 failed', self.data['repair-01/integration.stdout'])


if __name__ == '__main__':
    unittest.main()
