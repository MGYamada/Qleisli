#!/usr/bin/env python3
"""Mutation regressions for complete Rust test scheduling, without running Cargo.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import copy
import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_rust_test_partition as guard


ROOT = Path('/reviewed/root')


def commands(group='rust-latest', rest=('alpha',)):
    """Build independent literal command fixtures, including unchanged followups."""
    cargo = ['cargo', '+1.98.1'] if group == 'rust-latest' else ['python3', 'scripts/run_msrv.py']
    native = ['python3', 'scripts/run_kernel_tests.py', '--']
    scheduler = ['python3', 'scripts/run_rust_tests.py', '--workers', '2', '--record', '{record}', '--']
    before = [cargo + ['fmt', '--check']] if group == 'rust-latest' else []
    after = [native + cargo + ['test', '--test', 'sized_review_dialects', '--', '--ignored', '--skip', 'native'],
             ['python3', 'scripts/test_sized_primitive_catalog.py'], cargo + ['doc', '--no-deps'],
             native + cargo + ['test', '--doc']] if group == 'rust-latest' else []
    return before + [
        ['python3', 'scripts/check_rust_test_partition.py', '--group', group],
        native + scheduler + cargo + ['test', '--test', 'frontend_ownership_differential', '--test', 'source_ir_correspondence'],
        ['python3', 'scripts/check_rust_test_partition.py', '--group', group],
        native + scheduler + cargo + ['test', '--lib', '--bins', '--examples', '--benches'] +
        [part for name in rest for part in ['--test', name]],
    ] + after


def metadata(root=ROOT, tests=('alpha', 'frontend_ownership_differential', 'source_ir_correspondence')):
    """Synthetic Cargo conventions, not a claimed observation from a toolchain."""
    targets = []
    for kind, name, source, test, doctest, doc in [
        ('lib', 'qleisli', 'src/lib.rs', True, True, True),
        ('bin', 'qleisli', 'src/bin/qleisli.rs', True, False, True),
        ('custom-build', 'build-script-build', 'build.rs', False, False, False),
        *(( 'example', name, 'examples/' + name + '.rs', False, False, False)
          for name in ['interop', 'lean_kernel', 'native_acceptance', 'sampled_shor15', 'shor15']),
        *(( 'test', name, 'tests/' + name + '.rs', True, False, False) for name in tests),
    ]:
        targets.append(dict(name=name, kind=[kind], crate_types=['lib'] if kind == 'lib' else ['bin'],
                            src_path=str(root / source), edition='2024', test=test, doctest=doctest, doc=doc))
    return dict(version=1, workspace_root=str(root), workspace_members=['root-id'],
                workspace_default_members=['root-id'], packages=[dict(id='root-id', name='qleisli',
                manifest_path=str(root / 'Cargo.toml'), edition='2024', features={}, targets=targets)])


class PartitionTests(unittest.TestCase):
    def test_producer_partitions_cover_every_original_command_once(self):
        for group, first in [('rust-latest', [1, 2]), ('rust-msrv', [0, 1])]:
            original = commands(group)
            heavy = guard.command_indices(group, original, 'differential')
            rest = guard.command_indices(group, original, 'remaining')
            self.assertEqual(heavy, first)
            self.assertEqual(sorted(heavy + rest), list(range(len(original))))
            self.assertFalse(set(heavy) & set(rest))
            self.assertEqual(original[heavy[-1]][-4:],
                             ['--test', 'frontend_ownership_differential', '--test', 'source_ir_correspondence'])
            self.assertIn(['python3', 'scripts/check_rust_test_partition.py', '--group', group],
                          [original[index] for index in rest])

    def test_partition_selection_refuses_unknown_or_changed_complete_plans(self):
        for group in ('rust-latest', 'rust-msrv'):
            for part in ('', 'all', 'unknown'):
                with self.assertRaises(ValueError): guard.command_indices(group, commands(group), part)
            for index in range(len(commands(group))):
                changed = commands(group); changed[index] = ['true']
                for part in ('differential', 'remaining'):
                    with self.assertRaises(ValueError): guard.command_indices(group, changed, part)

    def test_both_pinned_entry_points_keep_complete_disjoint_selection(self):
        for group in ('rust-latest', 'rust-msrv'):
            actual = guard.validate(group, commands(group), metadata(), ROOT)
            self.assertEqual(actual['remaining'], ['alpha'])
            self.assertEqual(len(actual['inventory']), 11)
            self.assertEqual(actual['heavy'], ['frontend_ownership_differential', 'source_ir_correspondence'])

    def test_added_omitted_renamed_or_duplicate_metadata_target_refuses(self):
        for mutation in ('add', 'remove', 'rename', 'duplicate'):
            with self.subTest(mutation=mutation):
                value = metadata(); targets = value['packages'][0]['targets']
                if mutation == 'add':
                    targets.append(dict(targets[-1], name='new_target', src_path=str(ROOT / 'tests/new_target.rs')))
                elif mutation == 'remove':
                    targets.pop()
                elif mutation == 'rename':
                    targets[-1].update(name='renamed', src_path=str(ROOT / 'tests/renamed.rs'))
                else:
                    targets.append(copy.deepcopy(targets[-1]))
                with self.assertRaises(ValueError): guard.validate('rust-latest', commands(), value, ROOT)

    def test_wrong_kind_path_eligibility_crate_type_or_feature_refuses(self):
        for change in [dict(kind=['bench']), dict(kind=['example']), dict(src_path=str(ROOT / 'other.rs')),
                       dict(test=False), dict(test=1), dict(doctest=True), dict(doc=True),
                       dict(crate_types=['lib']), dict(edition='2021'), dict(**{'required-features': ['optional']})]:
            with self.subTest(change=change):
                value = metadata(); value['packages'][0]['targets'][-1].update(change)
                with self.assertRaises(ValueError): guard.validate('rust-latest', commands(), value, ROOT)

    def test_missing_or_extra_nonintegration_target_refuses(self):
        for mutation in ('missing', 'extra'):
            value = metadata(); targets = value['packages'][0]['targets']
            if mutation == 'missing':
                targets.pop(3)
            else:
                targets.append(dict(targets[3], name='new_example', src_path=str(ROOT / 'examples/new_example.rs')))
            with self.assertRaises(ValueError): guard.validate('rust-latest', commands(), value, ROOT)

    def test_automatic_build_script_is_preserved_as_dependency_only(self):
        for mutation in ('name', 'path', 'missing', 'unknown'):
            value = metadata(); targets = value['packages'][0]['targets']
            if mutation == 'name': targets[2]['name'] = 'renamed-build'
            elif mutation == 'path': targets[2]['src_path'] = str(ROOT / 'other-build.rs')
            elif mutation == 'missing': targets.pop(2)
            else: targets.append(dict(targets[2], name='second-build'))
            with self.assertRaises(ValueError): guard.validate('rust-latest', commands(), value, ROOT)
        value = commands(); value[4] += ['--test', 'build-script-build']
        with self.assertRaises(ValueError): guard.validate('rust-latest', value, metadata(), ROOT)

    def test_workspace_package_and_default_feature_drift_refuses(self):
        for mutation in ('workspace', 'default', 'package', 'path', 'features', 'version'):
            value = metadata()
            if mutation == 'workspace': value['workspace_members'].append('other-id')
            elif mutation == 'default': value['workspace_default_members'] = []
            elif mutation == 'package': value['packages'].append(copy.deepcopy(value['packages'][0]))
            elif mutation == 'path': value['packages'][0]['manifest_path'] = '/elsewhere/Cargo.toml'
            elif mutation == 'features': value['packages'][0]['features'] = {'default': []}
            else: value['version'] = 2
            with self.assertRaises(ValueError): guard.validate('rust-latest', commands(), value, ROOT)

    def test_selection_omission_addition_duplicate_overlap_and_filters_refuse(self):
        for tail in [[], ['--test', 'unknown'], ['--test', 'alpha', '--test', 'alpha'],
                     ['--test', 'alpha', '--test', 'source_ir_correspondence'],
                     ['--tests'], ['--all-targets'], ['--test', 'alpha', '--', '--skip', 'case'],
                     ['--test', 'alpha', '--no-default-features'], ['--test', 'alpha', '--features', 'foo']]:
            with self.subTest(tail=tail):
                value = commands(); value[4] = value[4][:-2] + tail
                with self.assertRaises(ValueError): guard.validate('rust-latest', value, metadata(), ROOT)

    def test_native_wrapper_pin_categories_and_guard_order_cannot_change(self):
        mutations = []
        value = commands(); value[2] = value[2][3:]; mutations.append(value)
        value = commands(); value[2][value[2].index('+1.98.1')] = '+1.85.0'; mutations.append(value)
        value = commands(); value[2][value[2].index('--workers') + 1] = '4'; mutations.append(value)
        value = commands(); value[4].remove('--benches'); mutations.append(value)
        value = commands(); value[1], value[2] = value[2], value[1]; mutations.append(value)
        value = commands(); value[2] = value[2][:-2]; mutations.append(value)
        value = commands(); value.pop(); mutations.append(value)
        value = commands(); value[5][-1] = 'unrelated'; mutations.append(value)
        for value in mutations:
            with self.assertRaises(ValueError): guard.validate('rust-latest', value, metadata(), ROOT)

    def test_explicit_harness_target_and_autodiscovery_overrides_refuse(self):
        baseline = (guard.ROOT / 'Cargo.toml').read_bytes()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            guard.manifest_conventions(root, baseline)
            for suffix in (b'\n[[test]]\nname="alpha"\nharness=false\n', b'\n[features]\noptional=[]\n',
                           b'\n[workspace]\nmembers=[]\n'):
                with self.assertRaises(ValueError): guard.manifest_conventions(root, baseline + suffix)
            for setting in ('autotests=false', 'autobins=false', 'autoexamples=false', 'autobenches=false'):
                altered = baseline.replace(b'[package]\n', b'[package]\n' + setting.encode() + b'\n')
                with self.assertRaises(ValueError): guard.manifest_conventions(root, altered)
            altered = baseline.replace(b'[lib]\n', b'[lib]\nharness=false\n')
            with self.assertRaises(ValueError): guard.manifest_conventions(root, altered)
            (root / '.cargo').mkdir(); (root / '.cargo/config.toml').write_text('[build]\ntarget="other"\n')
            with self.assertRaises(ValueError): guard.manifest_conventions(root, baseline)

    def test_metadata_is_not_started_for_invalid_selection(self):
        spec = guard.ci_source_checks.definition('rust-latest')
        spec['commands'] = commands(); spec['commands'][2] = ['cargo', 'test']
        with (patch.object(guard.ci_source_checks, 'definition', return_value=spec),
              patch.object(guard.sys, 'argv', ['guard', '--group', 'rust-latest']),
              patch.object(guard.subprocess, 'run') as run, contextlib.redirect_stderr(io.StringIO())):
            self.assertEqual(guard.main(), 1); run.assert_not_called()

    def test_first_actual_metadata_is_recorded_even_when_inventory_refuses(self):
        spec = guard.ci_source_checks.definition('rust-msrv'); spec['commands'] = commands('rust-msrv')
        value = metadata(guard.ROOT); value['packages'][0]['targets'].pop()
        output = io.StringIO()
        with (patch.object(guard.ci_source_checks, 'definition', return_value=spec),
              patch.object(guard.sys, 'argv', ['guard', '--group', 'rust-msrv']),
              patch.object(guard.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, json.dumps(value).encode(), b'')) as run,
              contextlib.redirect_stdout(output), contextlib.redirect_stderr(io.StringIO())):
            self.assertEqual(guard.main(), 1)
        self.assertEqual(json.loads(output.getvalue())['metadata'], value)
        self.assertEqual(run.call_args.args[0], ['python3', 'scripts/run_msrv.py', 'metadata', '--no-deps', '--locked', '--offline', '--format-version', '1'])
        self.assertEqual(run.call_args.kwargs['env']['RUSTUP_TOOLCHAIN'], '1.85.0')


if __name__ == '__main__':
    unittest.main()
