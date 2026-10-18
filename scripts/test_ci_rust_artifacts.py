"""Synthetic artifact mutations only; no real CI, Rust/native case or proof.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import copy
import base64
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import ci_rust_artifacts as gate
import ci_runtime
import ci_source_checks as checks
from test_ci_rust_producers import fixture

ROOT = Path(__file__).resolve().parents[1]
VERSIONS = {'python': 'Python 3.11.15', 'git': 'git version 2.50.0',
            'rust-latest': 'rustc 1.98.1 (synthetic)', 'cargo-latest': 'cargo 1.98.1 (synthetic)',
            'rust-msrv': 'rustc 1.85.0 (synthetic)', 'cargo-msrv': 'cargo 1.85.0 (synthetic)',
            'clippy-msrv': 'clippy 0.1.85 (synthetic)', 'lean': 'Lean (version 4.30.0, synthetic)'}


def prepare_root(root):
    manifest = json.loads((ROOT / 'corpus/manifest.json').read_text())
    for name in ['.github/ci/source-checks.json', 'corpus/manifest.json', 'scripts/check_input_corpus.py',
                 'corpus/' + manifest['negative_expectations']['path']]:
        path = root / name; path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, path)


class SyntheticRustReceipts:
    """Typed fixture data only; command success and CI provenance are simulated."""
    def __init__(self, root, context, binding):
        self.root, self.context, self.binding = root, context, binding
        self.kernel = dict(path=str(root / 'lean-kernel/.lake/build/bin/qleisli-kernel'), sha256='4' * 64)
        self.compiler = dict(path=str(root / 'target/debug/qleisli'), sha256='5' * 64)
        self.manifest = gate.digest((root / '.github/ci/source-checks.json').read_bytes())

    def report(self, group, partition):
        spec = checks.describe(group, partition=partition, root=self.root)
        environment = {key: value.replace('{root}', str(self.root)) for key, value in spec['environment'].items()}
        environment.update(CARGO_PROFILE_DEV_DEBUG='0', CARGO_PROFILE_TEST_DEBUG='0', CARGO_INCREMENTAL='0')
        rows = []
        for number, template in enumerate(spec['commands']):
            argv = [str(self.root / 'target/debug/qleisli') if arg == '{compiler}' else arg for arg in template]
            directory = Path('/synthetic-records') / group / str(number)
            command = ci_runtime.record_command(argv, directory)
            rows.append(dict(argv=argv, id=str(number), status='passed', log=str(directory / 'command.log'),
                             commands=[dict(command=command, executed_command=ci_runtime.launch_command(command),
                                            status='passed', exit_code=0)]))
        value = dict(format=1, status='passed', group=group, plan=spec, binding=self.binding,
                     manifest_sha256=self.manifest, commands=rows, kernel=self.kernel, environment=environment,
                     toolchain={name: dict(command=ci_runtime.launch_command(tool['command']), exit_code=0,
                                          version=VERSIONS[name], stderr='') for name, tool in spec['tools'].items()})
        if group in {'source-contracts', 'source-semantics'}:
            value['compiler'] = self.compiler
        return value

    def corpus(self):
        from check_input_corpus import representative_entries
        manifest_raw = (self.root / 'corpus/manifest.json').read_bytes(); manifest = json.loads(manifest_raw)
        negative = json.loads((self.root / 'corpus' / manifest['negative_expectations']['path']).read_text())
        ids = {'cases': [row['id'] for row in manifest['cases']], 'semantic_faults': sorted(gate.QUICK_FAULTS),
               'negative_cases': [row['id'] for row in negative['cases']]}
        probes = representative_entries(manifest['cases'])
        codes = {row['id']: row['expected_code'] for row in negative['cases']}
        return dict(format=1, status='passed', validation_mode='quick-representative-v1', failures=[],
                    representative_entries=json.loads(json.dumps(probes)), exhaustive_unitary_entries=False,
                    upstream_frameworks_executed=False,
                    manifest_sha256=gate.digest(manifest_raw),
                    oracle_script_sha256=gate.digest((self.root / 'scripts/check_input_corpus.py').read_bytes()),
                    compiler_sha256=self.compiler['sha256'], expected_ids=ids,
                    **{name: [dict(id=value, shipped_main='passed', semantic_probes=2 if value in probes else 0,
                                  typecheck='passed', semantic_mismatch='synthetic', exit_code=1, code=codes.get(value))
                              for value in values] for name, values in ids.items()})

    def child(self, profile, partition):
        return dict(format='qleisli.ci-rust-producer', version=1, context=self.context,
                    job=('check-rust' if profile == 'latest' else 'check-rust-msrv') + '-' + partition,
                    profile=profile, partition=partition, binding=self.binding, manifest_sha256=self.manifest,
                    kernel=self.kernel, compiler=self.compiler if partition == 'remaining' else None,
                    reports={group: gate.blob(gate.encoded(self.report(group, selected)))
                             for group, selected in gate.groups(profile, partition).items()},
                    corpus=gate.blob(gate.encoded(self.corpus())) if profile == 'latest' and partition == 'remaining' else None)


class RustArtifacts(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'candidate'; self.root.mkdir()
        prepare_root(self.root)
        self.context, self.needs = fixture()
        self.binding = dict(head=self.context['commit'], working_inputs_sha256='3' * 64)
        self.data = SyntheticRustReceipts(self.root, self.context, self.binding)
        self.kernel, self.compiler, self.manifest = self.data.kernel, self.data.compiler, self.data.manifest

    def child(self, profile, partition):
        return self.data.child(profile, partition)

    def test_first_wiring_and_release_refusals_keep_every_source_byte_without_execution(self):
        for name, stored_sha, raw_sha, size, count in [
            ('producer-wiring-first.json.gz', 'fb075f5bede090eb2ae8568b7909a4ba7beffbb219688e0791634d805777fbd6',
             'fe119666b81fc2caa5e1cc9f4df300cc7aefdeffc6aed9a570f31d699a4595ff', 109073, 7),
            ('producer-release-first.json.gz', 'a9a62c6b8cc19cd15f65786a81b69eddb26ac2ebc771905c1fa1d8b5361b6a8e',
             '6b638211ba3c7a81c1e021d5b7e3a5321e9f16fb58a6a608755025b93a033058', 132393, 3),
        ]:
            stored = (ROOT / 'tests/fixtures/authoring_sessions/ci-rust-parallel-v030' / name).read_bytes()
            self.assertEqual(hashlib.sha256(stored).hexdigest(), stored_sha)
            with gzip.GzipFile(fileobj=io.BytesIO(stored)) as archive:
                raw = archive.read(size + 1)
            self.assertEqual(len(raw), size)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), raw_sha)
            record = json.loads(raw)
            self.assertEqual(record['version'], 1)
            self.assertEqual(len(record['records']), count)
            self.assertEqual(len({row['path'] for row in record['records']}), count)
            for row in record['records']:
                data = base64.b64decode(row['base64'], validate=True)
                self.assertEqual((len(data), hashlib.sha256(data).hexdigest()), (row['bytes'], row['sha256']))

    def validate(self, value, profile='latest', partition='differential'):
        return gate.validate_child(self.root, self.context, profile, partition, gate.encoded(value), self.binding)

    def test_complete_synthetic_children_and_pair_keep_both_original_byte_blobs(self):
        for profile in ('latest', 'msrv'):
            context, needs = fixture(profile)
            children = {part: gate.encoded(self.child(profile, part)) for part in ('differential', 'remaining')}
            for part in children:
                job = ('check-rust' if profile == 'latest' else 'check-rust-msrv') + '-' + part
                needs[job]['outputs']['rust_receipt_sha256'] = gate.digest(children[part])
            files = gate.aggregate_files(self.root, context, profile, children, needs=needs, binding=self.binding)
            self.assertEqual(files['differential.json'], children['differential'])
            self.assertEqual(files['remaining.json'], children['remaining'])
            self.assertEqual(gate.validate_aggregate(self.root, context, profile, files, needs=needs, binding=self.binding), files)

    def test_wrong_role_context_source_manifest_or_binary_refuses(self):
        original = self.child('latest', 'differential')
        for field, value in [('profile', 'msrv'), ('partition', 'remaining'), ('job', 'check-rust'),
                             ('version', True), ('manifest_sha256', '0' * 64),
                             ('binding', self.binding | dict(head='9' * 40)),
                             ('context', self.context | dict(attempt='1')),
                             ('kernel', self.kernel | dict(path='/different/checker'))]:
            changed = copy.deepcopy(original); changed[field] = value
            with self.assertRaises(ValueError): self.validate(changed)
        for field in original:
            changed = copy.deepcopy(original); del changed[field]
            with self.assertRaises(ValueError): self.validate(changed)

    def test_missing_group_failed_omitted_or_changed_command_cannot_pass(self):
        original = self.child('latest', 'differential')
        changed = copy.deepcopy(original); changed['reports'] = {}
        with self.assertRaises(ValueError): self.validate(changed)
        for kind in ('status', 'missing', 'argv', 'execution', 'exit', 'native', 'compiler', 'tool', 'environment', 'plan'):
            changed = copy.deepcopy(original); report = json.loads(gate.unblob(changed['reports']['rust-latest']))
            if kind == 'status': report['commands'][-1]['status'] = 'not-run'
            elif kind == 'missing': report['commands'].pop()
            elif kind == 'argv': report['commands'][-1]['argv'].append('filter')
            elif kind == 'execution': report['commands'][-1]['commands'][0]['executed_command'].append('filter')
            elif kind == 'exit': report['commands'][-1]['commands'][0]['exit_code'] = False
            elif kind == 'native': report['kernel']['sha256'] = '8' * 64
            elif kind == 'compiler': report['compiler'] = self.compiler
            elif kind == 'tool': report['toolchain']['cargo-latest']['version'] = 'cargo 1.85.0 (wrong)'
            elif kind == 'environment': report['environment']['CARGO_PROFILE_TEST_DEBUG'] = '1'
            elif kind == 'plan': report['plan']['partition']['selected_indices'][0] = True
            changed['reports']['rust-latest'] = gate.blob(gate.encoded(report))
            with self.subTest(kind=kind), self.assertRaises(ValueError): self.validate(changed)

    def test_changed_blob_pair_hash_or_aggregate_cannot_substitute_for_actual_artifacts(self):
        child = self.child('latest', 'differential')
        child['reports']['rust-latest']['sha256'] = '0' * 64
        with self.assertRaises(ValueError): self.validate(child)
        children = {part: gate.encoded(self.child('latest', part)) for part in ('differential', 'remaining')}
        with self.assertRaises(ValueError): gate.aggregate_files(self.root, self.context, 'latest', children,
                                                               needs=self.needs, binding=self.binding)
        files = gate.aggregate_files(self.root, self.context, 'latest', children, binding=self.binding)
        changed = files | {'aggregate.json': files['aggregate.json'] + b' '}
        with self.assertRaises(ValueError): gate.validate_aggregate(self.root, self.context, 'latest', changed, binding=self.binding)
        with self.assertRaises(ValueError): gate.validate_aggregate(self.root, self.context, 'latest', {'aggregate.json': files['aggregate.json']}, binding=self.binding)

    def test_canonical_source_uses_the_captured_manifest_bytes(self):
        children = {part: gate.encoded(self.child('latest', part)) for part in ('differential', 'remaining')}
        captured = {}
        def read_source(name):
            if name not in captured:
                captured[name] = (self.root / name).read_bytes()
            return captured[name]
        gate.aggregate_files(self.root, self.context, 'latest', children, binding=self.binding, read_source=read_source)
        self.assertEqual(set(captured), {'.github/ci/source-checks.json', 'corpus/manifest.json',
                                         'scripts/check_input_corpus.py', 'corpus/negative/current-manifest.json'})
        manifest = self.root / '.github/ci/source-checks.json'
        manifest.write_bytes(b'{}')
        # Receipt checking keeps the captured source; its caller separately
        # rejects a source change through the complete snapshot/continuity gate.
        gate.aggregate_files(self.root, self.context, 'latest', children, binding=self.binding, read_source=read_source)
        with self.assertRaises(ValueError): gate.aggregate_files(self.root, self.context, 'latest', children, binding=self.binding)

    def test_latest_remaining_cannot_omit_corpus_cases_faults_or_counterexamples(self):
        for key in ('cases', 'semantic_faults', 'negative_cases'):
            changed = self.child('latest', 'remaining'); corpus = json.loads(gate.unblob(changed['corpus']))
            corpus[key].pop(); changed['corpus'] = gate.blob(gate.encoded(corpus))
            with self.assertRaises(ValueError): self.validate(changed, partition='remaining')
        changed = self.child('latest', 'remaining'); changed['corpus'] = None
        with self.assertRaises(ValueError): self.validate(changed, partition='remaining')

    def test_contradictory_corpus_rows_or_dropped_representative_probes_refuse(self):
        for kind in ('main', 'probes', 'fault', 'negative', 'selection'):
            changed = self.child('latest', 'remaining'); corpus = json.loads(gate.unblob(changed['corpus']))
            if kind == 'main': corpus['cases'][0]['shipped_main'] = 'failed'
            elif kind == 'probes':
                selected = next(row for row in corpus['cases'] if row['semantic_probes'] > 0)
                selected['semantic_probes'] = 0
            elif kind == 'fault': corpus['semantic_faults'][0]['semantic_mismatch'] = ''
            elif kind == 'negative': corpus['negative_cases'][0]['exit_code'] = 0
            elif kind == 'selection': corpus['representative_entries'] = {}
            changed['corpus'] = gate.blob(gate.encoded(corpus))
            with self.subTest(kind=kind), self.assertRaises(ValueError): self.validate(changed, partition='remaining')

    def test_producer_reads_actual_result_and_binary_bytes_before_emitting_outputs(self):
        # CI context/source observations are synthetic; file reading, canonical
        # report checks, digest binding and output/overwrite rules are actual.
        kernel_path = self.root / 'lean-kernel/.lake/build/bin/qleisli-kernel'
        compiler_path = self.root / 'target/debug/qleisli'
        kernel_path.parent.mkdir(parents=True); compiler_path.parent.mkdir(parents=True)
        kernel_path.write_bytes(b'SYNTHETIC-NOT-EXECUTABLE-KERNEL')
        compiler_path.write_bytes(b'SYNTHETIC-NOT-EXECUTABLE-COMPILER')
        self.data.kernel['sha256'] = gate.digest(kernel_path.read_bytes())
        self.data.compiler['sha256'] = gate.digest(compiler_path.read_bytes())
        for profile in ('latest', 'msrv'):
            for partition in ('differential', 'remaining'):
                with self.subTest(profile=profile, partition=partition):
                    results = Path(self.temp.name) / ('results-' + profile + '-' + partition);results.mkdir()
                    child = self.child(profile, partition)
                    for group, selected in gate.groups(profile, partition).items():
                        directory = results / (group if selected is None else group + '-' + selected)
                        directory.mkdir();(directory / 'results.json').write_bytes(gate.unblob(child['reports'][group]))
                    if child['corpus'] is not None:
                        (results / 'corpus.json').write_bytes(gate.unblob(child['corpus']))
                    output = Path(self.temp.name) / ('record-' + profile + '-' + partition)
                    gh_output = Path(self.temp.name) / ('outputs-' + profile + '-' + partition)
                    env = dict(GITHUB_JOB=child['job'], GITHUB_OUTPUT=str(gh_output), QLEISLI_KERNEL=str(kernel_path))
                    with (patch('check_release_ready.capture_context', return_value=self.context),
                          patch.object(checks, 'snapshot', return_value=self.binding)):
                        gate.record_producer(self.root, profile, partition, results, output, env)
                        with self.assertRaises(FileExistsError): gate.record_producer(self.root, profile, partition, results, output, env)
                    raw = (output / 'receipt.json').read_bytes()
                    self.assertIn('rust_receipt_sha256=' + gate.digest(raw), gh_output.read_text())
                    self.assertEqual(gate.validate_child(self.root, self.context, profile, partition, raw, self.binding)['job'], child['job'])
                    # A new byte identity cannot inherit an earlier check result.
                    original = kernel_path.read_bytes();kernel_path.write_bytes(original + b'changed')
                    with (patch('check_release_ready.capture_context', return_value=self.context),
                          patch.object(checks, 'snapshot', return_value=self.binding), self.assertRaises(ValueError)):
                        gate.record_producer(self.root, profile, partition, results, output.with_name(output.name + '-stale'), env)
                    kernel_path.write_bytes(original)

    def test_aggregate_reads_both_downloaded_receipts_and_rejects_symlink_or_wrong_digest(self):
        context, needs = fixture()
        evidence = Path(self.temp.name) / 'evidence';evidence.mkdir()
        for part in ('differential', 'remaining'):
            raw = gate.encoded(self.child('latest', part))
            directory = evidence / f'rust-validation-latest-{part}-{context["commit"]}-{context["attempt"]}'
            directory.mkdir();(directory / 'receipt.json').write_bytes(raw)
            needs['check-rust-' + part]['outputs']['rust_receipt_sha256'] = gate.digest(raw)
        output = Path(self.temp.name) / 'aggregate'
        env = dict(GITHUB_JOB='check-rust', RUST_NEEDS_JSON=json.dumps(needs))
        with (patch('check_release_ready.capture_context', return_value=context),
              patch.object(checks, 'snapshot', return_value=self.binding)):
            gate.record_aggregate(self.root, 'latest', evidence, output, env)
            files = {path.name: path.read_bytes() for path in output.iterdir()}
            gate.validate_aggregate(self.root, context, 'latest', files, needs=needs, binding=self.binding)
            changed = copy.deepcopy(needs);changed['check-rust-remaining']['outputs']['rust_receipt_sha256'] = '0' * 64
            with self.assertRaises(ValueError): gate.record_aggregate(self.root, 'latest', evidence, output.with_name('wrong'), env | dict(RUST_NEEDS_JSON=json.dumps(changed)))
            path = next(evidence.glob('*differential*/receipt.json'));target = path.with_name('outside.json')
            path.rename(target);path.symlink_to(target)
            with self.assertRaises(ValueError): gate.record_aggregate(self.root, 'latest', evidence, output.with_name('symlink'), env)


if __name__ == '__main__':
    unittest.main()
