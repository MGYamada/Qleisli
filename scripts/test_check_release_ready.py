#!/usr/bin/env python3
"""Synthetic readiness and adversarial CLI/provenance tests; no real release claim.

Hosted context, successful build receipts and release acceptance are simulated
in disposable repositories. Actual constitutional proof verification has its own
live tests; this suite neither fabricates human admission nor runs Lean builds.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
"""
import copy
import io
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import check_release_ready as checker
from check_ratification_packet import PacketError, ROOT

SCRIPT = ROOT / 'scripts/check_release_ready.py'
RESULT = dict(admitted_guarantees=2, pending_obligations=3, mode='source-identity-only')


def encoded(data):
    return (json.dumps(data, indent=2, sort_keys=True) + '\n').encode()


def archive(files, prefix=''):
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode='w') as out:
        for name, data in files.items():
            if hasattr(data, 'data'):
                raw, mode = data.data, data.mode
            else:
                raw, mode = data, 0o644
            item = tarfile.TarInfo(prefix + name)
            item.size, item.mode = len(raw), mode
            out.addfile(item, io.BytesIO(raw))
    return stream.getvalue()


class SyntheticRelease(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='qleisli-release-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / 'candidate'
        self.root.mkdir()
        self.evidence = Path(self.temp.name) / 'evidence'
        self.evidence.mkdir()
        self.git('init', '--quiet')
        self.write('Cargo.toml', b'[package]\nname="qleisli"\nversion="0.3.0-alpha"\n')
        self.write('lean/schema-registry.json', b'{}\n')
        for name in ['archive_lean_kernel.py', 'package_lean_kernel.py', 'check_lean_kernel.py']:
            self.write('scripts/' + name, b'# Synthetic source identity only\n')
        self.write('lean-kernel/Main.lean', b'-- Synthetic artifact input; not a proof\n')
        self.write('release/issue-snapshot.txt', b'Synthetic criterion for test only.\n')
        self.write('release/review.txt', b'Synthetic review; not human authority or an Issue decision.\n')
        self.write('release/evidence.txt', b'Synthetic positive/negative/implementation reference.\n')
        # Match the actual ledger's distinct binding/pending identity fields.
        # The prior {'id': ...} pending fixture concealed a production KeyError.
        interpretations = ['PR-2026-01', 'QS-2026-01', 'RS-2026-01']
        self.ledger = dict(
            binding_interpretations=[dict(id=name, jurisdiction=name[:2]) for name in interpretations],
            discharged_guarantees=[{'id': name} for name in ['QS-QLV1-OWNERSHIP-2026-01', 'QS-QLV1-SCOPE-2026-01']],
            pending_obligations=[dict(interpretation=name, formalization_status='pending-coverage-and-adequacy-review',
                                     proof_status='not-discharged', evidence_bindings=[]) for name in interpretations])
        self.write(checker.LEDGER, encoded(self.ledger))
        self.requirements = dict(format='qleisli.release-requirements', version=1, release_line='0.3.0',
                                identities=checker.IDENTITIES, groups=checker.GROUPS,
                                review=self.ref('release/review.txt'), issues=[
            dict(id=number, snapshot=self.ref('release/issue-snapshot.txt'), criteria=[dict(
                id='C1', text='Synthetic criterion for test only.', scope='required', roles=sorted(checker.ROLES))])
            for number in sorted(checker.ISSUES)])
        self.write(checker.REQUIREMENTS, encoded(self.requirements))
        self.base = self.commit()
        self.acceptance = dict(format='qleisli.release-acceptance', version=1,
            requirements_sha256=checker.digest(encoded(self.requirements)), identities=checker.IDENTITIES,
            schema_registry=self.ref('lean/schema-registry.json'),
            proof_scope=dict(claim='scoped-pre-v1', ledger_sha256=self.ref(checker.LEDGER)['sha256'],
                             admitted=sorted(row['id'] for row in self.ledger['discharged_guarantees']),
                             pending=sorted(row['interpretation'] for row in self.ledger['pending_obligations'])),
            issues=[dict(id=number, criteria=[dict(id='C1', disposition='implemented', review=self.ref('release/review.txt'),
                        evidence={role: self.ref('release/evidence.txt') for role in checker.ROLES})]) for number in sorted(checker.ISSUES)])
        self.write(checker.ACCEPTANCE, encoded(self.acceptance))
        self.head = self.commit()
        self.env = dict(GITHUB_ACTIONS='true', GITHUB_REPOSITORY='MGYamada/Qleisli', GITHUB_EVENT_NAME='workflow_dispatch',
                        GITHUB_REF='refs/heads/release/test', GITHUB_RUN_ID='17', GITHUB_RUN_ATTEMPT='2',
                        GITHUB_SHA=self.head, RELEASE_READINESS='true')
        self.refresh_receipts()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.root), '-c', 'user.name=Synthetic Test',
            '-c', 'user.email=synthetic@example.invalid', '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=/dev/null',
            '-c', 'maintenance.auto=false', '-c', 'gc.auto=0', *args], stderr=subprocess.PIPE)

    def commit(self):
        self.git('add', '--all'); self.git('commit', '--quiet', '-m', 'Synthetic verification fixture')
        return self.git('rev-parse', 'HEAD').decode().strip()

    def write(self, name, data):
        path = self.root / name; path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(data)

    def ref(self, name):
        return dict(path=name, sha256=checker.digest((self.root / name).read_bytes()))

    def directory(self, job):
        return self.evidence / f'release-receipt-{job}-{self.head}-2'

    def refresh_receipts(self):
        self.env['GITHUB_SHA'] = self.head
        self.context = checker.hosted_context(self.root, self.env)
        self.needs = {'changes': dict(result='success', outputs=dict(profile='full', proof_lane='full', head=self.head))}
        self.payloads = {job: {} for job in checker.SUITES}
        proof = dict(format='qleisli.release-constitution', version=1, context=self.context,
                     ledger_sha256=self.ref(checker.LEDGER)['sha256'], result=dict(self.constitution_result(), mode='current-Lean-replay'))
        self.payloads['check-lean']['constitution.json'] = encoded(proof)
        tracked = checker.tracked_files(self.root, self.head)
        source = archive(tracked)
        crate = archive({'Cargo.toml': (self.root/'Cargo.toml').read_bytes(),
                         '.cargo_vcs_info.json': encoded({'git': {'sha1': self.head}})}, 'qleisli-0.3.0-alpha/')
        report = dict(format='qleisli.distribution-validation', version=1, status='passed',
                      candidate=dict(commit=self.head, tree=self.context['tree'], clean=True), package=dict(version='0.3.0-alpha'),
                      installed_quickstart=dict(package='qleisli', version='0.3.0-alpha', checks=['Bell check/run/sample in text and JSON', 'embedded qft2', 'reject measured-owner reuse']),
                      commands=[dict(exit_code=0)], crate=dict(sha256=checker.digest(crate)), source_archive=dict(sha256=checker.digest(source)))
        self.payloads['check-distribution'] = {'distribution.json': encoded(report), 'package.crate': crate, 'source.tar': source}
        for job, target in checker.NATIVE_JOBS.items():
            sources = {name: checker.digest(file.data) for name, file in tracked.items() if name.startswith('lean-kernel/') or name in ['scripts/check_lean_kernel.py', 'scripts/package_lean_kernel.py']}
            payload = {'bin/qleisli-kernel': b'SYNTHETIC NOT EXECUTABLE', 'LICENSE': b'Apache-2.0', 'NOTICE': b'fixture', 'lean-runtime-licenses/LICENSE': b'fixture'}
            manifest = dict(format='qleisli.native-bundle', version=1, package_version='0.3.0-alpha', protocol=checker.IDENTITIES['native_protocol'],
                            validation=dict(lane='full', fresh_replay=True), sources=sources, files={name: checker.digest(raw) for name, raw in payload.items()})
            payload['manifest.json'] = encoded(manifest)
            payload['distribution.json'] = encoded(dict(format='qleisli.kernel-distribution', version=1, source_commit=self.head,
                package_version='0.3.0-alpha', target=target, bundle_manifest_sha256=checker.digest(payload['manifest.json']),
                archive_script_sha256=self.ref('scripts/archive_lean_kernel.py')['sha256']))
            name = f'qleisli-kernel-0.3.0-alpha-{target}.tar.gz'
            raw = archive(payload, name[:-7] + '/')
            self.payloads[job] = {name: raw, name+'.sha256': f'{checker.digest(raw)}  {name}\n'.encode()}
        for job in checker.SUITES:
            self.refresh_job(job)

    def refresh_job(self, job, **updates):
        directory = self.directory(job); directory.mkdir(parents=True, exist_ok=True)
        for name, raw in self.payloads[job].items(): (directory/name).write_bytes(raw)
        receipt = dict(format='qleisli.release-job', version=1, context=self.context, job=job,
                       files={name: checker.digest(raw) for name, raw in self.payloads[job].items()})
        receipt.update(updates)
        raw = encoded(receipt); (directory/'receipt.json').write_bytes(raw)
        self.needs[job] = dict(result='success', outputs=dict(release_receipt_sha256=checker.digest(raw)))
        self.env['RELEASE_NEEDS_JSON'] = json.dumps(self.needs)

    def constitution_result(self):
        result = dict(RESULT, ledger_sha256=self.ref(checker.LEDGER)['sha256'])
        if 'supplemental_interpretations' in self.ledger:
            result['supplemental_pending_obligations'] = len(self.ledger['supplemental_interpretations'])
        return result

    def check(self):
        # Only the already separately tested expensive/version/constitutional
        # services are simulated. Artifact, Git, coverage, provenance and CLI
        # helpers remain production code. No synthetic record enters real ledger.
        with patch.object(checker, 'version_plan', return_value={}), patch('check_constitution.check_constitution', return_value=self.constitution_result()) as constitutional:
            result = checker.check(self.root, base_ref=self.base, env=self.env, evidence=self.evidence)
            constitutional.assert_called_once_with(self.root, base_ref=self.base)
            return result

    def reject(self, phrase):
        with self.assertRaisesRegex((PacketError, ValueError), phrase): self.check()

    def update_acceptance(self, mutate):
        mutate(self.acceptance); self.write(checker.ACCEPTANCE, encoded(self.acceptance)); self.head=self.commit(); self.refresh_receipts()

    def test_complete_synthetic_candidate_retains_pending_scope(self):
        result=self.check()
        self.assertEqual((result['admitted'], result['pending']), (2,3))
        self.assertEqual(result['publication'], 'not-authorized-or-performed')

    def add_exactness_supplement(self):
        # Synthetic references intentionally point to labelled synthetic review
        # bytes. The constitutional service is mocked here, never human authority.
        self.ledger['supplemental_interpretations'] = [dict(
            id='EXACT-2026-01', jurisdictions=['QS', 'PR', 'RS'],
            applies_to=['QS-2026-01', 'PR-2026-01', 'RS-2026-01'],
            adoption=self.ref('release/review.txt'), reviewed_text=self.ref('release/review.txt'),
            formalization_status='pending-coverage-and-adequacy-review',
            proof_status='not-discharged', evidence_bindings=[])]
        self.write(checker.LEDGER, encoded(self.ledger))
        self.update_acceptance(lambda x: x['proof_scope'].update(
            ledger_sha256=self.ref(checker.LEDGER)['sha256'],
            pending=['EXACT-2026-01', 'PR-2026-01', 'QS-2026-01', 'RS-2026-01']))

    def test_live_ledger_row_shapes_disclose_three_obligations_and_exactness(self):
        # Read actual production rows independently of the synthetic fixture.
        # This would fail with KeyError('id') under the old pending extraction.
        ledger = json.loads((ROOT / checker.LEDGER).read_bytes())
        disclosure = checker.proof_disclosures(ledger)
        self.assertEqual(disclosure['pending'],
                         ['EXACT-2026-01', 'PR-2026-01', 'QS-2026-01', 'RS-2026-01'])
        self.assertEqual(disclosure['admitted'],
                         ['QS-QLV1-OWNERSHIP-2026-01', 'QS-QLV1-SCOPE-2026-01'])
        self.assertEqual({row['jurisdiction'] for row in ledger['binding_interpretations']},
                         {'QS', 'PR', 'RS'})

    def test_complete_synthetic_supplement_remains_pending_and_in_live_receipt(self):
        self.add_exactness_supplement()
        result = self.check()
        self.assertEqual((result['admitted'], result['pending']), (2, 4))
        self.assertEqual(result['publication'], 'not-authorized-or-performed')
        proof = json.loads(self.payloads['check-lean']['constitution.json'])
        self.assertEqual(proof['result']['pending_obligations'], 3)
        self.assertEqual(proof['result']['supplemental_pending_obligations'], 1)
        # A pre-supplement success receipt cannot stand for the active ledger,
        # even with updated ledger digest and trusted producer digest.
        del proof['result']['supplemental_pending_obligations']
        self.payloads['check-lean']['constitution.json'] = encoded(proof)
        self.refresh_job('check-lean')
        self.reject('mismatched guarantee replay')

    def test_hidden_supplement_and_fabricated_supplement_discharge_reject(self):
        self.add_exactness_supplement()
        original = copy.deepcopy(self.acceptance)
        changes = [
            lambda scope: scope['pending'].remove('EXACT-2026-01'),
            lambda scope: scope['admitted'].append('EXACT-2026-01'),
            lambda scope: scope['pending'].append('EXACT-2026-01'),
        ]
        for change in changes:
            with self.subTest(change=change):
                self.acceptance = copy.deepcopy(original)
                self.update_acceptance(lambda x: change(x['proof_scope']))
                self.reject('proof scope')

    def test_pending_identity_scope_and_status_must_bind_actual_ledger_rows(self):
        self.add_exactness_supplement()
        changes = [
            lambda x: x['pending_obligations'][0].update(id='PR-2026-01'),
            lambda x: x['pending_obligations'][0].update(interpretation='unadopted'),
            lambda x: x['pending_obligations'].append(x['pending_obligations'][0]),
            lambda x: x['pending_obligations'][0].update(proof_status='discharged'),
            lambda x: x['supplemental_interpretations'].append(x['supplemental_interpretations'][0]),
            lambda x: x['supplemental_interpretations'][0].update(id='QS-2026-01'),
            lambda x: x['supplemental_interpretations'][0].update(applies_to=['unadopted']),
            lambda x: x['supplemental_interpretations'][0].update(jurisdictions=['EXACT']),
            lambda x: x['supplemental_interpretations'][0].update(proof_status='discharged'),
            lambda x: x['supplemental_interpretations'][0].update(evidence_bindings=[{'proof': 'invented'}]),
        ]
        for change in changes:
            with self.subTest(change=change):
                ledger = copy.deepcopy(self.ledger)
                change(ledger)
                with self.assertRaises(PacketError):
                    checker.proof_disclosures(ledger)

    def test_missing_duplicate_issue_and_removed_criterion_reject(self):
        original=copy.deepcopy(self.acceptance)
        for change in [lambda x:x['issues'].pop(), lambda x:x['issues'].append(x['issues'][0]), lambda x:x['issues'][0]['criteria'].clear()]:
            with self.subTest(change=change):
                self.acceptance=copy.deepcopy(original); self.update_acceptance(change); self.reject('ID')

    def test_prior_108_issue_candidate_cannot_omit_exactness_requirement_or_acceptance(self):
        self.assertEqual(len(checker.ISSUES), 111)
        self.assertIn(311, checker.GROUPS['G02'])
        self.omitted_issue_packet_rejects({311, 315, 317}, 108)

    def test_prior_109_issue_candidate_cannot_omit_body_derived_effect_work(self):
        self.assertIn(315, checker.GROUPS['G10'])
        self.omitted_issue_packet_rejects({315, 317}, 109)

    def test_prior_110_issue_candidate_cannot_omit_semantic_stdlib_work(self):
        self.assertIn(317, checker.GROUPS['G10'])
        self.omitted_issue_packet_rejects({317}, 110)

    def omitted_issue_packet_rejects(self, omitted, previous_count):
        current_requirements = copy.deepcopy(self.requirements)
        current_acceptance = copy.deepcopy(self.acceptance)
        previous_ids = checker.ISSUES - omitted
        self.assertEqual(len(previous_ids), previous_count)
        cases = [
            ('previous groups and criteria', True, True, '13 groups/111 Issues'),
            ('updated groups without new Issue criteria', False, True,
             'reviewed Issues: missing or unexpected IDs'),
            ('updated requirements without new Issue acceptance', False, False,
             'acceptance Issues: missing or unexpected IDs'),
        ]
        for label, old_groups, old_criteria, diagnostic in cases:
            with self.subTest(case=label):
                self.requirements = copy.deepcopy(current_requirements)
                if old_groups:
                    for group in self.requirements['groups'].values():
                        group[:] = [number for number in group if number not in omitted]
                if old_criteria:
                    self.requirements['issues'] = [row for row in self.requirements['issues']
                                                   if row['id'] not in omitted]
                    self.assertEqual({row['id'] for row in self.requirements['issues']}, previous_ids)
                self.write(checker.REQUIREMENTS, encoded(self.requirements))
                self.base = self.commit()
                self.acceptance = copy.deepcopy(current_acceptance)
                self.acceptance['issues'] = [row for row in self.acceptance['issues'] if row['id'] not in omitted]
                self.assertEqual({row['id'] for row in self.acceptance['issues']}, previous_ids)
                self.acceptance['requirements_sha256'] = checker.digest(encoded(self.requirements))
                self.write(checker.ACCEPTANCE, encoded(self.acceptance))
                self.head = self.commit()
                self.refresh_receipts()
                self.reject(diagnostic)

    def test_candidate_cannot_rewrite_criterion_or_exclude_required_work(self):
        self.update_acceptance(lambda x:x['issues'][0]['criteria'][0].update(disposition='explicit-later-version'))
        self.reject('unauthorized exclusion')
        self.write(checker.REQUIREMENTS, encoded(dict(self.requirements, issues=[])))
        self.head=self.commit(); self.refresh_receipts()
        self.reject('unauthorized exclusion')

    def test_missing_stale_evidence_and_unknown_keys_reject(self):
        self.update_acceptance(lambda x:x['issues'][0]['criteria'][0]['evidence']['positive'].update(sha256='0'*64))
        self.reject('stale evidence')
        self.acceptance['extra']='ignored?'; self.write(checker.ACCEPTANCE, encoded(self.acceptance)); self.head=self.commit(); self.refresh_receipts()
        self.reject('expected exactly')

    def test_admitted_removal_fabricated_discharge_and_hidden_pending_reject(self):
        original=copy.deepcopy(self.acceptance)
        for field, value in [('admitted',[]), ('admitted',['QS-2026-01']), ('pending',[])]:
            with self.subTest(field=field,value=value):
                self.acceptance=copy.deepcopy(original); self.update_acceptance(lambda x:x['proof_scope'].update({field:value})); self.reject('proof scope')

    def test_full_conformance_claim_rejects(self):
        self.update_acceptance(lambda x:x['proof_scope'].update(claim='full-conformance')); self.reject('full constitutional')

    def test_tests_model_lanes_and_incomplete_suites_reject(self):
        original=copy.deepcopy(self.needs)
        for lane in ['tests','model']:
            self.needs=copy.deepcopy(original); self.needs['changes']['outputs']['proof_lane']=lane; self.env['RELEASE_NEEDS_JSON']=json.dumps(self.needs); self.reject('full proof lane')
        for status in ['skipped','cancelled','failure']:
            self.needs=copy.deepcopy(original); self.needs['check-rust']['result']=status; self.env['RELEASE_NEEDS_JSON']=json.dumps(self.needs); self.reject('check-rust')
        self.needs=copy.deepcopy(original); del self.needs['check-rust']; self.env['RELEASE_NEEDS_JSON']=json.dumps(self.needs); self.reject('validation dependency')

    def test_wrong_commit_run_attempt_and_digest_reject(self):
        for key in ['commit','tree','run_id','attempt']:
            with self.subTest(key=key):
                self.refresh_job('check-rust', context=dict(self.context, **{key:'wrong'})); self.reject('identity')
        self.refresh_job('check-rust'); (self.directory('check-rust')/'receipt.json').write_bytes(b'{}'); self.reject('producer digest')

    def test_failure_created_report_and_source_only_receipt_reject(self):
        job='check-distribution'; data=json.loads(self.payloads[job]['distribution.json']); data['status']='failed'
        self.payloads[job]['distribution.json']=encoded(data); self.refresh_job(job); self.reject('distribution report')
        self.refresh_receipts(); job='check-lean'; data=json.loads(self.payloads[job]['constitution.json']); data['result']['mode']='source-identity-only'
        self.payloads[job]['constitution.json']=encoded(data); self.refresh_job(job); self.reject('source-only')

    def test_missing_and_corrupted_native_assets_reject(self):
        job='check-lean-kernel'; name=next(iter(self.payloads[job])); original=copy.deepcopy(self.payloads[job])
        del self.payloads[job][name]; self.refresh_job(job); self.reject('native assets')
        self.payloads[job]=original; self.payloads[job][name]+=b'corrupt'; self.refresh_job(job); self.reject('checksum')

    def test_native_source_commit_and_version_mismatch_reject(self):
        job='check-lean-kernel'; name=next(iter(self.payloads[job])); original=self.payloads[job][name]
        for field, value in [('source_commit','0'*40), ('package_version','0.2.9')]:
            payload={key:file.data for key,file in checker.archive_bytes(original,prefix=name[:-7]).items()}
            record=json.loads(payload['distribution.json']); record[field]=value; payload['distribution.json']=encoded(record)
            raw=archive(payload,name[:-7]+'/'); self.payloads[job]={name:raw,name+'.sha256':f'{checker.digest(raw)}  {name}\n'.encode()}; self.refresh_job(job); self.reject('source/version/target')

    def test_receipt_path_escape_and_symlink_reject(self):
        self.refresh_job('check-rust',files={'../escape':'0'*64}); self.reject('path must')
        self.refresh_job('check-rust'); path=self.directory('check-rust')/'receipt.json'; raw=path.read_bytes(); path.unlink(); target=Path(self.temp.name)/'outside'; target.write_bytes(raw); path.symlink_to(target); self.reject('cannot read')

    def test_changed_record_during_check_rejects(self):
        original=checker.artifacts
        def changing(*args):
            original(*args)
            path=self.directory('check-lean')/'constitution.json'; path.write_bytes(path.read_bytes()+b' ')
        with patch.object(checker,'artifacts',side_effect=changing): self.reject('changed during checking')

    def test_dirty_candidate_and_trusted_sha_mismatch_reject(self):
        self.env['GITHUB_SHA']='0'*40; self.reject('hosted commit')
        self.env['GITHUB_SHA']=self.head; self.write('untracked.txt',b'new'); self.reject('candidate is dirty')

    def test_ignored_file_cannot_supply_candidate_evidence(self):
        self.write('.gitignore',b'ignored-evidence.txt\n')
        self.write('ignored-evidence.txt',b'not part of the candidate commit')
        self.update_acceptance(lambda x:x['issues'][0]['criteria'][0]['evidence'].update(positive=self.ref('ignored-evidence.txt')))
        self.reject('exact tracked Git blob')

    def test_wrong_tag_manual_request_and_untrusted_digest_reject(self):
        self.env.update(GITHUB_EVENT_NAME='push',GITHUB_REF='refs/tags/v0.2.9')
        self.reject('tag and product version')
        self.env.update(GITHUB_EVENT_NAME='workflow_dispatch',RELEASE_READINESS='false')
        self.reject('explicitly requested')
        self.env['RELEASE_READINESS']='true'
        del self.needs['check-lean']['outputs']['release_receipt_sha256']
        self.env['RELEASE_NEEDS_JSON']=json.dumps(self.needs)
        self.reject('missing trusted producer digest')

    def test_unknown_fields_duplicate_json_and_schema_coercions_reject(self):
        original=copy.deepcopy(self.acceptance)
        for field,value in [('version', True), ('identities', dict(checker.IDENTITIES,qrate_schema='2')),
                            ('command',['sh','arbitrary'])]:
            with self.subTest(field=field):
                self.acceptance=copy.deepcopy(original); self.update_acceptance(lambda x:x.update({field:value})); self.reject('unknown|coordinates|exactly')
        self.write(checker.ACCEPTANCE,b'{"format": "qleisli.release-acceptance", "format": "duplicate"}')
        self.head=self.commit(); self.refresh_receipts(); self.reject('duplicate JSON field')

    def test_live_receipt_uses_fixed_verifier_and_rechecks_inputs(self):
        path=Path(self.temp.name)/'live.json'
        bound_result = dict(self.constitution_result(), mode='current-Lean-replay')
        with patch('check_constitution.check_constitution',return_value=bound_result) as verifier:
            checker.record_constitution(self.root,path,self.env)
            verifier.assert_called_once_with(self.root,verify_lean=True)
        record=json.loads(path.read_bytes())
        self.assertEqual(record['ledger_sha256'],self.ref(checker.LEDGER)['sha256'])
        self.assertEqual(record['result']['ledger_sha256'],record['ledger_sha256'])
        self.assertEqual(record['result']['mode'],'current-Lean-replay')
        with self.assertRaisesRegex(PacketError,'outside candidate'):
            checker.record_constitution(self.root,self.root/'bad-output.json',self.env)
        def change(*args,**kwargs):
            self.write(checker.LEDGER,b'{}')
            return bound_result
        with patch('check_constitution.check_constitution',side_effect=change), self.assertRaisesRegex(ValueError,'candidate is dirty'):
            checker.record_constitution(self.root,Path(self.temp.name)/'changed.json',self.env)

    def test_live_producer_rejects_missing_or_different_validated_ledger_digest(self):
        bound = dict(self.constitution_result(), mode='current-Lean-replay')
        other_bytes = (self.root / checker.LEDGER).read_bytes() + b'\n'
        for digest in [None, checker.digest(other_bytes)]:
            result = dict(bound)
            if digest is None:
                del result['ledger_sha256']
            else:
                result['ledger_sha256'] = digest
            output = Path(self.temp.name) / ('missing.json' if digest is None else 'different.json')
            with self.subTest(digest=digest), patch('check_constitution.check_constitution', return_value=result):
                with self.assertRaisesRegex(PacketError, 'validated different ledger bytes'):
                    checker.record_constitution(self.root, output, self.env)
                self.assertFalse(output.exists(), 'a mismatched validation must not create a receipt')

    def test_readiness_rejects_temporary_validator_ledger_even_with_matching_receipt(self):
        self.add_exactness_supplement()
        bound = self.constitution_result()
        # The simulated validator inspected a different byte identity while the
        # outer candidate and both before/after reads stayed unchanged. Counts
        # and a mutually consistent producer receipt cannot bridge this gap.
        other_bytes = (self.root / checker.LEDGER).read_bytes() + b'\n'
        for digest in [None, checker.digest(other_bytes)]:
            result = dict(bound)
            if digest is None:
                del result['ledger_sha256']
            else:
                result['ledger_sha256'] = digest
            proof = json.loads(self.payloads['check-lean']['constitution.json'])
            proof['result'] = dict(result, mode='current-Lean-replay')
            self.payloads['check-lean']['constitution.json'] = encoded(proof)
            self.refresh_job('check-lean')
            with self.subTest(digest=digest), patch.object(checker, 'version_plan', return_value={}), \
                    patch('check_constitution.check_constitution', return_value=result):
                with self.assertRaisesRegex(PacketError, 'validated different ledger bytes'):
                    checker.check(self.root, base_ref=self.base, env=self.env, evidence=self.evidence)

    def cli(self, *args, env=None):
        # Preserve OS/tool lookup, but supply trust context only from this test.
        # An empty override must not re-import the caller's hosted CI context.
        actual={key:value for key,value in os.environ.items() if not key.startswith(('GITHUB_','RELEASE_'))}
        actual.update(self.env if env is None else env)
        return subprocess.run([sys.executable,str(SCRIPT),'--root',str(self.root),*args],env=actual,capture_output=True,text=True)

    def test_actual_cli_rejects_missing_context_and_unreviewed_requirements(self):
        # Reproduce ambient PR-job variables even when this suite runs locally.
        ambient=dict(self.env,GITHUB_EVENT_NAME='pull_request',GITHUB_REF='refs/pull/1/merge',
                     GITHUB_JOB='check-docs',RELEASE_TRUSTED_BASE=self.base)
        with patch.dict(os.environ,ambient):
            result=self.cli('--base-ref',self.base,env={})
        self.assertNotEqual(result.returncode,0); self.assertIn('trusted same-run',result.stderr)
        self.git('rm',checker.REQUIREMENTS); empty=self.commit(); self.head=empty; self.env['GITHUB_SHA']=empty
        result=self.cli('--base-ref',empty); self.assertNotEqual(result.returncode,0); self.assertIn('missing reviewed release/requirements.json',result.stderr)

    def test_actual_cli_producer_binds_bytes_and_rejects_wrong_job(self):
        output=Path(self.temp.name)/'producer'; env=dict(self.env,GITHUB_JOB='check-rust',GITHUB_OUTPUT=str(Path(self.temp.name)/'outputs'))
        result=self.cli('--record-job','check-rust','--output',str(output),env=env); self.assertEqual(result.returncode,0,result.stderr)
        raw=(output/'receipt.json').read_bytes(); self.assertEqual(Path(env['GITHUB_OUTPUT']).read_text(),f'release_receipt_sha256={checker.digest(raw)}\n')
        result=self.cli('--record-job','check-docs','--output',str(output),env=env); self.assertNotEqual(result.returncode,0); self.assertIn('wrong producer',result.stderr)

    def test_legacy_cli_delegates_instead_of_pending_obligation_placeholder(self):
        script=ROOT/'scripts/check_constitution.py'
        env={key:value for key,value in os.environ.items() if not key.startswith(('GITHUB_','RELEASE_'))}
        result=subprocess.run([sys.executable,str(script),'--require-release-ready'],env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode,1); self.assertIn('trusted base',result.stderr); self.assertNotIn('three broader binding interpretations remain pending',result.stderr)

    def test_workflow_runs_final_gate_and_trusted_producer_outputs(self):
        text=(ROOT/'.github/workflows/ci.yml').read_text()
        docs=text.split('  check-docs:\n')[1].split('  required:\n')[0]
        self.assertNotIn('--require-release-ready',docs)
        final=text.split('  release-readiness:\n')[1]
        for job in checker.SUITES:
            self.assertIn(job,final.split('    steps:')[0])
            self.assertIn(f'--record-job {job}',text)
            block=re.split(r'(?m)^  [a-z][a-z-]*:\n', text.split(f'  {job}:\n')[1])[0]
            self.assertIn('steps.release-receipt.outputs.release_receipt_sha256',block)
        self.assertIn('RELEASE_NEEDS_JSON: ${{ toJSON(needs) }}',final)
        self.assertIn('inputs.release_base || vars.QLEISLI_RELEASE_BASE',final)
        self.assertIn('release-receipt-*-${{ github.sha }}-${{ github.run_attempt }}',final)
        self.assertNotIn('run-id:',final)
        self.assertIn('--record-constitution',text)
        self.assertIn('inputs.release_readiness',final)


if __name__=='__main__':
    unittest.main()
