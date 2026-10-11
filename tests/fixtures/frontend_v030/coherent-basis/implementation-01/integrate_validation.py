from pathlib import Path
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone

ROOT = Path('/Users/masa/git/Qleisli')
BASE = ROOT / 'tests/fixtures/frontend_v030/coherent-basis/implementation-01'
OUT = BASE / 'integration-validation-01.json'
assert not OUT.exists(), 'Preserve the first integration record'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def binding(relative):
    path = ROOT / relative
    assert path.is_file(), relative
    return {'path': relative, 'sha256': digest(path)}

records = {}
for name in (
    'rust-latest-01', 'rust-latest-repair-02', 'rust-msrv-01',
    'sized-source-latest-01', 'sized-source-msrv-01',
    'bit-flip-reference-01', 'semantic-contract-example-01',
    'clippy-latest-final-02', 'clippy-msrv-final-02',
    'format-latest-final-02', 'selector-regressions-01',
    'constitution-continuity-01', 'documentation-policy-final-03',
    'mdbook-contract-final-04', 'book-links-contract-final-04'):
    path = BASE / (name + '.json')
    record = json.loads(path.read_text())
    assert record['exit_code'] == (101 if name == 'rust-latest-01' else 0)
    for stream in record.get('streams', {}).values():
        assert digest(ROOT / stream['path']) == stream['sha256']
    records[name] = {**binding(path.relative_to(ROOT).as_posix()),
                     'exit_code': record['exit_code'], 'seconds': record['seconds']}

build = json.loads((BASE / 'build-latest-01.json').read_text())
assert all(digest(ROOT / p) == h for p, h in build['source_sha256'].items())
cli = Path('/private/tmp/qleisli-bounded-validation-target/debug/qleisli')
assert digest(cli) == build['binary_sha256']
native = ROOT / 'lean-kernel/.lake/build/bin/qleisli-kernel'
assert digest(native) == '39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85'

oracles = []
for case, probes in (('pennylane_demos-vqe_excitation', 528),
                     ('qualtran-less_than2', 2080)):
    prefix = 'corpus/migrations/coherent-basis-v030/independent-oracle/' + case
    observation = json.loads((ROOT / prefix / 'observation.json').read_text())
    report = json.loads((ROOT / prefix / 'report.json').read_text())
    assert report['status'] == 'passed' and not report['failures']
    assert len(report['cases']) == 1 and report['cases'][0]['semantic_probes'] == probes
    assert observation['identities_unchanged'] and observation['report_sha256'] == digest(ROOT / prefix / 'report.json')
    oracles.append({'case': case, 'expected_probes': probes,
                    'observation': binding(prefix + '/observation.json'),
                    'report_binding': binding(prefix + '/report.json'),
                    'exit_code': observation['exit_code'], 'report_content': report})
    assert observation['exit_code'] == 0

changed = subprocess.check_output(['git', 'diff', '--name-only'], cwd=ROOT, text=True).splitlines()
assert [p for p in changed if p.startswith('src/')] == ['src/frontend/parser.rs']
assert not any(p.startswith(('lean/', 'lean-kernel/', 'governance/')) for p in changed)
source_bindings = {p: digest(ROOT / p) for p in changed}
for p in ('docs/src/reference/coherent-basis.md',
          'tests/fixtures/frontend_v030/coherent-basis/source-map.json',
          'tests/fixtures/frontend_v030/coherent-basis/scope-decision.json',
          'tests/fixtures/authoring_sessions/coherent-basis-v030/session.json'):
    source_bindings[p] = digest(ROOT / p)

evidence = [
    'build-latest-01.json', 'parser-ast-comparison-01.json',
    'docs-validation-01.json', 'docs-validation-02.json',
    'docs-reference-review-03.json', 'docs-independent-parser-migration-review-01.json',
    'test-diagnostic-repairs-01.json', 'verification-inventory-review-02.json',
    'previous-head-ci-hosted-review-02.json']
record = {
    'format': 'qleisli.coherent-basis-integration-validation', 'version': 1,
    'issue': 81, 'recorded_utc': datetime.now(timezone.utc).isoformat(),
    'checkout_head_before_integration': subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'status': 'bounded-unit-validation-complete',
    'records': records,
    'additional_evidence': [binding((BASE / p).relative_to(ROOT).as_posix()) for p in evidence],
    'current_source_bindings': source_bindings,
    'cli_sha256': digest(cli), 'native_sha256': digest(native),
    'source_binary_binding': 'All captured src/**/*.rs build inputs still match. Build and binary identities are local observations, not compiler/runtime proofs.',
    'rust': {
        'latest': {'unique_passed_across_stages': 301,
                   'first_sweep': '239 passed and one stale tuple-tree diagnostic assertion failed; tuple suite repaired and rerun in full. Later sized-source stale text assertion repaired and its full suite rerun.',
                   'successful_followups': {'tuple_unit_corpus': 29, 'sized_source': 38, 'bit_flip_reference': 2},
                   'deduplication': 'The first sweep\'s seven passed tuple tests reappear in the eight-test repair suite and count once.',
                   'complete_single_sweep_claimed': False},
        'msrv_1_85': {'passed': 170, 'initial_targets': 132, 'sized_source': 38},
        'existing_ignored': 'Three native-only sized-source tests on each Rust version remain ignored; not newly skipped by this migration.',
        'explicit_stress_exclusions': 'Existing 8192/3000 source-generator stress cases: three filters on latest and one on MSRV. No new maximum-system case generated or executed.',
        'cargo_clippy': 'Both supported Rust versions: all-targets with -D warnings passed after the final assertion repair.'},
    'source_study': {
        'before': binding('tests/fixtures/authoring_sessions/coherent-basis-v030/observations-before/capture.json'),
        'after': binding('tests/fixtures/authoring_sessions/coherent-basis-v030/observations-after/capture.json'),
        'initial_analysis': binding('tests/fixtures/authoring_sessions/coherent-basis-v030/analysis-after-01.json'),
        'supplement': binding('tests/fixtures/authoring_sessions/coherent-basis-v030/analysis-after-02.json'),
        'actual_after_commands': 57, 'initial_assertions': {'passed': 64, 'failed': 1},
        'supplementary_assertions': {'passed': 7, 'failed': 0},
        'first_failure': 'Independent authored numerical oracle omitted structural join; subsequent ordered-axis concatenation added without source repair or rewriting the first result.',
        'preservation': 'Three supported desired controls reproduce the original QIRF bytes and distributions. Five finite semantic refusals persist. Independent small complex action checks preserve +1 maps, ordered permutation and reference/phase interference.',
        'selected_correction': 'Original private main entry commands encountered visibility; four appended public entries reach current CoherentLift projection refusal. No OLD public-entry observation is invented.'},
    'migration': {'explicit_file_derivatives': 48, 'normalized_full_ast_matches': 48,
                  'normalization': 'Only source spans erased; all other AST structure compared.',
                  'corpus_old_current_commands': 12, 'corpus_snapshots': 2,
                  'corpus_observation': binding('corpus/migrations/coherent-basis-v030/observations-after/capture.json'),
                  'original_integrity': binding('corpus/migrations/coherent-basis-v030/final-integrity.json'),
                  'independent_oracles': oracles},
    'documentation': {'mdbook': '0.5.4', 'generated_html_files': 25,
                      'local_links': 1012, 'anchors': 377,
                      'scope': 'Final explicit no-Monad/do criterion14 sentence compiled and generated links checked; earlier raw TeX/rendering and copied-README failures preserved.'},
    'human_scope': binding('tests/fixtures/frontend_v030/coherent-basis/scope-decision.json'),
    'previous_hosted_ci': {
        'run': 37410058344, 'branch_head': '73355382a3db94893982e5954e9400fffcd7f48e',
        'actual_pr_merge_test_commit': '7e768e6ccdbb98077818664f985886bb5a86a374',
        'rust_latest_and_msrv': 'Both failed the stale sized_source canonical-type text expectation; current candidate repairs it and passes full38-test suite on each Rust version.',
        'distribution': 'Extracted source-production offline all-targets test exited101. Its internal logs/14.stderr was unavailable; underlying cause remains unverified. No same-candidate distribution/full-CI success claimed.'},
    'scope_limits': [
        'External qargo/qlippy diagnostics explicitly excluded by the maintainer; not validated.',
        'Selected concrete CoherentLift and existing finite quantum-Unit limitations remain.',
        'No native checker/schema/AST semantics, Lean proofs, protected guarantees, dependency versions or edition changed.',
        'No fresh local Lean build/audit/replay, full CI completion, fresh installation, release approval, tag or publication.',
        'Bounded tests, AST equality and accepted IR are not general source/runtime preservation, full QS/PR/quantitative RS or new guarantee admission.',
        'A separately preserved #82 study, if present in the working directory, is not part of this unit.'
    ]}
OUT.write_text(json.dumps(record, indent=2) + '\n')
print(OUT.relative_to(ROOT), digest(OUT))
