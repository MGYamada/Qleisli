"""Bind both Rust producer dependencies before independently reading their artifacts.

The caller supplies the current workflow's trusted context and needs outputs.
Arbitrary JSON does not authenticate CI. Returned digests are expected inputs
for artifact verification, not suite success or Qleisli acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
"""
import re

RUST_SUITES = {'latest': 'check-rust', 'msrv': 'check-rust-msrv'}
COMMIT = re.compile(r'[0-9a-f]{40}\Z')
SHA = re.compile(r'[0-9a-f]{64}\Z')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def producer_jobs(profile):
    require(type(profile) is str and profile in RUST_SUITES, 'unknown Rust producer profile')
    return {role: RUST_SUITES[profile] + '-' + role for role in ('differential', 'remaining')}


def validate_context(context):
    fields = {'repository', 'commit', 'tree', 'run_id', 'attempt', 'event'}
    require(type(context) is dict and set(context) == fields
            and all(type(value) is str for value in context.values()), 'invalid Rust producer context')
    require(context['repository'] == 'MGYamada/Qleisli'
            and context['event'] in {'push', 'pull_request', 'workflow_dispatch'}, 'unexpected Rust hosted context')
    require(all(COMMIT.fullmatch(context[key]) for key in ('commit', 'tree')), 'invalid Rust source identity')
    require(all(re.fullmatch(r'[1-9][0-9]*', context[key]) for key in ('run_id', 'attempt')),
            'invalid Rust run identity')


def expected_producer_receipts(needs, profile, context):
    """Reject missing, failed or stale pair dependencies; return both bound hashes.

    Reading and independently validating the corresponding receipt/artifact bytes
    remains mandatory. A successful dependency alone cannot replace that step.
    """
    validate_context(context)
    jobs = producer_jobs(profile)
    require(type(needs) is dict and set(needs) == {'changes', *jobs.values()},
            'missing or unexpected Rust producer dependency')
    selected = needs['changes']
    require(type(selected) is dict and selected.get('result') == 'success', 'Rust selection failed')
    outputs = selected.get('outputs')
    require(type(outputs) is dict and outputs.get('head') == context['commit']
            and outputs.get('profile') == 'full' and type(outputs.get('proof_lane')) is str
            and outputs['proof_lane'] in {'tests', 'model', 'full'}, 'wrong Rust selection source/profile')
    expected = {}
    for role, job in jobs.items():
        result = needs[job]
        require(type(result) is dict and result.get('result') == 'success', f'{job}: producer did not succeed')
        outputs = result.get('outputs')
        require(type(outputs) is dict, f'{job}: missing producer outputs')
        for output, field in [('source_head', 'commit'), ('source_tree', 'tree'),
                              ('source_run_id', 'run_id'), ('source_attempt', 'attempt')]:
            require(outputs.get(output) == context[field], f'{job}: wrong {field}')
        value = outputs.get('rust_receipt_sha256')
        require(type(value) is str and SHA.fullmatch(value), f'{job}: missing producer receipt digest')
        expected[role] = dict(job=job, sha256=value)
    return expected
