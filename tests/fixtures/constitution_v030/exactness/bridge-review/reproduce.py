#!/usr/bin/env python3
"""Small explicit-mock regression, not hosted provenance or a Lean/human claim.

Use the existing disposable SyntheticRelease fixture and the actual release
checker. Its constitutional service, version plan, hosted context, build
receipts and release acceptance are explicitly simulated by that fixture.
The service reports validating distinct bytes with a fourth pending supplement;
outer captured/final ledger bytes omit it. Before the bridge fix the counts and
receipt agree with that service while the release disclosure omits the row.
"""
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path('/Users/masa/git/Qleisli')
sys.path.insert(0, str(ROOT / 'scripts'))
import test_check_release_ready as suite

case = suite.SyntheticRelease()
case.setUp()
try:
    outer_bytes = (case.root / suite.checker.LEDGER).read_bytes()
    validated = copy.deepcopy(case.ledger)
    validated['supplemental_interpretations'] = [dict(
        id='EXACT-2026-01', jurisdictions=['QS', 'PR', 'RS'],
        applies_to=['QS-2026-01', 'PR-2026-01', 'RS-2026-01'],
        adoption=case.ref('release/review.txt'),
        reviewed_text=case.ref('release/review.txt'),
        formalization_status='pending-coverage-and-adequacy-review',
        proof_status='not-discharged', evidence_bindings=[])]
    validated_bytes = suite.encoded(validated)
    service_result = dict(suite.RESULT, supplemental_pending_obligations=1,
                         ledger_sha256=hashlib.sha256(validated_bytes).hexdigest())
    case.constitution_result = lambda: dict(service_result)
    case.refresh_receipts()
    result = dict(scope='explicit mocked constitutional service; no real release/proof/adoption claim',
                  captured_ledger_sha256=hashlib.sha256(outer_bytes).hexdigest(),
                  validated_ledger_sha256=service_result['ledger_sha256'],
                  inner_result=service_result)
    try:
        result['outcome'] = 'accepted'
        result['release_result'] = case.check()
    except Exception as error:
        result['outcome'] = 'rejected'
        result['exception'] = type(error).__name__
        result['message'] = str(error)
    result['final_ledger_unchanged'] = (case.root / suite.checker.LEDGER).read_bytes() == outer_bytes
    print(json.dumps(result, indent=2, sort_keys=True))
finally:
    case.doCleanups()
