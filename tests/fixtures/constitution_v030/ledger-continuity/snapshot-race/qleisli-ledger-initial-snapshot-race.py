"""Read-timing-only v4 frozen-snapshot counterexample in an isolated fixture root."""
import hashlib
import json
import sys
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
PROJECT = Path('/Users/masa/git/Qleisli')
sys.path.insert(0, str(PROJECT / 'scripts'))
import check_constitution as checker
import check_ratification_packet as packet
from test_check_constitution import ConstitutionalRecords

case = ConstitutionalRecords('test_recorded_identity_is_not_release_readiness_or_independent_authentication')
case.setUp()
try:
    path = case.root / 'CONSTITUTION.md'
    original = path.read_bytes()
    changed = original + b'\nUnapproved retained change.\n'
    path.write_bytes(changed)
    real_checked_file = packet.checked_file
    reads = []

    def timed_read(root, name, digest):
        if name != 'CONSTITUTION.md':
            return real_checked_file(root, name, digest)
        # Model a concurrent writer exposing valid bytes only while this read
        # occurs. The real hash checker still reads and validates those bytes.
        path.write_bytes(original)
        try:
            result = real_checked_file(root, name, digest)
            reads.append(name)
            return result
        finally:
            path.write_bytes(changed)

    error = None
    result = None
    with patch.object(checker, 'checked_file', side_effect=timed_read), \
            patch.object(packet, 'checked_file', side_effect=timed_read):
        try:
            result = checker.check_constitution(case.root)
        except packet.PacketError as caught:
            error = str(caught)
    print(json.dumps({
        'kind': 'initial-v4-enforcer-defect-not-proof-or-admission-counterexample',
        'checker_sha256': hashlib.sha256((PROJECT / 'scripts/check_constitution.py').read_bytes()).hexdigest(),
        'helper_sha256': hashlib.sha256((PROJECT / 'scripts/check_guarantee_ledger.py').read_bytes()).hexdigest(),
        'original_constitution_sha256': hashlib.sha256(original).hexdigest(),
        'retained_constitution_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'constitution_check_reads': len(reads),
        'final_invalid_constitution_retained': path.read_bytes() == changed,
        'result': result,
        'error': error,
        'accepted_invalid_frozen_snapshot': result is not None and path.read_bytes() == changed,
        'scope': 'Only checked-file timing is mocked; validation still uses real checked_file and the actual fixed initial verifier. All file writes occur in the temporary fixture root. No Lean or project file is modified.'
    }, indent=2))
finally:
    case.doCleanups()
