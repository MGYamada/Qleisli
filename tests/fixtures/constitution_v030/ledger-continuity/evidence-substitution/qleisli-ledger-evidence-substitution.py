"""Bounded read-timing probe of the live-evidence/ledger dispatch connection."""
import hashlib,json,sys
from pathlib import Path
from unittest.mock import patch
sys.dont_write_bytecode=True
PROJECT=Path('/Users/masa/git/Qleisli')
sys.path.insert(0,str(PROJECT/'scripts'))
import check_constitution as checker
import check_initial_guarantees as initial
from check_ratification_packet import PacketError
from test_check_constitution import ConstitutionalRecords
case=ConstitutionalRecords('test_recorded_identity_is_not_release_readiness_or_independent_authentication');case.setUp()
try:
 path=case.root/checker.CURRENT_PATH; original=path.read_bytes(); changed=json.loads(original)
 changed['validation']['source_revision']['sha256']='0'*64
 bad=json.dumps(changed).encode(); path.write_bytes(bad)
 ledger=json.loads((case.root/checker.LEDGER_PATH).read_bytes());ledger['current_bindings'][0]['evidence']['sha256']=hashlib.sha256(bad).hexdigest()
 case.write_json(checker.LEDGER_PATH,ledger)
 real_read=initial.read_file; reads=[]
 def timed_read(root,name):
  if name!=checker.CURRENT_PATH:return real_read(root,name)
  path.write_bytes(original)
  try:
   data=real_read(root,name);reads.append(hashlib.sha256(data).hexdigest());return data
  finally:path.write_bytes(bad)
 error=None;result=None
 with patch.object(initial,'read_file',side_effect=timed_read):
  try:result=checker.check_constitution(case.root)
  except PacketError as caught:error=str(caught)
 print(json.dumps({'kind':'mutable-evidence-dispatch-substitution-probe','result':result,'error':error,'profile_input_digests':reads,'ledger_input_digest':ledger['current_bindings'][0]['evidence']['sha256'],'retained_invalid_evidence':path.read_bytes()==bad,'accepted_invalid_snapshot':result is not None and path.read_bytes()==bad,'source_files':{p:hashlib.sha256((PROJECT/p).read_bytes()).hexdigest() for p in ['scripts/check_constitution.py','scripts/check_guarantee_ledger.py','scripts/check_initial_guarantees.py']},'scope':'Only timing of the actual initial checker read_file is mocked; validation and fixed verifier otherwise execute normally in an isolated historical-source fixture. No repository or Lean file is mutated.'},indent=2))
finally:case.doCleanups()
