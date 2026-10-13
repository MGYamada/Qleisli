#!/usr/bin/env python3
import sys,subprocess,struct,json
from pathlib import Path
data=sys.stdin.buffer.read()
record={'args':sys.argv[1:],'magic':data[:4].decode('ascii','replace')}
if data[:4]==b'QLV2' and len(data)>=24:
 scope,a,g,c,n=struct.unpack('<IIIII',data[4:24]);original=data[24:24+a]
 record.update(scope=scope,graph_bytes=g,caller_bytes=c,aliases=n)
 if original[:4]==b'QLV1':
  body_length,request_length=struct.unpack('<II',original[4:12])
  record['request_bytes']=request_length
  if request_length:
   request=json.loads(original[12+body_length:].decode())
   record['request_format']=request.get('format');record['request_kind']=request.get('kind')
with Path(__file__).with_suffix('.jsonl').open('a') as out:out.write(json.dumps(record)+'\n')
result=subprocess.run(['/tmp/qleisli-beta-362-qlv2-stable-kernel',*sys.argv[1:]],input=data,capture_output=True)
sys.stdout.buffer.write(result.stdout);sys.stderr.buffer.write(result.stderr)
raise SystemExit(result.returncode)
