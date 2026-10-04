from pathlib import Path
import hashlib,json,re,subprocess,collections
root=Path('/Users/masa/git/Qleisli');fix=root/'tests/fixtures/frontend_v030/ordinary-classical-types'; rows=[]
paths=subprocess.check_output(['git','ls-files'],cwd=root).decode().splitlines()
for path in paths:
 p=root/path
 if not p.is_file() or p.suffix not in ('.qli','.rs','.py','.md'):continue
 if path.startswith('tests/fixtures/frontend_v030/ordinary-classical-types/'):continue
 raw=p.read_bytes()
 try:text=raw.decode()
 except UnicodeDecodeError:continue
 counts={word:len(re.findall(r'\b'+word+r'\b',text)) for word in ('CBit','CBits')}
 if p.suffix=='.qli':
  counts.update({word:len(re.findall(r'\b'+word+r'\b',text)) for word in ('true','false')})
 if not any(counts.values()):continue
 if p.suffix=='.qli':
  if path.startswith('stdlib/'):category='active-stdlib'
  elif path.startswith('examples/'):category='active-examples'
  elif path.startswith('corpus/authoring/'):category='historical-corpus-authoring'
  elif path.startswith(('corpus/negative/','corpus/semantic_faults/')):category='active-corpus-counterexamples'
  elif path.startswith('corpus/'):category='active-corpus'
  elif path.startswith('tests/fixtures/'):category='fixture-candidates-require-harness-classification'
  else:category='other-source'
 elif p.suffix=='.rs' and path.startswith('src/'):category='production-rust'
 elif p.suffix=='.rs':category='rust-tests-or-clients'
 elif p.suffix=='.py':category='python-script-or-client'
 elif path.startswith('docs/src/'):category='current-book-documentation'
 elif path.startswith('tests/fixtures/'):category='fixture-documentation-preserve-history'
 else:category='other-documentation'
 rows.append(dict(path=path,category=category,text_occurrences=counts,sha256=hashlib.sha256(raw).hexdigest()))
summary=dict(collections.Counter(r['category'] for r in rows))
(fix/'migration-candidates.json').write_text(json.dumps(dict(scope='Tracked-file text-match candidate inventory, not an instruction to rewrite all matches. Comments/diagnostics/internal port tags may remain distinct; fixture inputs require explicit current/historical harness classification before edits.',summary_file_counts=summary,files=rows),indent=2)+'\n')
print(json.dumps(summary,indent=2))
