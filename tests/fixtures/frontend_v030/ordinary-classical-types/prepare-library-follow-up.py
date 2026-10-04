from pathlib import Path
import hashlib,json
fix=Path('/Users/masa/git/Qleisli/tests/fixtures/frontend_v030/ordinary-classical-types'); old=fix/'initial-study'; new=fix/'library-study';new.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
session=json.loads((old/'session.json').read_text());cases=[]
for case in session['cases']:
 name=case['name'];d=new/name;d.mkdir(); source=old/name/'main.qli';(d/'main.qli').write_text(source.read_text().replace('fn main(', 'fn f('));(d/'Qargo.toml').write_bytes((old/name/'Qargo.toml').read_bytes())
 cases.append(dict(name=name,original=f'../initial-study/{name}/main.qli',original_sha256=sha(source),change='Rename runtime function main to f only, avoiding finite main entry policy so generic body/type diagnostics are observed. The sized host entry is explicitly main::f.',sources={str(p.relative_to(new)):sha(p) for p in d.iterdir()}))
s=(old/'observer.rs').read_text().replace('"main::main"','"main::f"');(new/'observer.rs').write_text(s)
session.update(status='separate-library-sources-preserved-before-execution',cases=cases,scope='Follow-up library observation after initial study revealed main entry restrictions obscuring generic type/body diagnostics. Original sources and outputs retained.')
(new/'session.json').write_text(json.dumps(session,indent=2)+'\n')
