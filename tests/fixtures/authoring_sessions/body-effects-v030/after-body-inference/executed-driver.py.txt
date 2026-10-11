"""Observe frozen first programs; never execute commands read from a record."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CLI = Path("/private/tmp/qleisli-bounded-validation-target/debug/qleisli")
NATIVE = ROOT / "lean-kernel/.lake/build/bin/qleisli-kernel"
OUT = HERE / "after-body-inference"
OUT.mkdir()
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
files = json.loads((HERE / "first-files.json").read_text())["files"]
assert all(digest(HERE / name) == expected for name, expected in files.items())
wrapper = HERE / "native-log.py"
wrapper.chmod(0o755)
inputs = {"cli_sha256":digest(CLI),"native_sha256":digest(NATIVE),"wrapper_sha256":digest(wrapper),"first_manifest_sha256":digest(HERE / "first-files.json"),"rust_sources":{str(p.relative_to(ROOT)):digest(p) for p in sorted((ROOT/"src").rglob("*.rs"))}}
(OUT / "inputs.json").write_text(json.dumps(inputs,indent=2)+"\n")
(OUT / "executed-driver.py.txt").write_bytes(Path(__file__).read_bytes())
rows, observations = [], []
for folder in sorted((HERE / "attempt-01").iterdir()):
    name = folder.name
    finite = name in {"bad-iso-reset","finite-lift-permutation","finite-lift-expansion"}
    argv = [str(CLI),"check",str(folder),"--format=json"] if finite else [str(CLI),"check","--entry=main::f",f"--module=main={folder/'main.qli'}","--format=json"]
    if name in {"zero-fold-observation","dead-static-observation","recursive-observation"}:
        argv.append("--nat=n=0")
    if name in {"generic-access","generic-missing-access"}:
        argv.extend(["--type=A=Bit","--operation=U=main::flip"])
    log = OUT / (name + ".native.jsonl")
    log.write_bytes(b"")
    env = dict(os.environ,QLEISLI_KERNEL=str(wrapper),QLEISLI_HIERARCHY_KERNEL=str(wrapper),QLEISLI_STUDY_NATIVE_LOG=str(log),QLEISLI_STUDY_NATIVE=str(NATIVE))
    started=time.monotonic()
    result=subprocess.run(argv,cwd=ROOT,env=env,capture_output=True,timeout=30)
    (OUT/(name+".stdout.txt")).write_bytes(result.stdout)
    (OUT/(name+".stderr.txt")).write_bytes(result.stderr)
    data=json.loads(result.stdout)
    calls=len(log.read_text().splitlines())
    record={"command":argv,"exit_code":result.returncode,"stdout":data,"native_invocations":calls,"seconds":time.monotonic()-started,"recorded_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"timestamp_note":"Clock observation after completion; not authenticated provenance."}
    observation="observations/after-body-inference-"+name+".json"
    (HERE / "observations").mkdir(exist_ok=True)
    (HERE / observation).write_text(json.dumps(record,indent=2,ensure_ascii=False)+"\n")
    observations.append(observation)
    row={"case":name,"exit_code":result.returncode,"native_invocations":calls,"codes":[d["code"] for d in data["diagnostics"]]}
    rows.append(row)
    print(json.dumps(row),flush=True)
stable=all(digest(HERE/name)==expected for name,expected in files.items()) and digest(CLI)==inputs["cli_sha256"] and digest(NATIVE)==inputs["native_sha256"]
(OUT / "result.json").write_text(json.dumps({"results":rows,"sources_and_executables_stable":stable,"scope":"Actual observations after body inference; no numerical/source-preservation proof or Issue completion."},indent=2)+"\n")
session=json.loads((HERE / "session.json").read_text())
session["attempts"][0]["observations"].extend(observations)
session["follow_up_note"]="Same immutable first sources after body inference. Baseline observations preserved; follow-up outcomes do not retroactively alter first attempts."
(HERE / "session.json").write_text(json.dumps(session,indent=2)+"\n")
assert stable
