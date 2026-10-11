"""Freeze informed desired sources before any #315 checking experiment.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ATTEMPT = HERE / "attempt-01"
ATTEMPT.mkdir()
CASES = {
    "plain-unitary": "use std::quantum::h; pub fn f(q:Q<Bit>)->Q<Bit>{h(q)}",
    "plain-preparation": "use std::quantum::init0; pub fn f()->Q<Bit>{init0()}",
    "plain-observation": "use std::observe::measure_z; pub fn f(q:Q<Bit>)->Bit{measure_z(q)}",
    "wide-iso-caller": "iso fn g(q:Q<Bit>)->Q<Bit>{q} pub unitary fn f(q:Q<Bit>)->Q<Bit>{g(q)}",
    "wide-observe-caller": "observe fn g(q:Q<Bit>)->Q<Bit>{q} pub unitary fn f(q:Q<Bit>)->Q<Bit>{g(q)}",
    "bad-unitary-observation": "use std::observe::measure_z; pub unitary fn f(q:Q<Bit>)->Bit{measure_z(q)}",
    "bad-iso-reset": "use std::observe::reset; pub iso fn f(q:Q<Bit>)->Q<Bit>{reset(q)} observe fn main()->Unit{()}",
    "zero-fold-observation": "use std::quantum::init0; use std::observe::measure_z; fn tap(q:Q<Bit>)->Q<Bit>{let a=init0();let b=measure_z(a);q} pub fn f[static n:Nat](q:Q<Bit>)->Q<Bit> requires n<=1 {for static i in 0..n carry a=q {yield tap(a)}}",
    "dead-static-observation": "use std::quantum::init0; use std::observe::measure_z; pub fn f[static n:Nat](q:Q<Bit>)->Q<Bit> requires n<=1 {if static n==0 {q} else {let a=init0();let b=measure_z(a);q}}",
    "generic-access": "use std::quantum::x; pub fn flip(q:Q<Bit>)->Q<Bit>{x(q)} pub fn f[static A:Basis,static U:Op<A>](q:Q<A>)->Q<A> requires Apply(U){U(q)}",
    "generic-missing-access": "use std::quantum::x; pub fn flip(q:Q<Bit>)->Q<Bit>{x(q)} pub fn f[static A:Basis,static U:Op<A>](q:Q<A>)->Q<A>{U(q)}",
    "ordinary-copy": "pub fn f(x:Bit)->(Bit,Bit){(x,x)}",
    "scalar-unit": "use std::quantum::phase_eighth; pub fn f(q:Q<Unit>)->Q<Unit>{phase_eighth(q)}",
    "duplicate-owner": "pub fn f(q:Q<Bit>)->(Q<Bit>,Q<Bit>){(q,q)}",
    "primitive-like-local-name": "fn init0(q:Q<Bit>)->Q<Bit>{q} pub fn f(q:Q<Bit>)->Q<Bit>{init0(q)}",
    "finite-lift-permutation": "pub fn f(q:Q<Bit>)->Q<Bit>{do x <- q; pure not x} observe fn main()->Unit{()}",
    "finite-lift-expansion": "pub fn f(q:Q<Unit>)->Q<Bit>{do x <- q; pure 0} observe fn main()->Unit{()}",
    "recursive-observation": "use std::quantum::init0; use std::observe::measure_z; pub fn f[static n:Nat](q:Q<Bit>)->Q<Bit> requires n<=1 {if static n==0 {let a=init0();let b=measure_z(a);q} else {f[n-1](q)}}",
    "mutual-cycle": "fn g(q:Q<Bit>)->Q<Bit>{f(q)} pub fn f(q:Q<Bit>)->Q<Bit>{g(q)}",
    "unit-introduction": "use std::quantum::{unit,finish}; pub fn f()->Unit{finish(unit(()))}",
}
source_hashes = {}
files = {}
for name, source in CASES.items():
    folder = ATTEMPT / name
    folder.mkdir()
    (folder / "main.qli").write_text(source + "\n")
    (folder / "Qargo.toml").write_text('schema-version = 2\n[qrate]\nname = "body-effects-' + name + '"\nversion = "0.3.0-alpha"\nedition = "2026"\n[source]\nroot = "."\n')
    for path in sorted(folder.iterdir()):
        key = str(path.relative_to(HERE))
        files[key] = hashlib.sha256(path.read_bytes()).hexdigest()
    source_hashes[name + "/main.qli"] = files["attempt-01/" + name + "/main.qli"]
session = {"format":1,"kind":"informed_first_attempt","task":"Body-derived principal effects and checked annotation assertions for Issue #315", "baseline_commit":"21a488024b278fecf0ea5e43be6cc2e846bcc3fe","project_version":"0.3.0-alpha","author":"Codex; informed repository context; deployed model/sampling unavailable","context":"context.md","attempts":[{"id":"attempt-01","reason":"Twenty desired/control/counterexample sources frozen before checking. No compiler change yet; first outcomes remain to be observed.","sha256":source_hashes,"observations":[]}]}
(HERE / "session.json").write_text(json.dumps(session,indent=2)+"\n")
(HERE / "first-files.json").write_text(json.dumps({"files":files,"claim":"Complete first source/manifest identity before observation, not proof or model benchmark."},indent=2)+"\n")
print(json.dumps({"programs":len(CASES),"files":len(files),"manifest_sha256":hashlib.sha256((HERE/'first-files.json').read_bytes()).hexdigest()}))
