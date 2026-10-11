from pathlib import Path
import hashlib,json,subprocess
root=Path('/Users/masa/git/Qleisli'); fix=root/'tests/fixtures/frontend_v030/ordinary-classical-types/initial-study'
cases=[]
def add(name,text,goal,legacy=False): cases.append(dict(name=name,text=text+'\n',desired_property=goal,legacy_control=legacy))
def pair(name,source,legacy,goal):
 add(name+'-desired',source,goal);add(name+'-legacy',legacy,'Legacy control for '+goal,True)
pair('ordinary-bit','pub unitary fn main(b: Bit) -> Bit { b }','pub unitary fn main(b: CBit) -> CBit { b }','An ordinary Bit is copyable and is not a Q owner.')
pair('ordinary-word','pub unitary fn main(b: Bits<2>) -> Bits<2> { b }','pub unitary fn main(b: CBits<2>) -> CBits<2> { b }','Ordinary word type is Bits<2>; profile lowering may remain explicitly unsupported.')
pair('unit','pub unitary fn main(u: Unit) -> Unit { u }','pub unitary fn main(u: ()) -> () { u }','Ordinary Unit is one common exact type; legacy empty tuple type syntax migrates.')
pair('literal','pub unitary fn main() -> Bit { 0 }','pub unitary fn main() -> CBit { false }','One 0/1 Bit literal spelling; no preparation or readout implied.')
pair('boolean-flow','pub unitary fn main(a: Bit,b: Bit) -> Bit { if not a and b { 1 } else { 0 } }','pub unitary fn main(a: CBit,b: CBit) -> CBit { if not a and b { true } else { false } }','Runtime Boolean operations and branching over ordinary values retain effects and evaluation order.')
pair('measure-bit','use std::observe::measure_z; pub observe fn main(q: Q<Bit>) -> Bit { measure_z(q) }','use std::observe::measure_z; pub observe fn main(q: Q<Bit>) -> CBit { measure_z(q) }','Measurement consumes the Q owner and explicitly returns an ordinary Bit with Observe effect.')
pair('measure-word','use std::observe::measure_z; use std::classical::empty_bits; use std::classical::prepend_bit; pub observe fn main(q: Q<Bit>) -> Bits<1> { prepend_bit[0](measure_z(q),empty_bits()) }','use std::observe::measure_z; use std::classical::empty_bits; use std::classical::prepend_bit; pub observe fn main(q: Q<Bit>) -> CBits<1> { prepend_bit[0](measure_z(q),empty_bits()) }','Retain the already implemented one-bit hierarchy readout packing and low-axis-first order.')
pair('copy-word','pub unitary fn main(b: Bits<2>) -> (Bits<2>,Bits<2>) { (b,b) }','pub unitary fn main(b: CBits<2>) -> (CBits<2>,CBits<2>) { (b,b) }','Ordinary word copy is allowed independently of quantum owner uniqueness.')
pair('drop-bit','pub unitary fn main(b: Bit) -> Unit { b; () }','pub unitary fn main(b: CBit) -> () { b; () }','Ordinary drop is legal; the value () denotes Unit.')
pair('read-coercion','pub unitary fn main(q: Q<Bit>) -> Bit { q }','pub unitary fn main(q: Q<Bit>) -> CBit { q }','Reject implicit readout rather than inferring measurement from the return type.')
pair('prepare-coercion','pub unitary fn main(b: Bit) -> Q<Bit> { b }','pub unitary fn main(b: CBit) -> Q<Bit> { b }','Reject implicit preparation rather than inferring it from the return type.')
pair('runtime-natural','pub unitary fn main(n: Bits<1>,q: Q<Bits<n>>) -> Q<Bits<n>> { q }','pub unitary fn main(n: CBits<1>,q: Q<Bits<n>>) -> Q<Bits<n>> { q }','Runtime values cannot supply static sizes even when names and widths match.')
add('quantum-unit-identity','pub unitary fn main(q: Q<Unit>) -> Q<Unit> { q }','Q<Unit> remains an owner; no sized support is assumed.')
add('quantum-unit-copy','pub unitary fn main(q: Q<Unit>) -> (Q<Unit>,Q<Unit>) { (q,q) }','Reject duplicate zero-wire quantum owner.')
add('quantum-unit-drop','pub unitary fn main(q: Q<Unit>) -> Unit { () }','Reject implicit loss of zero-wire quantum owner.')
add('quantum-bit-copy','pub unitary fn main(q: Q<Bit>) -> (Q<Bit>,Q<Bit>) { (q,q) }','Reject duplicate quantum owner in both existing profiles.')
add('quantum-width-equality','pub unitary fn main(q: Q<Bits<1>>) -> Q<Bit> { q }','Bit and Bits<1> retain exact constructor identity despite equal widths.')
add('ordinary-width-equality','pub unitary fn main(b: CBits<1>) -> CBit { b }','Legacy control: ordinary Bit and Bits<1> retain exact constructor identity.',True)
add('empty-word-vs-unit','pub unitary fn main(b: CBits<0>) -> () { b }','Legacy control: zero-bit word does not equal empty tuple/Unit.',True)
add('nested-owner','pub unitary fn main(q: Q<Q<Bit>>) -> Q<Q<Bit>> { q }','Basis of Q cannot itself contain Q.')
add('bit-numeral-two','pub unitary fn main() -> Bit { 2 }','Reject non-Bit numeral rather than expected-type coercion or modulo conversion.')
add('basis-runtime-reuse','basis fn flip(b: Bit) -> Bit { not b } pub unitary fn main(b: CBit) -> CBit { flip(b) }','Observe current staging restriction; do not assume general cross-stage basis reuse for this cutover.',True)
assert len(cases)==34
for c in cases:
 d=fix/c['name'];d.mkdir(); (d/'main.qli').write_text(c.pop('text'));(d/'Qargo.toml').write_text('schema-version = 2\n\n[qrate]\nedition = "2026"\n')
 c['sources']={str(p.relative_to(fix)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.iterdir()}
paths=list((root/'src/frontend').rglob('*.rs'))+[root/'Cargo.toml',root/'Cargo.lock']
session=dict(format='qleisli.ordinary-classical-type-study',version=1,status='sources-preserved-before-execution',head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip(),cases=cases,source_identity={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},scope='34 bounded syntax/type/owner/profile cases; no native acceptance or source-preservation assertion; at most two declared qubits; no source edits.')
(fix/'session.json').write_text(json.dumps(session,indent=2)+'\n')
print('Preserved',len(cases),'source cases before running their observer.')
