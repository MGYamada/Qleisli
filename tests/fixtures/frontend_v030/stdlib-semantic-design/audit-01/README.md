# Read-only semantic stdlib migration audit

This additive packet prepares the atomic ordinary #317 unit after the common
checker is committed. It changes no source, public API, docs, harness selector,
map, license or existing packet. No build, test, CLI, native, fixture driver,
metadata-argv replay, Git or GitHub mutation was performed. File reads, `rg`,
local parsing/counting and hashes are the only observations here. The retained
before-code Issue snapshot is not a fresh GitHub read. This is non-normative
planning, with no acceptance-criteria credit, adoption, guarantee, proof or
release result. I authored the preceding common checker; this audit is not an
independent validation of that implementation.

The trusted constitutional continuity guard earlier in this same review context
passed against faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2. Both limited ordinary
QLV1 guarantees retain their scope. Broader QS/PR/RS and EXACT proof/enforcement
remain pending. Edition 2026, native rules, dependencies and corpus intake do
not change. No new Guardian interpretation is proposed or exercised.

## All current ordinary definitions

The four real sources contain **12 public definitions: 10 runtime functions and
2 Basis functions**, plus private Basis helper `nonzero2`. Thus the recorded
#317 table's ten runtime items is correct but not the full ordinary-library
inventory. The two unchanged `std::basis` items must remain visible in the
final public taxonomy. None of these 13 declarations is a sealed primitive.
Type notation below abbreviates B=Bit while preserving parentheses and owners.
Each runtime statement describes its contract, not a fresh theorem discharge.

| Current public identity / contract ID | Exact current contract and full interface | Recorded disposition |
| --- | --- | --- |
| arithmetic::increment2 / A001 | Q<(B,B)> -> same; y -> y+1 mod4, every coefficient +1; first leaf weight1, overflow wraps; no scratch/observation | Local examples/test modules, no canonical std export or old-path alias |
| arithmetic::add2 / A002 | Q<((B,B),(B,B))> -> same; (x,y) -> (x,x+y mod4), coefficient +1, x preserved, both pairs little-endian; no input promise/scratch | Local examples/test modules, no canonical std export |
| arithmetic::mul2_mod15 / A003 | Q<((B,B),(B,B))> -> same; y<15 maps2y mod15 and15 fixes15, coefficient +1; leaves weights1,2,4,8 and returned route(d,a,b,c) | Local order-finding/example/test module; preserve full-space value15 extension |
| transforms::qft2 / F001 | Q<(B,B)> -> same; F4[y,x]=exp(+2pi i xy/4)/2, E2(a,b)=a+2b, included reversal, fixed scalar phase | transform::qft2, subordinate to generic qft family with explicit ordered encoding correspondence |
| transforms::qft3 / F002 | Q<((B,B),B)> -> same; F8[y,x]=exp(+2pi i xy/8)/sqrt8, E3((a,b),c)=a+2b+4c, included reversal | transform::qft3, same subordinate rule; qft4 is not currently implemented |
| routines::hadamard2 / R001 | Q<(B,B)> -> same; H tensor H, unchanged leaf order, all inputs/references, no auxiliary | transform::hadamard2 |
| routines::reflect_uniform2 / R002 | Q<(B,B)> -> same; 2P_++-I with exact sign; protected computed auxiliary has all-input exact cleanup obligation | reflection::reflect_uniform2; move private nonzero2 with it, do not expose helper |
| routines::measure_x / R003 | Q<B> -> B; complete destructive instrument K_b=bra(b) H, reported X eigenvalue(-1)^b, input owner consumed | measurement::measure_x |
| routines::measure_z2 / R004 | Q<(B,B)> -> (B,B); K_ab=bra(a) tensor bra(b), full destructive ordered Z instrument, both owners consumed | measurement::measure_z2 |
| routines::parity_zz / R005 | (Q<B>,Q<B>) -> ((Q<B>,Q<B>),B); K_s=(I+(-1)^s Z tensor Z)/2, data owners retained/coherence within parity sectors, internal zero meter measured/consumed | measurement::parity_zz |
| basis::xor2 / B001 | (B,B) -> B; total x xor y, noninjective on four-label input; no quantum owner/measurement | Keep basis::xor2; coherent enclosing injectivity remains a separate obligation |
| basis::and2 / B002 | (B,B) -> B; total x and y, noninjective; a predicate for reversible XOR-computation, not a quantum instruction | Keep basis::and2 |

Private `nonzero2((a,b))=not(not a and not b)` is 0 at00 and1 elsewhere. Z on
its computed flag induces diag(+1,-1,-1,-1)=2P_00-I. Conjugating by H tensor H
produces the standard reflection above. The licensed Qualtran reflection2 is
**I-2P_++**, its exact negative. Preserve that distinction in active manifest,
README and controlled interference tests; a rename cannot erase scalar phase.
Separate returned owners never imply a product state. The measurement formulas
are unnormalized outcome-indexed actions tensored with reference identity,
not only sampled probabilities.

A001/F001/etc. are preserved identifiers in source comments. They do not
identify a newly checked standalone contract ledger or a discharged guarantee;
retired prose is not restored by this audit. Current source equations,
STDLIB.md, Reference and independent test expectations are separate inputs.

## Semantic admission and future identity

The existing ordinary #317 record selects these rules; this audit does not
adopt new names or forms:

- arithmetic: reusable parameterized arithmetic/number theory, independent of
  one fixed demonstration. Reserve modexp<N> as an intended shape and
  primefact<N> as the v1 factorization identity; neither is an available API.
- transform: named exact basis transforms with full phase/coordinate equations.
  Its canonical Fourier family is positive F_N on Q<Bits<N>>, N>=0, with axis0
  least significant, included reversal, no observation/auxiliary, same owner.
  N=0 is exact +1 identity on Q<Bits<0>>, distinct from Q<Unit> and zero owners.
- reflection: phase-fixed 2P-I with the projector, sign and reference contract
  explicit. The negative licensed reflection remains a separate contract.
- measurement: complete outcome-indexed instruments, explicit consumed/retained
  owners and ordered classical encoding; distinct from compiler-owned observe.
- basis: total finite Basis-label maps, ordinary checked source. Noninjectivity
  may be legitimate here and does not grant coherent-lift evidence.

Names denote the mathematics; algorithm selection is separate policy. Generic
family identities own the canonical name, fixed specializations remain
subordinate where retained. Existing static declaration/call spelling is
the declaration `qft[static N:Nat]` and specialization `qft[N]` applied to `q`;
angle brackets express semantic identity, not an implemented source call syntax. No aliases for retired arithmetic, transforms
or routines have a demonstrated requirement in the inspected record.

Foundation catalog accounting remains distinct: **27 sealed names**, grouped
quantum18, observe3, registers4, classical2. The catalogs' concrete subsets are
still finite17/selected18. Their admission rules describe exact gate/owner
structure, complete observation/reset/discard, exact ordered register
extraction/insertion/empty owners, and ordinary classical value construction,
respectively. `phase_eighth` is scalar zeta I, not T=diag(1,zeta). `unit`,
`finish`, empty register owners and nested Toffoli shape keep their exact
contracts. The singular mathematical-namespace convention does not by itself
rename existing sealed foundation paths or create another primitive catalog.

## Concrete integration barrier before generic embedding

Current finite compile/mod.rs::process_loaded_project_details performs the
complete common judgment first, then profile-checks **every declaration**,
then selects the native kernel and performs concrete construction/checking.
compile/profile.rs still rejects static Nat, Bits, static folds/conditions and
unsupported concrete forms. Embedding generic qft in the ordinary transform
module alone would therefore cause finite projects to refuse even an unused
qft definition. The source checker is no longer the missing component, but
concrete public-path integration is still required.

The next ordinary #32/#317 contract must resolve this precisely before code:
keep mandatory complete original declaration/body/kind/owner/effect checking;
keep real native checking of unused closed concrete definitions; keep requested
unsupported concrete specializations as located refusals. This audit chooses
no unchecked pass flag, skip policy, privileged qft injection, fallback or
profile-filtered source AST. Finite and selected use the same retained original
sources and checked facts, but their concrete capabilities remain different.

Current selected projection of existing qif/Basis/Meaning bodies can remain
unsupported when requested, after their original source checks. Rehoming does
not make them materializable, and a family name cannot replace an unsupported
body with a known operator. Strict opaque Op/static/host provider paths,
conservative Apply/Adjoint/Controlled masks, pending Meaning/injectivity/clean/
provider obligations and native acceptance remain intact. The existing target
phase-domain/work limits still refuse unsupported exact instances; no rounding
or matcher waiver follows from a generic definition.

## Atomic migration inventory

migration-inventory.json records exact matching lines and explicit indirect
module/count/selector dependencies. It contains **55 active/dependency files**
and **22 retained current fixture files**. The 99-row selected input map and
separate 5-row actual declaration/manifest map bind this read-only observation;
they are not a whole compiled source attestation or full historical inventory.

- Registry/loaders: source.rs changes the ordinary entries and include_str paths
  together; project/sized count and byte policies follow the actual new registry.
  Removing arithmetic and splitting routines into reflection/measurement while
  merging hadamard2 into transform can preserve four modules (basis,transform,
  reflection,measurement); do not make this count authoritative before actual
  chosen helpers/files are finalized. An empty reserved arithmetic source is
  not required merely to reserve its future mathematical meaning.
- Active examples: phase_estimation and operation_algorithms estimation import
  singular transform; grover/bernstein_vazirani use transform and measurement;
  bit_flip_code uses measurement; order_finding gets a local exact mul2_mod15
  module plus transform. New local arithmetic modules must also be copied by
  tests/order_finding.rs helpers; deleting imports alone loses the tests.
- Live Rust source strings/assertions: algorithms, static_operations,
  order_finding, static_semantics, repair_diagnostics, review_v024, project,
  editions, documentation and body_effects carry direct old paths/module counts.
  Preserve their independent equations and negative categories. The misplaced
  routines::qft2 input is intentionally invalid; update its positive suggested
  path, not by making an alias. Basis/parser tests remain foundation controls.
- Packaging/discovery: README's qlidoc command and STDLIB.md source links, the
  Reference's catalog/admission table, documentation include_str lists,
  body-derived effect exports and fresh-install embedded-qft2 test must agree.
  stdlib/docs/README.md currently claims product0.2.3 while the manifest is
  0.3.0-alpha; repair this active statement without rewriting its historical
  observed qargo integration paragraph into a new test success.
- Active licensed corpus derivatives: qualtran/qft2,qualtran/qpe2,
  qualtran/reflection2, quantum_katas/grover2,quantum_katas/qpe3 and
  pennylane_demos/qpe3 import old paths. Use an additive provenance-aware
  migration layer; preserve original intake/attempt sources and pinned upstream
  files. corpus/manifest.json and reflection2 README contain the phase-sign
  relation and need accurate current-name presentation; do not rewrite old
  validation metadata to claim it checked new library dependencies.
- Retained but currently selected fixtures: 18 files under ordinary-type-cutover/
  current plus4 under ordinary-type-client-integration/current reference old
  paths. They are captured prior migration inputs and must stay byte-identical.
  Create new namespace derivatives, record exact old/new hashes and complete
  companion sources/manifests, then explicitly retarget qli_corpus,
  authoring_ergonomics,sampling and current_source_fixtures selection. Old maps
  and the earlier selected derivatives do not silently become mutable.

All authoring FIRST sources, session JSON, before/after snapshots, raw results,
upstream commits/hashes, native fixtures and immutable adoption records stay
unchanged. In particular qft-family-v030 and qft-exact-request-v030 are local
licensed studies, not canonical standard sources or authorization to rewrite
those packets. No retired docs-old prose is restored. Keep Apache/MIT allocation,
Google/Microsoft/PennyLane notices and Masahiko G. Yamada attribution; the
copied generic Fourier body must retain its actual Google+translation header.

## Next bounded mechanical closure

After the next ordinary before-code contract and independent review, preserve
new desired canonical sources and first genuine diagnostics before any code.
Exercise actual public project and selected routes, ordinary source origin,
all unused/private bodies, reserved-std injection refusals and absence of the
retired public exports. Check generic QFT only N=0,1,2,3, and retained fixed2/3
through explicit tuple/Bits encodings against independent full complex Fourier
entries and unchanged exact native requests. N=0 keeps its independently chosen
single owner Bits0 identity-rewire contract; do not use named qft0 or adapt the
request after observing a different shape. Preserve phase/axis/reversal/provider
faults and failed operational observations. Existing small arithmetic and
measurement/reference controls retain their full contracts; no new maximum
quantum case is generated. Fresh native validity, requested conformance,
finite numerical evidence and analytic/source-preservation proofs remain
separate. No all-input or generic-family theorem follows from bounded probes.

The retained #152 alignment keeps all twelve criteria and the0.4.0 target. Its
later structural/re-export/tooling work consumes the frozen0.3.0 identities,
admission rules and correspondences; it cannot resurrect routines or incidental
arithmetic APIs, change phase/effects, or infer trust from placement. This audit
resolves no #152 work and claims none of #317's24 criteria complete. Root owns
the next implementation/adoption/publication decisions and actual validation.
