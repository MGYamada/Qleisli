# Standard-library semantic namespaces

The **standard library** is the `std` [qrate](packages-and-artifacts.md) that
an official Qleisli distribution bundles. It consists of ordinary checked
`.qli` source. A **semantic namespace** is a top-level namespace of `std`,
such as `std::gate`. Each semantic namespace admits a public member by one
mathematical admission rule.

Use this chapter to find where a library function lives and what its
contract is. The chapter is normative for edition 2026. It specifies the
canonical distribution version, the naming and admission rules, the contract
of every public definition, and the retired paths. It is subordinate to the
[authority hierarchy](authority.md) and the
[primitive boundary](primitive-boundary.md).

The chapter specifies intended contracts. A namespace, a source comment or a
successful source check is not a proof of a mathematical implementation.
When you meet a derived abstraction that you do not know, the
[inference and discovery boundary](architecture.md#inference-and-explicit-discovery)
specifies how it leads to its contract and to ordinary source.

## Canonical distribution version

A toolchain and its standard library are distributed as one pair. This
section says which `std` belongs to a toolchain and how the loader checks
the pair.

The **product version** of a toolchain is its complete version identifier,
including every prerelease and build suffix. The **canonical `std`** of a
toolchain is the `std` qrate whose version equals that product version. The
compiler embeds the source and the manifest of that qrate. The
**embedded-manifest gate** is the check that the loader applies to the
embedded manifest.

Rules:

- An official Qleisli distribution must bundle exactly one canonical `std`
  qrate. Qleisli `0.3.0-beta` requires `std` `0.3.0-beta`.
- The equality covers every prerelease and build suffix. A range, a string
  that needs whitespace trimming, or a different suffix cannot satisfy it.
- A manifest must write the canonical version string without the `v` prefix
  of a release tag.
- A source program receives the embedded `std` without declaring a separate
  standard-library dependency.
- To use an older or a newer canonical `std`, a user must select the
  corresponding Qleisli toolchain.
- A user qrate keeps its own version. That version need not match Qleisli.
- The embedded manifest must declare schema 2, edition `"2026"`, the string
  `[qrate].name = "std"` and a string `[qrate].version` equal to the product
  version. The name and the version are the identity fields. The gate
  rejects an identity field that is missing, that is not a string or that
  does not match. It does so with the code `project`, before the loader
  loads the bundle.
- The schema check and the edition check precede the identity check. Their
  diagnostics are those of any manifest.

The pairing couples `std` to the toolchain for distribution and for
compatibility. It gives `std` no semantic privilege: `std` is ordinary
checked source. The
[qrate and artifact Reference](packages-and-artifacts.md#canonical-std-and-the-selected-toolchain)
specifies the coupling between canonical `std` and the toolchain.

For the product version `0.3.0-beta`, the embedded-manifest gate gives these
results:

| Embedded `[qrate].version` | Result |
| --- | --- |
| `"0.3.0-beta"` | Accepted |
| `"0.2.9"` or `"0.3.1"` | Rejected |
| `"0.3.0"` | Rejected |
| `"0.3.0-other"` | Rejected |
| `"v0.3.0-beta"` | Rejected |
| `"0.3.0-beta "`, with a trailing space | Rejected |
| `"0.3.0-beta+different"` | Rejected |
| A missing version, or the integer `17` | Rejected |

A user manifest that carries any of these values is accepted, because a user
qrate keeps its own version.

> **Implementation note.** The private function `check_bundled` in
> `src/frontend/project/edition.rs` is the embedded-manifest gate. It compares
> the version with the compiler's complete `CARGO_PKG_VERSION`. It parses the
> immutable embedded manifest once and caches only that packaging result
> across loads. A user manifest gets a fresh schema and edition check on every
> load. The gate caches no source, Meaning or native acceptance judgment.

## Names follow mathematical meaning

A canonical name states the mathematical meaning of an operation. It tells a
caller what the operation computes, not how an implementation computes it.

Rules:

- The canonical name of a mathematical stdlib function must describe what the
  operation computes.
- The name must not put the history, a benchmark, a decomposition or an
  algorithm of an implementation in place of that meaning.
- When a caller needs a choice of algorithm, that choice belongs in an
  explicit parameter, policy or configuration layer. This rule specifies no
  policy syntax and no supported implementation.
- A top-level mathematical namespace prefers a singular noun that names a
  semantic concept.
- Every public operation has one canonical home, and that home has a semantic
  admission rule. `routines`, `utils`, `helpers`, `misc` or an equally empty
  collection is not a mathematical classification.
- The layout of the source files does not determine membership.
- A genuine parameterized mathematical family owns its canonical semantic API
  identity. A fixed-size name describes its own bounded contract. It cannot
  replace the identity of the family.
- A reserved identity is not an available API. It is no evidence of
  specialization correspondence.

`qft2` and `qft3` are fixed-size names, and their contracts are supported
fixed interfaces. [Status and limits](#status-and-limits) states that generic
QFT is excluded.

## Admission rules

Each namespace admits a public API by one rule. Read the table to decide
where an API belongs, or to learn what the members of a namespace have in
common.

| Namespace | An API belongs here if and only if ... | Ordinary source |
| --- | --- | --- |
| `std::basis` | Its defining contract is a total finite map on ordinary basis labels, with no quantum owner transition and no observation. Coherent use must satisfy the separate obligations of the enclosing construction. | `stdlib/src/basis.qli` |
| `std::transform` | Its defining contract is a mathematical basis transform with an explicit whole-input operator and ordered coordinates, such as a Hadamard or a Fourier transformation. A contract defined as a reflection about a subspace belongs in `reflection`. A measurement belongs in `measurement`. | `stdlib/src/transform.qli` |
| `std::reflection` | Its defining contract is a phase-fixed reflection about a specified state or subspace, including the exact projector, the sign and the owner interface. Being unitary alone is not this classification. | `stdlib/src/reflection.qli` |
| `std::measurement` | Its defining mathematical operation is a complete measurement instrument with declared classical outcomes and residual quantum owners. This includes a destructive measurement and a measurement that retains data. An arbitrary observing routine is not enough. | `stdlib/src/measurement.qli` |
| `std::gate` | It is an ordinary checked gate definition with an exact operator, a scalar phase and an ordered-owner contract. Gate membership confers no primitive authority and no verifier authority. | `stdlib/src/gate.qli` |
| `std::state` | Its defining contract explicitly prepares a state, or replaces an owned state under a complete effect and reference contract. Pure preparation and observation-bearing reset are distinct. | `stdlib/src/state.qli` |
| `std::structure` | It is an ordinary checked structural map that explicitly changes an owner partition or a representation order. Its exact input and output trees and its axis map are part of the contract. It is not a physical gate merely because it denotes a permutation. | `stdlib/src/structure.qli` |
| `std::arithmetic` (reserved) | Its public identity is a reusable parameterized arithmetic or number-theoretic operation whose contract is independent of one hard-coded circuit instance. | None: the namespace has no bundled module and no public export. |

### Reserved arithmetic identities

The reserved namespace `std::arithmetic` holds two design identities. The
design sets these names aside. Neither is an operation that a program can
call.

| Reserved identity | Meaning |
| --- | --- |
| `std::arithmetic::modexp<N>` | The reserved shape of modular exponentiation |
| `std::arithmetic::primefact<N>` | The v1 semantic identity of prime factorization |

Rules:

- `shor<N>` is an algorithm name. It is not the canonical mathematical API of
  prime factorization.
- A reserved identity is a design identity. It is not callable syntax, a
  commitment to a generic-parameter syntax, or a delivered operation.

### Language primitives

Language primitives are bare typed identities of the language. They are not
part of the standard library, and this section says how the two relate. The
[primitive boundary](primitive-boundary.md) specifies all 13 retained
identities, the 27-entry migration and the concrete profile limits.

Rules:

- Name resolution selects a language primitive only after lexical bindings and
  after ordinary declarations and imports.
- A language primitive is not a standard-library export, and the primitives
  are not a prelude.
- `std::quantum`, `std::observe`, `std::registers` and `std::classical` are
  retired without aliases.
- An ordinary module, including `std::basis`, has no primitive privilege.

## Inventory

The standard library has 8 bundled ordinary modules. They expose 26 public
definitions and 6 transparent prelude reexports, and they contain 5 private
helpers.

| Module | Public definitions | Private helpers |
| --- | --- | --- |
| `std::basis` | 2: `xor2`, `and2` | None |
| `std::transform` | 3: `hadamard2`, `qft2`, `qft3` | `bit_identity`, a fixed Bit identity |
| `std::reflection` | 1: `reflect_uniform2` | `nonzero2`, a classical predicate |
| `std::measurement` | 3: `measure_x`, `measure_z2`, `parity_zz` | None |
| `std::gate` | 11: `id`, `x`, `z`, `s`, `sdg`, `t`, `tdg`, `cnot`, `toffoli`, `controlled_phase`, `swap` | `scalar_eighth`, a scalar phase; `phase_leaf`, a parameterized phase; `cnot_pair`, a packed CNOT |
| `std::state` | 2: `init0`, `reset` | None |
| `std::structure` | 4: `permute_axes`, `transpose_axes`, `empty`, `consume_empty` | None |
| `std::prelude` | None. The module reexports `id`, `x`, `z`, `t` and `cnot` of `std::gate`, and `init0` of `std::state`. | None |

The [prelude and import quick reference](prelude.md#quick-reference) lists
the six reexported members, their lookup priority and the explicit opt-out.

Rules:

- A contract identifier, such as B001 or R003, names a source contract. It is
  not a constitutional ledger entry and not a verification badge.

## Interfaces and contracts

This section gives the contract of every public definition, one namespace at
a time. Each table quotes the header of a declaration as its source file
writes it. A header describes an interface. It is not a function type.

Rules:

- A public quantum function has an explicit effect contract, which the
  checker checks under the order `Unitary <= Isometry <= Observe`. The
  checker checks the body of the function independently.
- An external caller uses the public effect. Inference within the same module
  keeps its precision and any further external boundary.
- Bundled source and user source follow the
  [same effect rules](source-text.md#ordinary-function-effects-and-assertions).
- A classical function has a total ordinary meaning. It may receive ordinary
  runtime values, including Bits that a program has already measured.
- A classical function preserves the effects of its evaluated arguments. It
  cannot inspect a live quantum owner.
- The truth table of a classical function grants no quantum preparation, no
  observation, no inverse or control access and no evidence of coherent
  injectivity. Coherent use keeps its separate checks.
- Every quantum contract applies to an arbitrary permitted input, tensored
  with the identity on an external reference.
- Separate owners may be entangled with each other or with a reference.
- No measurement result authorizes an implicit discard, a clean release, or
  inverse or controlled access.

### `std::basis`

| Path | Declaration | Contract |
| --- | --- | --- |
| `std::basis::xor2` | `pub classical fn xor2(x: Bit, y: Bit) -> Bit` | B001: total XOR on the four pairs of input labels. The map is not injective on the product domain. |
| `std::basis::and2` | `pub classical fn and2(x: Bit, y: Bit) -> Bit` | B002: total AND on the four pairs of input labels. The map is not injective on the product domain. |

Each function takes two arguments, not one pair.

### `std::transform`

| Path | Declaration | Contract |
| --- | --- | --- |
| `std::transform::hadamard2` | `pub unitary fn hadamard2(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)>` | R001: ordered H tensor H |
| `std::transform::qft2` | `pub unitary fn qft2(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)>` | F001: positive F4 with included reversal |
| `std::transform::qft3` | `pub unitary fn qft3(q: Q<((Bit, Bit), Bit)>) -> Q<((Bit, Bit), Bit)>` | F002: positive F8 with included reversal |

F001 and F002 use `F_d[y,x] = exp(2*pi*i*x*y/d)/sqrt(d)` for `d = 4, 8`. For
the two-bit input `(a,b)`, `x = a + 2*b`. For `((a,b),c)`,
`x = a + 2*b + 4*c`. The output coordinates follow the same convention and
include the reversal of the circuit.

Rules:

- The complete tuple tree, the ordered axes and the scalar phase are part of
  each contract. Equal bit width, agreement of probabilities or an inverse
  round trip cannot substitute for them.
- R001 preserves the original order of its two owners and specifies exact
  Hadamard coefficients.

### `std::reflection`

| Path | Declaration | Contract |
| --- | --- | --- |
| `std::reflection::reflect_uniform2` | `pub unitary fn reflect_uniform2(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)>` | R002: the phase-fixed reflection about the uniform two-bit state |

R002 is `2|++><++| - I`, with this exact sign. Its body uses the private total
classical predicate `nonzero2`, which returns zero exactly on `00` and one
elsewhere. The computed auxiliary of that predicate supplies the phase +1 on
`00` and -1 elsewhere, before conjugation by R001.

Rules:

- The protected computed scope requires two things of the temporary
  auxiliary: an exact return to zero, and separation. It requires them for
  all permitted inputs and references.
- Moving the helper or naming the reflection does not supply that evidence.
- The helper is private. `std::reflection` imports the ordinary public
  Hadamard transform.

### `std::measurement`

| Path | Declaration | Contract |
| --- | --- | --- |
| `std::measurement::measure_x` | `pub observe fn measure_x(q: Q<Bit>) -> Bit` | R003: destructive X measurement |
| `std::measurement::measure_z2` | `pub observe fn measure_z2(q: Q<(Bit, Bit)>) -> (Bit, Bit)` | R004: destructive ordered two-bit Z measurement |
| `std::measurement::parity_zz` | `pub observe fn parity_zz(a: Q<Bit>, b: Q<Bit>) -> ((Q<Bit>, Q<Bit>), Bit)` | R005: nondestructive Z-parity measurement of the data |

Each contract describes every outcome with its unnormalized branch, without
postselection:

- R003 has the branch `K_b = <b| H`. It returns `b` for the X eigenvalue
  `(-1)^b` and consumes its target owner.
- R004 has the branch `K_(a,b) = <a,b|` in the ordered coordinates of the
  register. It returns the left result and the right result in that order,
  and it consumes both owners.
- R005 has the branch `K_s = (I + (-1)^s Z_a Z_b)/2`. It returns both data
  owners in their original order together with `s`, and it preserves
  coherence within each parity subspace. It measures and consumes its
  fresh-zero meter.

Rules:

- R005 requires distinct owners. It does not require a product state.

### `std::gate`

| Path | Declaration | Contract |
| --- | --- | --- |
| `std::gate::id` | `pub unitary fn id[const A: Basis](q: Q<A>) -> Q<A>` | Identity with coefficient +1. It keeps the full Basis tree and every zero-width owner. It emits no physical instruction and performs no implicit type conversion. |
| `std::gate::x` | `pub unitary fn x(q: Q<Bit>) -> Q<Bit>` | X, as `H Z H` |
| `std::gate::z` | `pub unitary fn z(q: Q<Bit>) -> Q<Bit>` | Z, the half-turn phase `phase[1,1]` |
| `std::gate::s` | `pub unitary fn s(q: Q<Bit>) -> Q<Bit>` | S, the quarter-turn phase `phase[1,2]` |
| `std::gate::sdg` | `pub unitary fn sdg(q: Q<Bit>) -> Q<Bit>` | S†, as `adjoint(s)` |
| `std::gate::t` | `pub unitary fn t(q: Q<Bit>) -> Q<Bit>` | T, exactly `diag(1, exp(i*pi/4))`. The body controls the scalar phase on a fresh `Q<Unit>` owner and explicitly consumes that owner. It adds no physical wire. |
| `std::gate::tdg` | `pub unitary fn tdg(q: Q<Bit>) -> Q<Bit>` | T†, as `adjoint(t)` |
| `std::gate::cnot` | `pub unitary fn cnot(a: Q<Bit>, b: Q<Bit>) -> (Q<Bit>, Q<Bit>)` | Ordinary controlled X. The first owner is the control. The outputs keep their order, with phase +1. |
| `std::gate::toffoli` | `pub unitary fn toffoli(a: Q<Bit>, b: Q<Bit>, c: Q<Bit>) -> ((Q<Bit>,Q<Bit>),Q<Bit>)` | Ordinary control of a packed CNOT. Both controls keep their basis labels. The target flips if and only if both controls are one, with phase +1 and no additional physical wire. |
| `std::gate::controlled_phase` | `pub unitary fn controlled_phase[const j: Nat, const k: Nat](a: Q<Bit>, b: Q<Bit>) -> (Q<Bit>, Q<Bit>)` | Ordinary control of `phase[j,k]`: exactly `diag(1,1,1,exp(2*pi*i*j/2^k))` in control/target order. The concrete coefficient and profile conditions of the phase provider apply. |
| `std::gate::swap` | `pub unitary fn swap(a: Q<Bit>, b: Q<Bit>) -> (Q<Bit>, Q<Bit>)` | Two-Bit SWAP with exact phase +1, as three ordinary CNOT calls that keep their controlled-X work. The output wires keep their original order. A target gate cost requires a checked realization. |

Rules:

- `x`, `z`, `s`, `sdg` and `tdg` each preserve the full exact phase and the
  original returned owner interface.

#### The exact phase of `t`

This section says how the body of `t` obtains its exact phase. The private
scalar helper `scalar_eighth` has the exact meaning `zeta_8 I_Unit`. Coherent
control of that helper gives `diag(1,zeta_8)` on the retained Bit. The
zero-width target is a logical owner: the body introduces it with `unit(())`
and consumes it with `finish`.

Rules:

- The absence of physical wires does not imply a zero synthesis cost or a
  zero gate cost.
- A body that applies the scalar directly to `Q<Bit>` gives `zeta_8 I_Bit`.
  That body must fail an exact T request.
- `global_phase_eighth` is the bare scalar primitive. `phase_eighth` is not an
  alias.

> **Implementation note.** The body of `t` keeps a `CircuitAction::Contract`
> dependency. The terminal OpenQASM 3 exporter and the terminal QIR Base
> exporter expand the retained circuit of that dependency. They preserve the
> ordered axes, the control polarity and the adjoints before they lower to
> target gates.

### `std::state`

| Path | Declaration | Contract |
| --- | --- | --- |
| `std::state::init0` | `pub isometry fn init0() -> Q<Bit>` | Exact zero-state preparation with coefficient +1. The function is nullary. It allocates one fresh physical wire and one owner. |
| `std::state::reset` | `pub observe fn reset(q: Q<Bit>) -> Q<Bit>` | An explicit discard, followed by `init0` |

`init0` prepares exactly `|0>`, tensored with the identity on every retained
reference. Its body is the ordinary `basis unit(()) as _ { 0 }`, which uses
the injective singleton rule.

`reset` has the channel `rho_AR -> |0><0| tensor Tr_A(rho_AR)`. The fresh zero
state is independent of the erased input.

Rules:

- `reset` is Observe even on a zero input.

### `std::structure`

| Path | Declaration | Contract |
| --- | --- | --- |
| `std::structure::permute_axes` | `pub unitary fn permute_axes(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)>` | Structural two-axis map `[1,0]` with exact phase +1. The output wire order is reversed. The body emits no gate instruction. |
| `std::structure::transpose_axes` | `pub unitary fn transpose_axes[const n: Nat, const i: Nat, const j: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> requires i < j, j < n` | The output-to-input axis map is the identity with the positions `i` and `j` exchanged. The phase is +1, and the body emits no gate instruction. |
| `std::structure::empty` | `pub unitary fn empty() -> Q<Bits<0>>` | Explicit singleton basis map from a fresh Unit owner to the exact `Bits<0>` tag, with coefficient +1 and no physical wire. The function is nullary. |
| `std::structure::consume_empty` | `pub unitary fn consume_empty(q: Q<Bits<0>>) -> Unit` | Explicit singleton map to Unit, followed by `finish`. It keeps the complete scalar and reference action. It performs no observation and no implicit coercion. |

Rules:

- A call of `transpose_axes` must satisfy `i < j < n`. The checker rejects a
  call that breaks this premise with the class `size`.
  [Codes](diagnostics.md#codes) gives the code of that class on each route.
- Each argument of a call is relative to the input order at that call.
- A finite sequence of transpositions describes an arbitrary ordered
  permutation, under the usual specialization bounds.

The checker accepts this program:

```qli
use std::structure::transpose_axes;

pub unitary fn probe(q: Q<Bits<3>>) -> Q<Bits<3>> {
    transpose_axes[3,0,1](transpose_axes[3,1,2](q))
}
```

On `Bits<3>`, the program first exchanges positions 1 and 2, then positions 0
and 1. It gathers the original axes in the order `[2,0,1]`. The checker
rejects the calls `transpose_axes[3,1,1]`, `transpose_axes[3,2,1]` and
`transpose_axes[3,0,3]` on the same input.

### Physical swap and axis reordering

This section compares two functions that exchange two Bits.
`std::gate::swap` and `std::structure::permute_axes` are ordinary checked
`.qli`, as is every function of `std::gate` and `std::structure`. Under fixed
input and output coordinates, both denote `|a,b> -> |b,a>` with phase +1.
Their wire maps and their physical work differ.

Rules:

- `swap(excl a, excl b)` returns authority to the updated original owners.
- `permute_axes(q)` consumes its pair and returns it with the explicit axis
  map.
- Neither operation is binding exchange.
- Matrix equality alone grants an optimizer no permission to replace one
  routing implementation by the other.
- Target routing and a quantitative resource claim each need their own
  checked correspondence and accounting. Zero source gate instructions are
  not a promise of zero physical routing cost.

## Retired paths

A **retired path** is an earlier public path of the standard library that no
module provides. The table says where the members of each retired path are.

| Retired path | Canonical location |
| --- | --- |
| `std::transforms::{qft2,qft3}` | `std::transform::{qft2,qft3}` |
| `std::routines::hadamard2` | `std::transform::hadamard2` |
| `std::routines::reflect_uniform2` | `std::reflection::reflect_uniform2` |
| `std::routines::{measure_x,measure_z2,parity_zz}` | `std::measurement::{measure_x,measure_z2,parity_zz}` |
| `std::gate::permute_axes` | `std::structure::permute_axes` |
| `std::arithmetic::{increment2,add2,mul2_mod15}` | Local `arithmetic` source in `examples/order_finding/arithmetic.qli`; no canonical std export |

A grouped path in this table abbreviates one row for each member. The table
defines no import syntax.
[Prelude, imports and qualified names](prelude.md) gives the import forms.

Rules:

- A program must name a supported declaration by its canonical location. A
  retired path has no compatibility alias, and the loader rejects an import
  of it.
- All five former public members of `routines` have a namespace under
  [Admission rules](#admission-rules). The private `nonzero2` is in
  `std::reflection`, with the reflection.
- The three former arithmetic exports are the entire retired public
  arithmetic surface.
- A contract identifier keeps its meaning when its definition moves.
- The move changes no public result tree and no consume or return obligation.
- Active imports, examples, corpus translations, tests and documentation must
  migrate together.
- First authoring sources, earlier diagnostics, proofs, counterexamples and
  validation records keep their original paths and bytes. A historical record
  is not a compatibility API and not an executable migration target.

The loader accepts `use std::transform::qft2;`. It rejects
`use std::transforms::qft2;`, `use std::routines::hadamard2;` and
`use std::arithmetic::add2;`. It also rejects `use std::gate::permute_axes;`,
and the message names `std::structure::permute_axes` and `std::gate::swap`.

### Local arithmetic

The three retired arithmetic definitions are ordinary local source of the
order-finding example.

| Local definition | Whole-space contract |
| --- | --- |
| `increment2` / A001 | `Q<(Bit,Bit)> ->` the same tree; `y -> (y+1) mod 4` with coefficient +1, first leaf weight 1 and overflow wrapping. |
| `add2` / A002 | `Q<((Bit,Bit),(Bit,Bit))> ->` the same tree; `(x,y) -> (x,(y+x) mod 4)` with coefficient +1; both pairs little-endian and the addend retained. |
| `mul2_mod15` / A003 | `Q<((Bit,Bit),(Bit,Bit))> ->` the same tree; `y -> 2*y mod 15` for `y < 15` and `15 -> 15`, with coefficient +1; weights `(1,2,4,8)` and returned route `(d,a,b,c)`. |

Rules:

- These fixed teaching and test circuits have no input-range promise, no
  auxiliary and no measurement. They return every owner.
- Their removal from std changes none of their bodies, contracts, evidence or
  license.
- They are ordinary local source. They do not establish scalable arithmetic
  support.

## Checking

The standard library receives the checks of any source. Its place in the
distribution exempts it from none of them.

Rules:

- All eight modules, their private and unused declarations, and the source of
  the caller undergo the same mandatory common-source judgment.
- Concrete lowering and fresh native acceptance are separate stages. The
  support for each stage is specific to a profile.
- A path grants no sealed status, no body-derived effect, no independent exact
  Meaning, no provider capability and no acceptance exception.
- Migrated source must be rechecked. A cached fact must not be rebound to
  other bytes.

## Status and limits

Limits of the library:

- Generic QFT is excluded from all of v0.3.0 and from the adopted development
  goal. The exclusion covers four things: its implementation, its public
  integration, the equivalence of the fixed and generic forms, and the
  completion of proofs that are specific to QFT. This chapter promises
  neither `qft<N>` nor a completion target.
- The library contains no arithmetic implementation and no mechanism that
  selects an algorithm.
- A single first-class permutation argument is unsupported.
- On the bounded producer path of `t`, the exporters apply their target
  vocabulary and their workspace limits. They refuse an unsupported body.
- A later structural refactor consumes these mathematical identities and the
  contracts that are complete. It may change layout, visibility and
  discovery. It must not redefine a meaning, restore the retired catch-all
  namespace or the retired arithmetic exports, or add a dependency on generic
  QFT.
- The analysis tools QLT, QDB and QCP, and general growth of the standard
  library, have their own later scope.

Limits of the canonical version:

- The embedded-manifest gate is implemented. It implements no resolver and no
  record API.
- The binding of the resolved pair by qargo is unfinished. It requires the
  checks of qargo on the resolved environment and on the pairing of lock and
  build records.
- Equal version strings alone cannot detect stale or substituted source
  content, establish an official artifact identity, or replace the source and
  evidence checks.
- The duty to carry the authoritative edition identity through public and
  native artifacts is met in part. The
  [native envelope](execution-view.md#native-envelope-cutover) carries the
  explicit edition through native acceptance. The ecosystem migration is not
  complete, and its CI is open.
- Packaging identity is not a source-preservation proof. It discharges none
  of QS, PR, RS and EXACT.

Evidence:

- Source checking, bounded complex and instrument comparisons, conformance of
  the checked IR, source preservation and specification review each have
  separate evidence and premises.
- Tests: `tests/project.rs` checks the canonical paths and the rejection of
  every retired path. `tests/editions.rs` compares the bundled descriptor with
  `stdlib/Qargo.toml` and with every file of `stdlib/src`. The unit tests of
  `src/frontend/project/edition.rs` check the embedded-manifest gate.
  `tests/axis_routing_boundary.rs` checks the transposition example.
- The source definitions and their exact requested checks are separate from
  source-to-target preservation and from quantitative PR and RS evidence.
- The migrated source requires exact literal-output phase checks and
  clean-scratch checks. These include the narrow zero-input, one-output
  singleton table for preparation. Their coverage must be recorded with the
  final artifact. This chapter reports no execution of them.
- Those checks supply no general export preservation theorem and no
  quantitative resource certificate.
- This namespace contract completes no broader QS, PR, quantitative RS or
  EXACT proof obligation. It admits no constitutional guarantee.
- Validation of the source migration is recorded separately. This chapter
  does not report a completed same-commit release gate.

## History

- [#317](https://github.com/MGYamada/Qleisli/issues/317) adopted the semantic
  namespaces, their admission rules and the path migration. The chapter was
  written as normative for the product version `0.3.0-beta`.
- `std` is ordinary checked source under
  [#167](https://github.com/MGYamada/Qleisli/issues/167), the qrate definition
  [#170](https://github.com/MGYamada/Qleisli/issues/170) and the
  external-artifact boundary
  [#169](https://github.com/MGYamada/Qleisli/issues/169).
- [#171](https://github.com/MGYamada/Qleisli/issues/171) requires the checks
  of qargo on the resolved environment and on the pairing of lock and build
  records.
- [#255](https://github.com/MGYamada/Qleisli/issues/255) holds the duty to
  carry the authoritative edition identity through public and native
  artifacts.
- The structural refactor is planned for 0.4.0 in
  [#152](https://github.com/MGYamada/Qleisli/issues/152).
- The first desired namespace clients and the failures before the migration
  are retained in
  `tests/fixtures/authoring_sessions/stdlib-semantic-namespaces-v030/`.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
