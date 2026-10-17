# Standard-library semantic namespaces

This chapter is normative for the edition-2026 `0.3.0-beta` mathematical
stdlib namespaces, their admission rules and the path migration adopted in
[#317](https://github.com/MGYamada/Qleisli/issues/317). It is subordinate to the
[authority hierarchy](authority.md) and [primitive boundary](primitive-boundary.md).
It specifies intended contracts; a namespace, source comment or successful
source check is not a proof of its mathematical implementation.
The [inference and discovery boundary](architecture.md#inference-and-explicit-discovery)
specifies how unfamiliar derived abstractions lead to their contracts and ordinary source.

## Names follow mathematical meaning

A canonical mathematical stdlib function name must describe what the operation
computes. It must not name an implementation's history, benchmark, decomposition
or algorithm in place of that meaning. When callers need an algorithm choice,
that choice belongs in an explicit parameter, policy or configuration layer.
This rule specifies no new policy syntax or supported implementation.

Top-level mathematical namespaces prefer singular semantic concept nouns.
Every public operation has one canonical home with a semantic admission rule;
`routines`, `utils`, `helpers`, `misc` or an equally empty collection is not a
mathematical classification. Source-file layout does not determine membership.

When an operation forms a genuine parameterized mathematical family, that family
owns its canonical semantic API identity. Fixed-size names describe their bounded
contracts and cannot replace the family's identity. A reserved identity is not
an available API or evidence of specialization correspondence. In particular,
generic QFT implementation, public integration, fixed/generic equivalence and
QFT-specific proof completion are excluded from all v0.3.0 and the current goal.
The existing `qft2` and `qft3` contracts remain supported fixed interfaces; this
chapter promises neither `qft<N>` nor a future completion target.

## Admission rules

| Namespace | An API belongs here iff ... | Current ordinary source |
| --- | --- | --- |
| `std::basis` | Its defining contract is a total finite map on ordinary basis labels, with no quantum owner transition or observation. Coherent use must satisfy the enclosing construction's separate obligations. | `stdlib/src/basis.qli` |
| `std::transform` | Its defining contract is a mathematical basis transform with an explicit whole-input operator and ordered coordinates, such as Hadamard or Fourier transformation. A contract defined as reflection about a subspace belongs in `reflection`; a measurement belongs in `measurement`. | `stdlib/src/transform.qli` |
| `std::reflection` | Its defining contract is a phase-fixed reflection about a specified state or subspace, including the exact projector, sign and owner interface. Being unitary alone is not this classification. | `stdlib/src/reflection.qli` |
| `std::measurement` | Its defining mathematical operation is a complete measurement instrument with declared classical outcomes and residual quantum owners, including destructive measurement or a measurement that retains data. An arbitrary observing routine is not enough. | `stdlib/src/measurement.qli` |
| `std::gate` | An ordinary checked gate definition has an exact operator, scalar phase and ordered-owner contract. Gate membership confers no primitive or verifier authority. | `stdlib/src/gate.qli` |
| `std::state` | Its defining contract explicitly prepares a state or replaces an owned state under a complete effect/reference contract. Pure preparation and observation-bearing reset remain distinct. | `stdlib/src/state.qli` |
| `std::structure` | An ordinary checked structural map explicitly changes an owner partition or representation order. Its exact input/output trees and axis map are part of the contract; it is not a physical gate merely because it denotes a permutation. | `stdlib/src/structure.qli` |
| `std::arithmetic` (reserved) | Its public identity is a reusable parameterized arithmetic or number-theoretic operation whose contract is independent of one hard-coded circuit instance. | No current bundled module or public export. |

The reserved shape `std::arithmetic::modexp<N>` represents modular
exponentiation. `std::arithmetic::primefact<N>` reserves the v1 semantic identity
of prime factorization; `shor<N>` is an algorithm name, not its canonical
mathematical API. These are design identities, not current callable syntax,
generic-parameter syntax commitments or delivered operations. No arithmetic
implementation or algorithm-selection mechanism is introduced here.

Language primitives are bare typed identities resolved only after lexical
bindings and ordinary declarations/imports. They are not standard-library
exports or a prelude. `std::quantum`, `std::observe`, `std::registers` and
`std::classical` are retired without aliases. The
[primitive boundary](primitive-boundary.md) specifies all 13 retained identities,
the complete 27-entry migration and concrete profile limits. Ordinary modules,
including `std::basis`, have no primitive privilege.

## Current interfaces and contracts

The seven bundled ordinary modules expose twenty-five public definitions and five
private helpers for a classical predicate, scalar phase, parameterized phase,
packed CNOT and fixed Bit identity.
Contract identifiers retain their existing meanings after the
move; they are not constitutional ledger entries or verification badges.

| Public path | Exact interface | Source contract / principal effect |
| --- | --- | --- |
| `std::basis::xor2` | `classical fn (Bit, Bit) -> Bit` (two arguments) | B001: total XOR on four input-label pairs; noninjective on the product domain. |
| `std::basis::and2` | `classical fn (Bit, Bit) -> Bit` (two arguments) | B002: total AND on four input-label pairs; noninjective on the product domain. |
| `std::transform::hadamard2` | `fn (Q<(Bit, Bit)>) -> Q<(Bit, Bit)>` | R001: ordered H tensor H; Unitary. |
| `std::transform::qft2` | `fn (Q<(Bit, Bit)>) -> Q<(Bit, Bit)>` | F001: positive F4 with included reversal; Unitary. |
| `std::transform::qft3` | `fn (Q<((Bit, Bit), Bit)>) -> Q<((Bit, Bit), Bit)>` | F002: positive F8 with included reversal; Unitary. |
| `std::gate::swap` | `unitary fn (Q<Bit>, Q<Bit>) -> (Q<Bit>, Q<Bit>)` | Two-Bit SWAP, exact phase +1; three ordinary CNOT calls with retained controlled-X work, original output wire order. Actual target gate costs require a checked realization. |
| `std::gate::t` | `unitary fn (Q<Bit>) -> Q<Bit>` | Exact `diag(1, exp(i*pi/4))`, derived by controlling the scalar phase on a fresh `Q<Unit>` owner and explicitly consuming that owner. No additional physical wire. |
| `std::gate::{s,sdg,tdg,z,x}` | Each `unitary fn (Q<Bit>) -> Q<Bit>` | S and Z use the quarter-turn and half-turn phases `phase[1,2]` and `phase[1,1]`; S† and T† use `adjoint(s)` and `adjoint(t)`. X is `H Z H`. Each preserves the full exact phase and the original returned owner interface. |
| `std::gate::id` | Static `[const A:Basis]`; `unitary fn (Q<A>) -> Q<A>` | Identity with coefficient +1, retaining the full Basis tree and every zero-width owner. No physical instruction or implicit type conversion. |
| `std::gate::cnot` | `unitary fn (Q<Bit>, Q<Bit>) -> (Q<Bit>, Q<Bit>)` | Ordinary controlled X. The first owner is the control; outputs retain their order and phase +1. |
| `std::gate::toffoli` | `unitary fn (Q<Bit>, Q<Bit>, Q<Bit>) -> ((Q<Bit>,Q<Bit>),Q<Bit>)` | Ordinary control of packed CNOT. Both controls retain their basis labels; target flips iff both are one, with phase +1 and no additional physical wire. |
| `std::gate::controlled_phase` | Static `[const j:Nat,const k:Nat]`; `unitary fn (Q<Bit>, Q<Bit>) -> (Q<Bit>, Q<Bit>)` | Ordinary control of `phase[j,k]`, exact `diag(1,1,1,exp(2*pi*i*j/2^k))` in control/target order. The phase provider's concrete coefficient/profile conditions remain required. |
| `std::state::init0` | Nullary `isometry fn () -> Q<Bit>` | Exact `|0>` preparation with coefficient +1, one fresh physical wire and owner, tensored with identity on every retained reference. Ordinary `basis unit(()) as _ { 0 }`, using the existing injective singleton rule. |
| `std::state::reset` | `observe fn (Q<Bit>) -> Q<Bit>` | Explicit discard followed by `init0`; the fresh zero state is independent of the erased input, with channel `rho_AR -> |0><0| tensor Tr_A(rho_AR)`. It remains Observe on a zero input. |
| `std::structure::empty` | Nullary `unitary fn () -> Q<Bits<0>>` | Explicit singleton basis map from a fresh Unit owner to the exact Bits<0> tag, coefficient +1, no physical wire. |
| `std::structure::consume_empty` | `unitary fn (Q<Bits<0>>) -> Unit` | Explicit singleton map to Unit followed by `finish`; complete scalar/reference action retained, no observation or implicit coercion. |
| `std::structure::permute_axes` | `unitary fn (Q<(Bit,Bit)>) -> Q<(Bit,Bit)>` | Structural two-axis map `[1,0]`, exact phase +1; reversed output wire order, no gate instruction. |
| `std::reflection::reflect_uniform2` | `fn (Q<(Bit, Bit)>) -> Q<(Bit, Bit)>` | R002: `2|++><++| - I`, with this exact sign; Unitary. |
| `std::measurement::measure_x` | `fn (Q<Bit>) -> Bit` | R003: destructive X measurement; Observe. |
| `std::measurement::measure_z2` | `fn (Q<(Bit, Bit)>) -> (Bit, Bit)` | R004: destructive ordered two-bit Z measurement; Observe. |
| `std::measurement::parity_zz` | `fn (Q<Bit>, Q<Bit>) -> ((Q<Bit>, Q<Bit>), Bit)` | R005: nondestructive Z-parity measurement of the data; Observe. |

The `std::gate` and `std::structure` functions are ordinary `.qli`, not sealed
compiler entries. The two-Bit interfaces of `swap` and `permute_axes` are explicit:
generic register SWAP and arbitrary permutation witnesses remain unsupported. `swap(excl a, excl b)`
returns authority to the updated original owners; `permute_axes(q)` consumes
and returns its pair with the explicit axis map. Neither is binding exchange.
Under fixed input/output coordinates both denote `|a,b> -> |b,a>` with phase
+1, but their wire maps and physical work differ. Matrix equality alone grants
no optimizer permission to replace one routing implementation by the other.
Actual target routing and quantitative resource claims need their own checked
correspondence and accounting; zero source gate instructions are not a promise
of zero physical routing cost.

For T, the private scalar helper has exact meaning `zeta_8 I_Unit`. Coherent
control gives `diag(1,zeta_8)` on the retained Bit; the zero-width target is a
logical owner, explicitly introduced with `unit(())` and consumed with `finish`.
Its absence of physical wires does not imply zero synthesis or gate cost.
Applying the scalar directly to `Q<Bit>` instead gives `zeta_8 I_Bit`, which
must fail an exact T request. The source definitions and exact requested checks
remain separate from source/target preservation and quantitative PR/RS evidence.
`global_phase_eighth` is the bare scalar primitive; `phase_eighth` is not an alias.
The ordinary T body retains a `CircuitAction::Contract` dependency. The terminal
OpenQASM 3 and QIR Base exporters expand its actual retained circuit, preserving
ordered axes, control polarity and adjoints before lowering to target gates.
This bounded producer path has the same target vocabulary and workspace limits;
an unsupported body still refuses. Exact literal-output phase and clean-scratch
checks are required for the actual migrated source, including the narrow
zero-input/one-output singleton table for preparation. Their coverage must be
recorded with the final artifact; this chapter does not report a new execution.
They do not supply a general export
preservation theorem or a quantitative resource certificate.

These rows are interface descriptions, not declaration syntax or new function
types. Public quantum functions have explicit checked effect contracts under
`Unitary <= Isometry <= Observe`; their bodies are checked independently.
External callers use those public effects, while same-module inference retains
its precision and any further external boundary. Ordinary bundled and user
source follow the [same effect rules](source-text.md#ordinary-function-effects-and-assertions).
Classical functions have total ordinary meaning and may also receive ordinary
runtime values, including already measured Bits. They preserve the effects of
their evaluated arguments and cannot inspect live quantum owners. Their truth
tables grant no quantum preparation, observation, inverse/control access or
coherent injectivity evidence; coherent use retains its separate checks.

For F001 and F002, `F_d[y,x] = exp(2*pi*i*x*y/d)/sqrt(d)` for `d = 4, 8`.
For the two-bit input `(a,b)`, `x = a + 2*b`; for `((a,b),c)`,
`x = a + 2*b + 4*c`. Output coordinates follow the same convention and include
the circuit's reversal. Complete tuple trees, ordered axes and scalar phase
are part of the contract; equal bit width, probability agreement or an inverse
round trip cannot substitute for them. R001 likewise preserves the original
two-owner order and specifies exact Hadamard coefficients.

R002 uses the private total classical predicate `nonzero2`: it returns zero exactly
on `00`, and one elsewhere. Its computed auxiliary supplies phase +1 on `00`
and -1 elsewhere before conjugation by R001. The protected computed scope
requires exact zero return and separation of that temporary auxiliary for all
permitted inputs and references. Moving the helper or naming the reflection
does not supply that evidence. The helper remains private; reflection imports
the ordinary public Hadamard transform.

The three measurement contracts describe every outcome with its unnormalized
branch, without postselection:

- R003 has branch `K_b = <b| H`, returns `b` for X eigenvalue `(-1)^b`, and
  consumes its target owner.
- R004 has branch `K_(a,b) = <a,b|` in the register's ordered coordinates,
  returns the left and right results in that order, and consumes both owners.
- R005 has branch `K_s = (I + (-1)^s Z_a Z_b)/2`. It returns both data owners in
  their original order together with `s`, preserving coherence within each
  parity subspace. Its fresh-zero meter is measured and consumed.

All quantum contracts apply to arbitrary permitted inputs tensored with an
external reference identity. Separate owners may be entangled with each other
or a reference; R005 requires distinct owners, not a product-state promise.
The public result trees and consume/return obligations are unchanged. No
measurement result authorizes implicit discard, clean release, inverse or
controlled access.

## Migration and local arithmetic

| Earlier public path | Current location |
| --- | --- |
| `std::transforms::{qft2,qft3}` | `std::transform::{qft2,qft3}` |
| `std::routines::hadamard2` | `std::transform::hadamard2` |
| `std::routines::reflect_uniform2` | `std::reflection::reflect_uniform2` |
| `std::routines::{measure_x,measure_z2,parity_zz}` | `std::measurement::{measure_x,measure_z2,parity_zz}` |
| `std::gate::permute_axes` | `std::structure::permute_axes` |
| `std::arithmetic::{increment2,add2,mul2_mod15}` | Local `arithmetic` source in `examples/order_finding/arithmetic.qli`; no canonical std export. |

The grouped path notation in this table is a migration abbreviation, not new
import syntax. Import each supported declaration explicitly. There are no
old-path compatibility aliases. All five former public `routines` members are
classified above; private `nonzero2` moves with reflection. The three former
arithmetic exports are the entire retired public arithmetic surface:

| Preserved local definition | Whole-space contract |
| --- | --- |
| `increment2` / A001 | `Q<(Bit,Bit)> ->` the same tree; `y -> (y+1) mod 4` with coefficient +1, first leaf weight 1 and overflow wrapping. |
| `add2` / A002 | `Q<((Bit,Bit),(Bit,Bit))> ->` the same tree; `(x,y) -> (x,(y+x) mod 4)` with coefficient +1; both pairs little-endian and the addend retained. |
| `mul2_mod15` / A003 | `Q<((Bit,Bit),(Bit,Bit))> ->` the same tree; `y -> 2*y mod 15` for `y < 15` and `15 -> 15`, with coefficient +1; weights `(1,2,4,8)` and returned route `(d,a,b,c)`. |

These fixed teaching/test circuits have no input-range promise, auxiliary or
measurement, and return every owner. Their removal from std does not change
their preserved bodies, contracts, evidence or license. They remain ordinary
local source and do not establish scalable arithmetic support.

Active imports, examples, corpus translations, tests and current documentation
must migrate together. First authoring sources, earlier diagnostics, proofs,
counterexamples and validation records retain their original paths and bytes;
historical records are not compatibility APIs or executable migration targets.
The first desired namespace clients and actual pre-migration failures are
retained in `tests/fixtures/authoring_sessions/stdlib-semantic-namespaces-v030/`.

## Checking and later structure

All seven modules, their private/unused declarations and caller source undergo
the same mandatory common-source judgment. Concrete lowering and fresh native
acceptance remain separate stages with profile-specific support. A path grants
no sealed status, body-derived effect, independent exact Meaning, provider
capability or acceptance exception. Recheck migrated source rather than rebinding
cached facts to new bytes.

The [0.4.0 structural refactor](https://github.com/MGYamada/Qleisli/issues/152)
consumes these mathematical identities and actually completed contracts. It may
change layout, visibility and discovery without redefining meaning, restoring
the retired catch-all or arithmetic exports, or adding a generic-QFT dependency.
QLT, QDB, QCP and general stdlib growth retain their own later scope.

Source checking, bounded complex/instrument comparisons, actual-IR conformance,
source preservation and specification review must retain their separate evidence
and premises. This namespace contract completes no broader QS, PR, quantitative
RS or EXACT proof obligation and admits no new constitutional guarantee.
Validation of the current source migration is recorded separately; this chapter
does not report a completed same-commit release gate.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
