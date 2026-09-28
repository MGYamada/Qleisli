# Fixed-width operation parameters and meaning contracts (M1)

Status: **selected on 2026-09-27; fixed-width language slice implemented in
0.1.8 on 2026-09-28**. This is the normative
M1 supplement to [current v0](language-spec.md); the finite grammar and older
special forms retain their contracts. The [implementation/release record](releases/v0.1.8.md)
records executed validation and migration. Separate [machine interfaces](machine-interface-spec.md)
and the [M2 profile](hierarchical-ir-spec.md) retain their own open gates.
This implementation completes neither M1 as a whole nor G020-3's release gates.

## Scope, vocabulary and limits

M1 has fixed basis trees `Unit`, `Bit`, and ordered pairs only. A static operation
description contains no quantum state or runtime classical value. Its semantic
interface is a phase-fixed unitary on one `Q<A>`, including zero-width ownership.
It carries a logical meaning and separately justified implementation access.
Operation descriptions may be copied at compile time; quantum owners may not.
`Op` is a static parameter category, not a runtime ownership/effect type.

All new spellings below are **language forms**, including meaning declarations,
static parameters/arguments, access constraints and static constructors. There
is no new sealed physical gate or ordinary-library function in this slice.
The existing gate library and both computed forms retain their contracts.
General builders returning operations, runtime closures, size parameters,
new effects and public capability wrapper types are excluded.

The new operation/meaning profile permits 0–6 interface bits, at most 1,024
steps per materialized contract circuit and the existing exact work budget of
10,000,000. Control/tensor count their entire resulting interface against six
bits. Static repetitions accept 0–4,096. Type/syntax depth remains 64 and type
trees at most 4,096 nodes. New specialization is limited to 256 distinct
instances per project, depth 64 and 1,000,000 aggregate lowering work units;
one work unit is one visited AST node or emitted circuit step, charged on every
visit/emission. Existing non-generic programs retain their existing profile.
Budget exhaustion diagnoses `limit`, never changes semantics or omits checks.

## Grammar and resolution

Extend the [v0 lexical and grammar rules](syntax-v0.md) as follows. `Name` is
an imported or local declaration name, not a qualified expression. No trailing
commas are accepted. `Nat` is decimal with no leading zero except `0`.

```ebnf
Decl          ::= ... | "pub"? "meaning" Ident ":" BasisType "=" Meaning ";"
QuantumDecl   ::= "pub"? Kind "fn" Ident StaticParams?
                  "(" Params? ")" "->" Type Requires? Block
StaticParams  ::= "[" StaticParam ("," StaticParam)* "]"
StaticParam   ::= "static" Ident ":" "Op" "<" BasisType ("," Name)? ">"
Requires      ::= "requires" Access ("," Access)*
Access        ::= ("Apply" | "Adjoint" | "Controlled") "(" Ident ")"
Meaning       ::= "permutation_by" "(" Name ")" | "phase_by" "(" Name ")"
StaticOp      ::= Name | "bind_op" "(" Name "," Name ")"
                | "inverse_op" "(" StaticOp ")"
                | "then_op" "(" StaticOp "," StaticOp ")"
                | "tensor_op" "(" StaticOp "," StaticOp ")"
                | "controlled_op" "(" StaticOp ")"
                | "repeat_op" "(" Nat "," StaticOp ")"
                | "conjugate_op" "(" StaticOp "," StaticOp ")"
StaticArgs    ::= "[" StaticOp ("," StaticOp)* "]"
Call          ::= Name StaticArgs? "(" Args? ")"
```

The `pub` in `QuantumDecl` above denotes the existing declaration modifier once,
not a second optional modifier inside `Decl`. `Kind` and runtime types remain v0.
Static parameter names share the local name namespace with runtime parameters;
duplicates are rejected. Static descriptions cannot occur as runtime results,
tuple elements, `let` values or basis expressions. A static parameter is only
usable as a static operand or as the callee of one quantum argument.

New reserved words are `meaning`, `static`, `Op`, `requires`, `Apply`, `Adjoint`,
`Controlled`, `permutation_by`, `phase_by`, `bind_op`, `inverse_op`, `then_op`,
`tensor_op`, `controlled_op`, `repeat_op`, and `conjugate_op`. Imports/visibility
of meanings use the same declaration rules as functions. Meanings and functions
share the module namespace. A meaning cannot refer to another meaning or an
operation parameter in this profile; it names an ordinary total basis function.
Static constructors are only parsed in `StaticOp` positions.

Generic calls require explicit arguments in declaration order. There is no
inference from runtime values. Evaluate runtime arguments left to right with
the v0 pending-owner rules, then resolve the static callee and arguments in the
residual lexical environment. Live and spent local bindings shadow global
declarations, as for current static forms. Static parameters are immutable;
a local binding may shadow one but cannot later resurrect it within that scope.
Static constraint names resolve in the declaration header, before the body.
All declarations are checked, including unused bodies and zero-repeat bodies.
The call graph, including static provider dependencies, must be acyclic.

`adjoint`, `repeat_static` and the two arms of `qif` additionally accept a
static parameter name wherever they accept a unitary name today. A constructed
operation can be passed to a helper's bracket arguments first; these old forms
do not gain arbitrary expression operands. `apply_contract` and both
`with_computed` forms retain their existing name operands and exact rules.

## Meanings and binding

For a declared exact basis tree A, flatten bit leaves left to right with the
first leaf least significant, preserving Unit nodes in the type identity.
The meanings are:

```text
permutation_by(f): f : A -> A is total and bijective
                  P_f |x> = |f(x)>
phase_by(phi):     phi : A -> (Bit,(Bit,Bit)) is total
                  D_phi |x> = zeta_8^(b0 + 2*b1 + 4*b2) |x>
```

Both operands must be ordinary `basis fn` declarations with exactly one
parameter. Exhaustively check their finite tables in M1. Duplicate permutation
outputs, missing values or a mismatched exact type tree are errors; equal bit
counts are insufficient. Phases reduce modulo eight. This introduces no new
runtime integer/phase type. Constant phase on `Unit` is observable under control
and must be retained. Arbitrary floats and equality modulo global phase are
rejected. These are mathematical target descriptions independent of the
implementation's circuit.

`bind_op(u,m)` requires an ordinary, closed declared unitary with the exact
signature `Q<A> -> Q<A>` and a meaning m on A. Lower and independently verify u,
extract its ordered operator using the existing finite contract boundary, and
check **exact** equality to m. The checked record binds the full meaning table,
type tree, implementation raw IR, port order, source bytes and dependency DAG.
It is not authorized by a name, digest, compiler cache entry or provider claim.
Changing any dependency invalidates the record. A plain unitary name as a
static argument uses its independently extracted circuit as its meaning;
use `bind_op` when the caller requires an independent mathematical target.

`Op<A,m>` restricts the operation to the fixed declared meaning m; `Op<A>`
quantifies over a phase-fixed meaning supplied by its argument. A constrained
parameter cannot be substituted solely because its provider is unitary.
Provider substitution requires identical tree and exact meaning. No implicit
coercion changes phase, layout, encoding or access. Private scratch is admitted
only through the current verified computed certificates, with zero entry/exit
and the complete external interface retained.

## Access judgments and composition

A generic body is checked against **only its declared access constraints**.
`Op` alone supplies no executable access. Constraints have no implicit
entailments: `Controlled(U)` does not silently provide `Apply(U)` or
`Adjoint(U)`. M1 transparent providers can supply all three after independent
extraction and verification of the derived circuits; that does not prove that
every abstract unitary has accessible control/inverse. Opaque external providers
are excluded from M1. Every requested derived circuit must fit the profile.

For descriptions U,V with meanings u,v, the following rules construct checked
descriptions. Execution order for `then_op(U,V)` is U then V.

| Constructor | Meaning/interface | Access required for Apply; for Adjoint; for Controlled |
| --- | --- | --- |
| `inverse_op(U)` | u† on A | Adjoint(U); Apply(U); Adjoint of a checked controlled-U circuit |
| `then_op(U,V)` | v u on identical A | Apply of both; Adjoint of both in reverse execution order; Controlled of both |
| `tensor_op(U,V)` | u tensor v on (A,B), A's bits first | Corresponding access to both on disjoint ports |
| `controlled_op(U)` | C(u) on (Bit,A), with index c+2x as defined below | Controlled(U); inverse of that checked circuit; control of that checked circuit |
| `repeat_op(n,U)` | u^n on A | Corresponding access to U even when n=0; checked count and repetition |
| `conjugate_op(V,W)` | v w v† on identical A | Apply/Adjoint(V) and Apply(W); Apply/Adjoint(V) and Adjoint(W); Apply/Adjoint(V) and Controlled(W) |

For `controlled_op`, let d=2^bits(A), c be the control bit, and 0≤x<d the
target label. In the [existing integer basis order](static-semantics.md#1-scope-and-coordinates),
the pair (c,x) has index c+2x. Define the phase-fixed controlled operator by

```text
C(u) |0+2x> = |0+2x>
C(u) |1+2x> = sum_y u[y,x] |1+2y>.
```

The block matrix diag(I_d,u) applies only after regrouping the basis by control:
with P|c+2x>=|c*d+x>, C(u)=P† diag(I_d,u) P. It is not the matrix in integer
index order before that permutation. For A=Bit and u=X, the output-label table
is `[0,3,2,1]`; `[0,1,3,2]` controls the higher bit and is rejected. For A=Unit,
d=1, so a scalar u=zeta_8^k gives diag(1,zeta_8^k); the active control sector
retains the scalar phase. This definition extends linearly and with identity
on any reference system, without an assumption of separable input.

“That checked circuit” means the actual retained transparent implementation
and evidence, never an opaque access assertion. Transforming it invokes the
finite structural inverse/control checker and exact comparison, including its
phase; failure to extract it is `unsupported`. Constructors check all operands
even when a result cancels mathematically. Identity result never erases an
unavailable premise or malformed dependency.

The controlled conjugation executes V†, then controlled W, then V, with the
control excluded from V's ports. Its inactive sector is v v†=I, and active
sector v w v†; the equality holds with an arbitrary reference. V must be a
whole-space unitary, not merely an isometry, and use its matching phase-fixed
inverse. For an encoded compute/uncompute construction, prove the analogous
equation on the admitted zero-scratch encoding and retain the entry/exit
certificate; the whole-space rule cannot invent that premise.

Calling a static parameter consumes exactly one `Q<A>` and returns one `Q<A>`,
with own effect Unitary joined with argument effects. `adjoint(U,q)` requires
Adjoint(U); repeating U requires Apply(U); `qif` requires Controlled on both
arms and disjoint control/target ownership. A generic declaration's declared
effect is still the public effect at all calls, including unused/zero-repeat
cases. Generic `iso`/`observe` functions may call operations; an operation
provider itself must satisfy the unary unitary signature above.

## Accepted and rejected examples

Runnable examples in 0.1.8 (not accepted by 0.1.7):

```qli
use std::quantum::z;
use std::quantum::t;

basis fn z_phase(x: Bit) -> (Bit,(Bit,Bit)) { (0,(0,x)) }
meaning ZMeaning: Bit = phase_by(z_phase);
unitary fn direct_z(q: Q<Bit>) -> Q<Bit> { z(q) }
unitary fn via_t(q: Q<Bit>) -> Q<Bit> { repeat_static(4,t,q) }

unitary fn twice[static U: Op<Bit,ZMeaning>](q: Q<Bit>) -> Q<Bit>
requires Apply(U) { U(U(q)) }

unitary fn first(q: Q<Bit>) -> Q<Bit> {
    twice[bind_op(direct_z,ZMeaning)](q)
}
unitary fn second(q: Q<Bit>) -> Q<Bit> {
    twice[bind_op(via_t,ZMeaning)](q)
}
```

Both clients use the same checked body and independently fixed Z meaning;
the result is I with exact phase. Acceptance still depends on budgets.

| Rejection case | Required diagnostic category and reason |
| --- | --- |
| Replace direct_z by X or by minus-Z | `contract`: different operator or exact phase |
| Declare permutation by a constant Bit function | `contract`: duplicate output, witness input pair |
| Use `adjoint(U,q)` with only Apply(U) | `capability`: missing Adjoint constraint even if a concrete caller supplies Z |
| Supply an observe/iso function as static provider | `effect`: wrong declared provider effect |
| Use `(Unit,Bit)` where Bit is required | `type_mismatch`: exact trees differ |
| Capture a live quantum variable in a provider | `ownership` or `unsupported`: no operation closures |
| Call U twice on the same owner rather than the returned owner | `ownership`: use after consumption |
| Control an operation with its target also used as control | `ownership`: overlapping interface |
| Unavailable access in a zero repetition or unreachable branch | `capability`: every branch/body is checked |
| Stale dependency, different output axes, or edited meaning | `contract`: record/binding mismatch, never a cache hit |

These new categories are mapped to the [versioned diagnostic interface](machine-interface-spec.md#diagnostics).
Human diagnostics must also locate the operation/constraint and relate the
provider or conflicting declaration. They need not expose internal matrices.

## Lowering and compatibility

First type/effect/ownership-check each generic body parametrically, deriving
its meaning composition and access obligations. Then specialize explicit
static arguments under a cache keyed by the full immutable binding, not just
function names. Check every instantiated cleanup/contract numerically **with
exact arithmetic** in this bounded M1 profile. Uninstantiated parametric
cleanup obligations cannot authorize execution; they are discharged for each
instance. No symbolic all-size theorem is claimed.

Lower static calls to finite `ApplyUnitary` circuits retaining semantic
evidence. **Implementation refinement, 2026-09-28:** `FiniteMeaning` lowers its
complete target to canonical monomial raw IR; `MeaningEvidence` checks that
target against the implementation through existing `FunctionEvidence`. The
private checked receipt retains both full raw programs, exact type tree and
source/dependency identity. Final IR uses existing `CircuitAction::Contract`
and the independent verifier checks its binding. The proposed new core action
is unnecessary: no irreducible obligation requires a new acceptance rule.
Existing raw-IR/evidence consumers need no migration or adapter replacement.
The public AST, tokens and frontend diagnostic variants do require the
[documented migration](releases/v0.1.8.md#compatibility-and-migration).
Portable interchange remains unimplemented under its separate specification.

Each generic body is checked with abstract operations and only declared access.
Disposable identity placeholders support resource checking but never produce
an executable generic program or evidence. Three-argument computed equations
inside that check remain obligations: concrete specialization rebuilds the
body and verifies every exact equation, including zero-count and unselected
source branches. No uninstantiated cleanup claim authorizes execution.
A per-project registry counts full immutable concrete bindings; lowering still
expands each call and charges its work rather than caching unchecked output.

Existing named-function cases of all five static/contract language forms keep
their evaluation order, local/spent-name shadowing, effects, phase, tree and
zero-count checks. Computed forms keep their different cleanup premises.
No keyword becomes an ordinary function. Existing programs need only rename
identifiers colliding with the newly reserved words when migrating to this
extension. Old public Rust AST/token/error matches must handle the documented
additions; core IR matches remain unchanged. New source-capacity defaults have an explicit legacy override in
the machine-interface specification; they remain unimplemented and do not
apply in 0.1.8.

## Implementation acceptance matrix

| Gate | Required evidence (implementation validation in the release record) |
| --- | --- |
| N1 grammar/resolution | Parse every new production and reject category misuse, duplicate static names, missing arguments, captures, cycles and runtime operation values; preserve old parser/name-resolution cases. |
| N2 meanings | Compare all columns for permutation and phase fixtures on Unit, Bit and nested pairs; include low-bit controlled-X `[0,3,2,1]`, reject the high-bit control table `[0,1,3,2]`, and retain controlled scalar phases on Unit; reject collisions, wrong trees, minus-sign changes, stale sources and output permutations. |
| N3 capabilities | Parametric body rejects missing access before specialization; test all constructors, unavailable zero-repeat access, both qif arms and conjugation with non-Hermitian V and phased W. |
| N4 ownership/effects | Preserve pending frames, entangled references, Q<Unit>, declared effects and all old computed/static rejection cases. |
| N5 binding/limits | Feed independently mutated target/receipt attachments directly to the verifier; enforce exact arithmetic/work/width/instance limits without recursion or unchecked allocations. |
| N6 reuse/migration | Compile and execute the two providers above through one unchanged client; exercise the canonical target/existing-receipt adapter, retain old CLI behavior, and document reserved-name/public API migration. |

G020-2 requires implementation of the selected shipping slice and G020-3 its
matrix, Rust/Lean/release checks and evidence ledger. These are **acceptance
requirements**; dated executed results belong to the implementation/release
record, not the original documentation-only adoption.
