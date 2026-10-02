# Fixed-width operations and meaning contracts (M1)

Normative implemented supplement; [language](language-spec.md), [types](type-system.md),
[static forms](static-operations.md), [finite contracts](finite-contracts.md) and
[machine interfaces](machine-interface-spec.md) remain separate. No general sizes/
operation values/closures/gate builder or effect is introduced.

## Scope and limits

Static Op is a copyable phase-fixed unary Q<A>->Q<A> description with full meaning
and separate checked access, no runtime capture. A is Unit/Bit/ordered exact products,
including empty owners. Width0..6, circuit1024, repeat0..4096, syntax/type depth64,
type4096nodes,256distinct specializations/depth64, aggregate lowering1M/exact10M.
Count control/tensor full widths; check unused arguments/zero bodies and share budgets.
One frozen full-project snapshot includes comments/std/every module, charged once
before copy with retained strong identity; each receipt rechecks names/metadata/pairs/
exact equation. Public owned views charge bytes. No guaranteed256-provider capacity.

## Grammar and resolution

Name local/imported declaration, no qualified expression; Nat canonical decimal,
no trailing comma. Reserve literal forms/constraints. Static/runtime names share
namespace; descriptions occur only static operands/unary callees, never runtime
let/tuple/result/basis expression. meaning shares declaration/import visibility and
names an ordinary total unary basis function, not another meaning/parameter.
Explicit static arguments in order, no inference. Runtime arguments evaluate first
left-to-right with pending owners, then statics in residual scope; live/spent locals
shadow globals/parameters. Resolve header access before body. Check all declarations,
acyclic providers and zero bodies. Existing adjoint/repeat/qif names admit static
parameters, not constructor expressions; bracket arguments may construct descriptions.
Computed/apply_contract restrictions remain unchanged.

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

## Meanings and binding

permutation_by(f) requires total bijective f:A->A, P|x>=|f(x)>.
phase_by(phi) requires total phi:A->(Bit,(Bit,Bit)), D|x>=zeta8^(b0+2b1+4b2)|x>.
First Bit low, full Unit/tree retained; exhaustive bounded tables. Reject collisions,
wrong trees/equal-width coercion/floats and equality modulo scalar.
bind_op(u,m) freshly checks closed ordinary declared unary unitary, full tree/ports,
actual raw circuit/ordered operator equality and complete source/dependency DAG.
Plain transparent provider derives meaning from verified circuit; binding adds
independent target. Op<A,m> fixes that meaning; Op<A> accepts the phase-fixed argument
meaning. No coercion/access from names/digests/caches. Scratch needs existing exact
entry/exit evidence and full frames.

## Access judgments and composition

Body may use only declared direct access: Controlled(U) alone permits neither U(q)
nor adjoint(U,q). Actual transparent checked circuits retain published constructor-
derived access, including inverse/control of controlled circuits; tightening it needs
MINOR. Opaque unitarity supplies no access. Check operands at cancellation/count0;
failed extraction is unsupported. Parameter application joins unitary with argument
effect; generic iso/observe may call operations, providers must declared unitary.

| Constructor | Meaning; required access |
| --- | --- |
| inverse_op(U) | u†; Apply needs Adjoint(U), inverse needs Apply(U), control uses adjoint of checked controlled-U. |
| then_op(U,V) | v u on identical A; corresponding access to both, inverses execute reversed. |
| tensor_op(U,V) | u⊗v on (A,B), A low; corresponding access on disjoint owners. |
| controlled_op(U) | C(u); Controlled(U), with inverse/control of that actual checked circuit. |
| repeat_op(n,U) | u^n; corresponding access even n0, exact repeated squaring within bounds. |
| conjugate_op(V,W) | v w v†; Apply/Adjoint(V), and Apply/Adjoint/Controlled(W) for each requested access. |

C(u)|0+2x>=|0+2x>; C(u)|1+2x>=sum_y u[y,x]|1+2y>.
Low-control X table[0,3,2,1], not high-control[0,1,3,2]. Unit phase becomes
diag(1,zeta8^k). Controlled conjugation executes V†/controlledW/V with disjoint control,
whole-space V/inverse; encoded range requires separate entry/exit proof. Preserve
arbitrary references/phase. adjoint needs Adjoint, repeat Apply, both qif arms Controlled.

## Examples, lowering and acceptance

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

Both bound Z providers serve one unchanged client. Reject X/-Z/stale dependencies/
changed axes/meaning as contract; missing Adjoint or zero-body access as capability;
iso/observe provider as effect; tree substitution as type_mismatch; reused/aliased
owners as ownership; captures ownership/unsupported. Locate operation/constraint/
provider/conflict; matrix display is unnecessary.

Generic checking uses abstract types/access, then specialization keyed by complete
immutable binding. Resource-only identity placeholders issue no evidence. Rebuild
exact cleanup equations for concrete/zero/unselected bodies; unresolved generic
obligations authorize nothing. Count registry bindings and every expanded call.
FiniteMeaning canonical monomial -> existing FunctionEvidence/Contract actions retain
both programs/full trees/source/dependencies, independently checked at final attachment.
No new core action; old CLI/IR/static/computed contracts and documented AST migration
persist. QIRF1/2 has its own contract, future overrides never apply implicitly.

N1 tests all grammar/resolution/captures/cycles; N2 every-column means/Unit/nested types,
low-control/scalar-phase and collision/stale/layout faults; N3 every capability/zero
body/conjugation; N4 frames/references/empty owners/effects; N5 direct receipt mutations
and exact work/capacity; N6 unchanged-client substitution/adapters/migration. Executed
[operation tests](../tests/operation_parameters.rs) are bounded evidence, not all-size
or general source adequacy proof.
