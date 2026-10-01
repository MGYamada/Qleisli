# Fixed-width operation parameters and meaning contracts (M1)

Normative fixed-width M1 supplement, selected 2026-09-27/implemented 0.1.8. [Language v0](language-spec.md), [static forms](static-operations.md), [machine interfaces](machine-interface-spec.md) and [M2](hierarchical-ir-spec.md) retain separate contracts/gates. Tuple arity/nesting follows [current types](type-system.md); phase result remains (Bit,(Bit, Bit)), not flat triple. Shipping this slice does not complete all M1/G020 gates; [historical migration](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/releases/v0.1.8.md) records adoption/public changes.

## Scope, vocabulary and limits

Static Op is a copyable compile-time description of phase-fixed unary unitary Q<A>→Q<A>, including zero owners, carrying meaning and separately checked access; no quantum/classical runtime capture. Fixed Unit/Bit/ordered tuples only. Forms add no sealed gate/new effect/runtime closure/general builder/size API. Existing computed contracts remain.

Caps: 0–6 bits, contract circuit 1024 steps, repeat 0–4096, type/syntax depth 64, type4096 nodes, 256 distinct project specializations/depth 64, aggregate lowering 1M. Control/tensor entire interface counts. Shared exact 10M covers meaning/provider/contract/transforms/final verifier, even unused arguments; no per-callee reset, limit on exhaustion. One frozen full-project snapshot includes every loaded module/comments/std; charge once before copy, retain strong reference preventing allocation identity reuse. Metadata/name/path/pair work and exact equations still checked for every receipt; public owned identity retains full byte charge. Shared storage gives no unconditional 256-provider capacity. Powers exact repeated squaring. [Frontend limits](frontend-v0.md)/[FC-CACHE](function-contracts-v0.1.md) govern all copied/lowered work.

## Grammar and resolution

Grammar below extends v0. Name means local/imported declaration, no qualified expression; Nat decimal no leading zero except 0, no trailing comma. QuantumDecl includes pub once. Static/runtime parameter names share namespace; descriptors appear only static operands or unary callees, never runtime let/tuple/result/basis expression. Reserve all literal form/constraint names shown. Meaning/function namespace and import visibility shared; meaning names one ordinary total basis function, not another meaning/parameter.

Explicit arguments in declaration order, no inference. Evaluate runtime arguments left-to-right/pending owners first, then static callee/args in residual scope. Live/spent local bindings shadow globals/static parameters; no resurrection. Header access resolves before body. Check all declarations/zero bodies; provider call graph acyclic. Existing adjoint/repeat_static/qif name operands additionally admit static parameter names, not constructor expressions. Pass constructed operations through brackets. apply_contract/with_computed name/cleanup rules unchanged.

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

Flatten Bit leaves left-to-right, first low bit, preserving complete tree/Unit identity. Targets below require ordinary unary basis functions and exhaustive bounded tables; permutations total/bijective, phase total right-associated triple, modulo 8. Reject missing/colliding outputs, wrong trees/equal-width coercion/floats/equality modulo scalar. Unit scalar remains observable under control.

`bind_op(u,m)` requires closed ordinary declared unitary with exact Q<A> signature, fresh verified lowering/exact ordered operator equality. Bind full meaning/tree/raw IR/ports/source/dependency DAG; changing any dependency invalidates. Names/digests/cache claims grant no evidence. Plain transparent provider derives its meaning from verified circuit; bind_op adds independent target. Op<A, m> requires exact fixed meaning; Op<A> parameterizes argument phase-fixed meaning. No phase/layout/encoding/access coercion. Scratch only through existing exact zero-entry/exit certificates and full external frame.

```text
permutation_by(f): f : A -> A is total and bijective
                  P_f |x> = |f(x)>
phase_by(phi):     phi : A -> (Bit,(Bit,Bit)) is total
                  D_phi |x> = zeta_8^(b0 + 2*b1 + 4*b2) |x>
```

## Access judgments and composition

Body uses only declared direct access: Controlled(U) alone permits neither U(q) nor adjoint(U, q). Constructor-derived controlled/inverse circuit access in table remains accepted M1; transparent actual verified circuits supply transforms, opaque providers excluded. Tightening these supported derivations requires MINOR. Every derived circuit fits caps. Constructor operands/premises checked even when result cancels or repeat 0. Failed extraction is unsupported, never assumed unitary access.

Table gives meanings and capabilities. Controlled coordinates c+2x, first control low bit; regrouping P|c+2x>=|c*d+x> gives C=P†diag(I, u)P. X table [0, 3, 2, 1], high-control [0, 1, 3, 2] wrong; Unit scalar yields diag(1,ζ8^k). Extend to arbitrary references. Controlled conjugation executes V†, controlledW, V with distinct control; whole-space V/matching phase-fixed inverse required, encoded range needs its separate entry/exit proof.

Parameter call consumes/returns one Q<A>, unitary joined with argument effect. adjoint needs Adjoint; repeat Apply; qif Controlled for both arms/disjoint owners. Generic declared effect stays visible at every call/zero body. Generic iso/observe may call operations; providers themselves unary declared unitary.

| Constructor | Meaning/interface | Access required for Apply; for Adjoint; for Controlled |
| --- | --- | --- |
| `inverse_op(U)` | u† on A | Adjoint(U); Apply(U); Adjoint of a checked controlled-U circuit |
| `then_op(U,V)` | v u on identical A | Apply of both; Adjoint of both in reverse execution order; Controlled of both |
| `tensor_op(U,V)` | u tensor v on (A,B), A's bits first | Corresponding access to both on disjoint ports |
| `controlled_op(U)` | C(u) on (Bit,A), with index c+2x as defined below | Controlled(U); inverse of that checked circuit; control of that checked circuit |
| `repeat_op(n,U)` | u^n on A | Corresponding access to U even when n=0; checked count and repetition |
| `conjugate_op(V,W)` | v w v† on identical A | Apply/Adjoint(V) and Apply(W); Apply/Adjoint(V) and Adjoint(W); Apply/Adjoint(V) and Controlled(W) |

```text
C(u) |0+2x> = |0+2x>
C(u) |1+2x> = sum_y u[y,x] |1+2y>.
```

## Accepted and rejected examples

Executable provider/client examples below retain independently fixed Z and result exact I, subject to budgets. Rejections require the listed versioned categories and located operation/constraint/provider/conflicting declaration; internal matrices need not be displayed.

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

## Lowering and compatibility

Check generic type/effect/ownership/composition using abstract operations and declared access, then explicit specialization keyed by full immutable binding. Resource-only identity placeholders issue no executable evidence. Concrete specialization rebuilds/checks every exact cleanup equation, including zero/unselected source bodies; uninstantiated obligations authorize nothing. Project registry counts bindings, each call expansion still charges work.

FiniteMeaning lowers independent target to canonical monomial raw IR; MeaningEvidence uses existing FunctionEvidence, retaining both programs/full tree/source/dependencies. Final CircuitAction:: Contract binding is independently checked; no new core action. Existing IR consumers unchanged; public AST/tokens/diagnostics need the documented 0.1.8 migration. Old static forms keep evaluation/shadowing/effects/phase/tree/zero checks, computed forms their distinct premises. Portable QIRF now follows [its separate contract](machine-interface-spec.md); proposed future capacity overrides do not apply implicitly.

## Implementation acceptance matrix

N1–N6 are slice acceptance requirements; executed results live in retained release/fixture records. G020-2 shipping implementation and G020-3 validation/ledger remain separate from adoption; no symbolic all-size/source adequacy theorem is asserted.

| Gate | Required evidence (implementation validation in the release record) |
| --- | --- |
| N1 grammar/resolution | Parse every new production and reject category misuse, duplicate static names, missing arguments, captures, cycles and runtime operation values; preserve old parser/name-resolution cases. |
| N2 meanings | Compare all columns for permutation and phase fixtures on Unit, Bit and nested pairs; include low-bit controlled-X `[0,3,2,1]`, reject the high-bit control table `[0,1,3,2]`, and retain controlled scalar phases on Unit; reject collisions, wrong trees, minus-sign changes, stale sources and output permutations. |
| N3 capabilities | Parametric body rejects missing access before specialization; test all constructors, unavailable zero-repeat access, both qif arms and conjugation with non-Hermitian V and phased W. |
| N4 ownership/effects | Preserve pending frames, entangled references, Q<Unit>, declared effects and all old computed/static rejection cases. |
| N5 binding/limits | Feed independently mutated target/receipt attachments directly to the verifier; enforce exact arithmetic/work/width/instance limits without recursion or unchecked allocations. |
| N6 reuse/migration | Compile and execute the two providers above through one unchanged client; exercise the canonical target/existing-receipt adapter, retain old CLI behavior, and document reserved-name/public API migration. |
