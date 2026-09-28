# QLI quick reference

**Implemented source, Qleisli 0.1.9.** Start here and copy a complete program
into `main.qli` in a source directory. Run `cargo run --bin qleisli -- check
<directory>` or `cargo run --bin qleisli -- run <directory>`; append the single
flag `--format=json` for machine-readable results. `run` enumerates the finite
reference distribution; it does not sample a device. All `qli` fences on this
page are complete programs compiled and executed by
[`every_quick_reference_program_compiles_and_executes`](../tests/qli_corpus.rs)
in the existing all-target Rust CI jobs. Other documents may contain proposals.

## Ownership and ordinary feedback

Import each operation explicitly. `Q<Bit>` is one owned qubit; using it consumes
that binding. An operation may return its successor under the same name.
`measure_z` consumes its qubit and returns `CBit`. `if` branches on a classical
bit and both arms must return compatible ownership. `false`/`true` are `CBit`;
`0`/`1` are `Bit` in basis computations. N-ary tuples
left-associate: `(a,b,c)` and `(CBit,CBit,CBit)` mean `((a,b),c)` and
`((CBit,CBit),CBit)`. Explicit `(a,(b,c))` remains a different tree.

This teleportation sends `|->`. The first two results are independent uniform
message bits; the last is always one. The body is the user-supplied Claude
example with explicit imports added.

```qli
use std::quantum::init0;
use std::quantum::h;
use std::quantum::x;
use std::quantum::z;
use std::quantum::cnot;
use std::observe::measure_z;

observe fn main() -> ((CBit, CBit), CBit) {
    let psi = h(x(init0()));
    let (alice, bob) = cnot(h(init0()), init0());
    let (psi, alice) = cnot(psi, alice);
    let m1 = measure_z(h(psi));
    let m2 = measure_z(alice);
    let bob = if m2 { x(bob) } else { bob };
    let bob = if m1 { z(bob) } else { bob };
    ((m1, m2), measure_z(h(bob)))
}
```

Functions use `unitary` for reversible pure operations, `iso` for pure
isometries including fresh allocation, and `observe` for non-pure operations
including measurement, reset and discard. `basis fn` defines a total classical basis computation.
`pub` exports a declaration from a module; `use bell::prepare;` imports
`pub ... prepare` from `bell.qli` in the same project. There is no implicit
prelude. See [modular protocols](../examples/protocols/README.md).

## Registers, basis predicates and phase kickback

`(Q<Bit>,Q<Bit>)` contains two owners; `Q<(Bit,Bit)>` owns a pair as one register.
`join(a,b)` and `split(q)` change that ownership packaging without copying state.
Product trees are exact types: `Q<((Bit,Bit),Bit)>` differs from
`Q<(Bit,(Bit,Bit))>`. Separate owners may still be entangled. Results print in
tuple leaf order; in QFT/QPE integer labels the first leaf has weight one.

This two-bit Deutsch–Jozsa example uses the balanced predicate `a xor b`.
The output is `11` with probability one. `with_computed` computes a clean flag,
applies its phase and uncomputes it. Its two-argument form admits expanded
identity/Z/T flag bodies; other pure bodies need the explicit logical-operation
contract of the [three-argument form](semantic-contracts-v0.1.md).

```qli
use std::quantum::init0;
use std::quantum::join;
use std::quantum::z;
use std::routines::hadamard2;
use std::routines::measure_z2;

basis fn balanced((a,b): (Bit,Bit)) -> Bit { a xor b }
unitary fn oracle(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    with_computed(q, balanced) { |flag| z(flag) }
}
observe fn main() -> (CBit,CBit) {
    let q = hadamard2(join(init0(),init0()));
    measure_z2(hadamard2(oracle(q)))
}
```

## Reusable operation arguments

Pass an ordinary closed `unitary fn` in brackets, wrapping a sealed gate when
needed. `Op<Bit>` fixes the basis interface; it does **not** declare a generic
type variable. Declare each access separately: `Apply(U)`, `Adjoint(U)`,
`Controlled(U)`. Each permits only its declared direct access to U. The
[M1 constructor rules](next-minor-spec.md#access-judgments-and-composition)
also derive Apply/Adjoint for `controlled_op(U)` and Controlled for
`inverse_op(U)` from `Controlled(U)`, using checked transparent circuits.
This does not extend to future opaque providers; see
[A020-09](v0.2.0-backlog.md#a020-09--controlled-access-can-derive-inverse-access-through-constructors).
`adjoint(U,q)` is inverse application;
`qif(c,q) { 0 => f, 1 => U }` coherently applies branch operations and returns
`(control,target)`, preserving phase. `qif` is not classical `if`.

```qli
use std::quantum::init0;
use std::quantum::h;
use std::quantum::t;
use std::observe::measure_z;

unitary fn eighth_phase(q: Q<Bit>) -> Q<Bit> { t(q) }
unitary fn round_trip[static U: Op<Bit>](q: Q<Bit>) -> Q<Bit>
requires Apply(U), Adjoint(U) { adjoint(U,U(q)) }
observe fn main() -> CBit {
    measure_z(h(round_trip[repeat_op(3,eighth_phase)](h(init0()))))
}
```

The output is zero. Static descriptions include `inverse_op(U)`, `then_op(U,V)`
(U first), `tensor_op(U,V)`, `controlled_op(U)`, `repeat_op(k,U)` and
`conjugate_op(A,V)` (A V A†). These are bracket expressions, not runtime values;
`k` is a literal. An `Op<A,m>` additionally requires the independently checked
meaning `m`, supplied using `bind_op(provider,m)`. See the
[implemented contract example](../examples/operation_contracts/main.qli) and
[operation-parameter algorithms](../examples/operation_algorithms/README.md).

A patterned basis parameter is one argument; names and `_` match the declared
product tree. For phase meanings keep the exact `(Bit,(Bit,Bit))` exponent type:
`(Bit,Bit,Bit)` left-associates differently. Ordinary function parameters still
require names. There are no type/size parameters, runtime operation values,
general loops or arbitrary angles in this profile. Finite operation contracts
currently support at most six interface bits and the documented work limits.
Do not infer auxiliary zero return from a variable name, lifetime or successful
type check. Algorithm correctness needs its own oracle or evidence.

For a complete measurement-feedback algorithm, see
[iterative QPE](../examples/iterative_phase_estimation/README.md). Type errors
print expected/actual binary trees; check association before adding an adapter.
For unsupported `with_computed` bodies, the diagnostic names the explicit
logical-contract form. Its exact cleanup check must still succeed.

For details, consult [frontend v0](frontend-v0.md), [static operations](static-operations.md),
[M1 forms](next-minor-spec.md) and the [stdlib index](standard-library.md).
The [authoring report](qli-authoring-feedback.md) records runnable counterexamples
and proposed improvements; it is not additional syntax.
