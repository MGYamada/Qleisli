# QLI quick reference

**Implemented finite source, Qleisli 0.2.4.** Start here and copy a complete program
into `main.qli` in a source directory. Run `cargo run --bin qleisli -- check
<directory>` or `cargo run --bin qleisli -- run <directory>`; append the single
flag `--format=json` for machine-readable results. `run` enumerates the finite
reference distribution; it does not sample a device. All `qli` fences on this
page are complete programs compiled and executed by
[`every_quick_reference_program_compiles_and_executes`](../tests/qli_corpus.rs)
in the existing all-target Rust CI jobs. Other documents may contain proposals.

Every filesystem source tree needs a top-level `Qargo.toml`, even if it is not
a qrate. All current `.qli` and `.qlt` files use Qleisli edition `"2026"`:

```toml
schema-version = 2

[qrate]
edition = "2026"
```

See the [edition and qrate migration contract](language-editions.md).

## Exact phase primitives

Import `std::quantum::{s,sdg,tdg,id,phase_eighth}` directly. S/S†/T† act on
`Q<Bit>`; `id` and `phase_eighth` accept any supported finite `Q<A>`, including
`Q<Unit>`. `phase_eighth(q)` multiplies the full operator by `exp(i*pi/4)`
without an ancilla. Its inverse is `adjoint(phase_eighth,q)`. Phase is retained
under coherent control. The program below returns zero.

```qli
use std::quantum::{init0,h,s,sdg,tdg,t,id,phase_eighth};
use std::observe::measure_z;

observe fn main() -> CBit {
    let q = h(init0());
    let q = tdg(t(sdg(s(id(q)))));
    let q = adjoint(phase_eighth,phase_eighth(q));
    measure_z(h(q))
}
```

See the [exact contracts](standard-library.md#exact-phase-aliases-024).

## Fresh samples and portable verification

From the repository root, these commands exercise the implemented finite APIs:

```sh
cargo run --bin qleisli -- sample examples/bell --shots=16 --seed=0 --format=json
cargo run --bin qleisli -- emit-ir examples/bell --output=bell-ir.json
cargo run --bin qleisli -- verify-ir bell-ir.json --format=json
cargo run --example sampled_shor15
```

The output artifact path must not already exist. `verify-ir` reconstructs its
finite evidence without reading the source. Independently expected unitary
contracts use `--against=<request-file>` and retained exact root type trees;
the closed Bell observation entry has no unary type metadata. See the
[machine contract and host API mapping](machine-interface-spec.md).

`run` still returns the exhaustive distribution. `sample` prepares anew for
each shot, with an explicit seed; neither executes a physical device. The CLI
now limits input to 1 MiB per file and 16 MiB per project. Explicit
`--source-bytes=N --project-bytes=N` or `--legacy-source-limits` provide migration.
The selected `Bits<n>`/`CBits<m>` sized extension is still pending; `CWord` is
not a supported alias. The complete programs below use implemented finite types.

For a qrate with `[source].root = "src"`, use `qleisli check path/to/qrate --qrate`
(or pass `path/to/qrate/src` directly). Only that source directory is traversed;
all its modules are checked. Ordinary commands warn on unused manifest keys.

User-defined finite unary compositions already support an independent source
reference in one call: `apply_contract(provider, expected, q)`. Both names are
separately defined unitary functions with the same exact type tree. For example,
use `provider(q) = h(h(q))` and an independently written `expected(q) = q`;
changing the provider to `h(q)` rejects. This is the existing finite contract
API, not QLT or a whole observing-program specification, and its reference's
intended meaning and source preservation remain separate obligations.

## Ownership and ordinary feedback

Import each operation explicitly; grouped imports such as
`use std::quantum::{h,x};` are also supported. `Q<Bit>` is one owned qubit; using it consumes
that binding. An operation may return its successor under the same name.
`measure_z` consumes its qubit and returns `CBit`. `if` branches on a classical
bit and both arms must return compatible ownership. `false`/`true` are `CBit`;
`0`/`1` are `Bit` in basis computations. Tuples retain immediate arity:
`(a,b,c)`, `((a,b),c)` and `(a,(b,c))` are different shapes, as are their types.
Use matching patterns or an explicit conversion. The [type system](type-system.md)
defines equality and ownership; the [migration guide](tuple-shapes.md) includes
copyable conversion definitions.

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
[A020-09](https://github.com/MGYamada/Qleisli/blob/abe42496fbfccf3ba605ff12cd58c9e7c68dfb45/docs/v0.2.0-backlog.md#a020-09--controlled-access-can-derive-inverse-access-through-constructors).
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
`(Bit,Bit,Bit)` is a flat three-field type and also differs. Ordinary function parameters still
require names. There are no type/size parameters, runtime operation values,
general loops or arbitrary angles in this profile. Finite operation contracts
currently support at most six interface bits and the documented work limits.
Do not infer auxiliary zero return from a variable name, lifetime or successful
type check. Algorithm correctness needs its own oracle or evidence.

For a complete measurement-feedback algorithm, see
[iterative QPE](../examples/iterative_phase_estimation/README.md). Type errors
print expected/actual arity and nesting; check both before adding an adapter.
For unsupported `with_computed` bodies, the diagnostic names the explicit
logical-contract form. Its exact cleanup check must still succeed.

For details, consult [frontend v0](frontend-v0.md), [static operations](static-operations.md),
[M1 forms](next-minor-spec.md) and the [stdlib index](standard-library.md).
The [authoring report](qli-authoring-feedback.md) records runnable counterexamples
and proposed improvements; it is not additional syntax.
