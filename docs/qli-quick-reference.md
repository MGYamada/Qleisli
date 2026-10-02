# QLI quick reference

Implemented finite edition2026 source. Each complete program below is compiled/executed by [CI](../tests/qli_corpus.rs). Put main.qli in a source tree with this Qargo.toml:

```toml
schema-version = 2
[qrate]
edition = "2026"
```

`qleisli check PROJECT`, `run PROJECT`, `sample PROJECT --shots=16 --seed=0`; --format=json opt-in. run exhaustive floating reference, sample fresh seeded trajectories, neither hardware. emit-ir --output=NEW exclusively creates; verify-ir freshly reconstructs evidence, --against requires independent unitary request/exact retained trees. [Machine contract](machine-interface-spec.md). Source defaults1 MiB/file/16 MiB/project with explicit overrides/legacy policy; --qrate selects manifest source root.

## Exact phase primitives

s/sdg/tdg on Bit, id/phase_eighth on exact finite A incl Unit; phase_eighth=zeta8 I survives control. This returns0:

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

## Ownership and ordinary feedback

Q owns/moves once, measure_z consumes; if checks compatible owners in both arms. CBit true/false differ from basis Bit0/1; flat/nested tuples differ. Separate owners may be entangled. Explicit imports/pub module exports. Effects Unitary<=Iso<=Observe. Teleport |->; two uniform messages then1:

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

## Registers, basis predicates and phase kickback

join/split change binary ownership packaging, no state copy; first QFT/QPE leaf low bit, result display tuple order. Legacy computed body expanded empty/Z/T; broader body needs [SC equation](finite-contracts.md). This returns11:

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

Static Op<Bit> is exact description, no runtime closure/type generic. Declare Apply/Adjoint/Controlled separately; unitarity grants no access. qif(c,q){0=>f,1=>U} retains distinct control/target and phase. Constructor laws [M1](next-minor-spec.md), including transparent controlled/inverse derivations. This returns0:

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

Descriptors inverse_op/then_op(U first)/tensor_op/controlled_op/repeat_op(literal count)/conjugate_op(A,V)=AVA†. Op<A,m> requires checked bind_op(provider,m); [examples](../examples/operation_contracts/main.qli). Finite contracts<=6 bits/full tree/order/phase/cleanup/budgets; phase exponent uses exact (Bit,(Bit,Bit)), not flat triple. No generic finite sizes/loops/arbitrary angles. [Sized experiment](sized-corpus-source.md) separate; CWord unsupported. [Types](type-system.md)/[frontend](frontend-v0.md)/[iterative QPE](../examples/iterative_phase_estimation/README.md) cover further use. Algorithm meaning requires independent evidence, not successful typing/lifetime.
