# Finite routine contracts and algorithm clients

Ordinary source, not extra sealed operations. [Ledger R001–R005](stdlib-contracts.md)
fixes signatures, owners/effects/operators/costs and independent regressions;
[code](../stdlib/src/routines.qli) receives the same production checks as user code.

## Reflection phase

```text
R0 = diag(1,-1,-1,-1) = 2|00><00|-I
D = (H⊗H) R0 (H⊗H) = 2|s><s|-I
```

Marking zero instead yields -D, distinguishable under control. Source nonzero2 uses
protected Z and exact compute/uncompute; no lifetime or approximate-zero substitute.

## Whole-system meaning of parity measurement

```text
P_s = (I+(-1)^s Z_a Z_b)/2
E_s(rho) = (P_s⊗I_R) rho (P_s⊗I_R), s in {0,1}
```

Retain both separately owned data wires, consume fresh meter. Preserve parity-sector
coherence/arbitrary references: |++> yields equiprobable Bell residuals. Two individual
Z measurements then XOR is a different instrument. measure_x consumes its target and
reports eigenvalue(-1)^b; measure_z2 consumes pair, returning left/right in low-bit order.

## Composed algorithm examples

Grover preparation Iso, oracle/step Unitary, readout Observe. One marked label of four
has theta=pi/6 and success sin²((2k+1)theta); all targets/k0..4 tested, extra iterations
can overshoot. BV assumes total linear f_s and uses H² O_s H²|00>=|s>; typing does not
prove the linear promise. All four secrets reuse preparation/readout.

Ideal three-wire bit-flip code assumes code space/at most one X error. Syndromes
I/Xa/Xb/Xc=00/10/11/01. encode:Q<Bit>->Q<((Bit,Bit),Bit)> Iso injectively lifts
b->((b,b),b), not state cloning. recover Observe returns data plus two classical
syndrome bits using parity checks/conditional X. decode Unitary returns
(Q<Bit>,(Q<Bit>,Q<Bit>)) by CNOT(a,b),CNOT(a,c), preserving all owners.
D_dec C_s E V|psi>=|psi>⊗|00>, reference-stable; zeros still require explicit disposal.
Z/two-X errors remain counterexamples, not typing guarantees.

## Execution and verification

[Algorithm tests](../tests/algorithms.rs) cover contracts, phases/correlations and misuse.
[Protocols](../examples/protocols/README.md), [operation clients](../examples/operation_algorithms/README.md)
and [iterative QPE](../examples/iterative_phase_estimation/README.md) are example APIs,
not std additions. Grover/BV/code mains ideally return11/10/11000; finite f64 checks
at1e-12 are distinct from general compiler/algorithm/hardware proofs.

```sh
cargo run --bin qleisli -- run examples/grover
cargo run --bin qleisli -- run examples/bernstein_vazirani
cargo run --bin qleisli -- run examples/bit_flip_code
cargo test --test algorithms --test project
```
