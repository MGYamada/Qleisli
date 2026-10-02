# Requirements for a quantum programming language

Adopted requirements, English authoritative. They constrain design/implementation;
not all are proved guarantees. [Language v0](language-spec.md) implements a finite
profile; [formal core](formal-core.md) distinguishes actual proofs from intended scope.

## Semantics and purity

**Q1:** H(A)=C^A. Iso V satisfies V†V=I on the whole domain; Unitary also VV†=I.
Retain scalar phase in IR/control. Pure programs terminate; initial loops are static
finite. Arbitrary free-vector bind is not an execution API.

**Q2:** Loading declarations performs no operations. Compose explicit transformations
of values/owners without implicit mutable quantum state/I/O. Q<A> is ownership,
not an effect. Observe accounts for probabilities; host/device/file effects are separate.

## Quantum resources and auxiliary systems

**Q3:** Linear exclusive operation rights reject duplicates, wire aliases, implicit
disposal and use after consumption. Discard is explicit Observe. Split/join rebind
handles, not product-state assertions. Current capture/disjointness rules do not
implement general borrowing.

**Q4:** Basis labels are not measured CBits. Injective x->(x,x) may lift coherently;
Q ownership cannot copy, noninjective x->0 cannot lift purely.

**Q5:** Pure release requires exact zero return and factorization for every input/
reference. Restricted compute/use/uncompute preserves source/auxiliary labels;
[SC](finite-contracts.md) instead checks actual W E_f=E_f u and permits relation-preserving
joint changes. Both reject protected measurement/reset/discard. Lifetime/name alone
is not zero-return evidence.

## Observation and control

**Q6:** Measurement/reset/discard are Observe. Each outcome is CP/TNI and their sum TP
on the whole entangled system/reference. measure_z consumes the logical wire;
reset/discard lose correlations explicitly, physical reuse prepares a different owner.

**Q7:** Classical if arms exclusively receive the same context and return compatible
ownership. qif retains control and same-type unitary target arms, preserving relative
phase. Classical branching alone is not measurement.

## Requirements for an executable language

**Q8:** Express known preparation, interference, entanglement, predicate phase oracles,
partial measurement and feedback. Closed main returns classical data and no owners.

**Q9:** Ordinary std definitions obey user checking. Sealed operations/checked forms
mediate gates, lifts, measurements, structure and cleanup. Check evidence validity,
not presence; execute the accepted core and reject or meaning-preservingly translate
unsupported backend features.

**Q10:** Ownership does not imply separability. Local operations/partial observations
retain arbitrary references; only Q5 evidence authorizes pure release, Q6 permits
observing correlation loss.

**Q11:** Prove finite terminating type/resource safety and instrument semantics under
valid primitives, checked lifts/cleanup and composition. Until actual frontend/IR
acceptance is connected to these premises, compile success is not proved physical
validity. [Three theorem gates](release-milestones.md) remain distinct.

## Acceptance examples and research

Accept injective basis-copy, certified compute/Z/uncompute, Bell-half measurement/
explicit disposal and outcome-driven X. Reject copied owners, constant Bit lift,
protected observation, unsupported pure disposal and Bell-half release from ownership
alone. [QML](https://people.cs.nott.ac.uk/psztxa/publ/qml.pdf),
[Qurts](https://arxiv.org/pdf/2411.10835), [OpenQASM3.1](https://openqasm.com/versions/3.1/language/insts.html)
and [QIR Adaptive](https://github.com/qir-alliance/qir-spec/blob/main/specification/profiles/Adaptive_Profile.md)
are prior work, not Qleisli proofs.
