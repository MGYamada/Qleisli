# Requirements for a quantum programming language

Adopted English requirements; [finite language](language-spec.md)/[formal scope](formal-core.md), not all implemented/proved.

## Semantics and purity

Q1 H(A)=C^A,Iso V†V=I,Unitary also VV†=I,retain scalar phase/termination/static finite loops,no unrestricted free-vector bind. Q2 declarations load without operations/implicit mutable quantum state/I/O; Q ownership not effect, Observe probabilities vs host/device/file effects.

## Quantum resources and auxiliary systems

Q3 linear exclusive rights/no duplicate/alias/reuse/implicit disposal,explicit Observe discard,split/join no separability/general borrowing. Q4 Bit labels vs CBit,injective basis-copy lift allowed,unknown state cloning/constant pure lift not. Q5 exact zero/factorization every input/reference,legacy protected labels or [SC](finite-contracts.md) W Ef=Ef u; no protected observation/reset/discard/name/lifetime evidence.

## Observation and control

Q6 whole-reference Observe CP/TNI per outcome/TP sum,measure consumes/reset fresh/discard correlations explicitly. Q7 classical branches same exclusive context/compatible outputs,qif retains control/same-type unitary arms/full phase; if alone not measurement.

## Requirements for an executable language

Q8 preparation/interference/entanglement/oracles/partial observation/feedback,closed main classical/no owners. Q9 std ordinary user checks,sealed meanings/checked forms/evidence validity,execute accepted core/meaning-preserving supported backend. Q10 local operations/function boundaries retain arbitrary correlations; only Q5 pure cleanup/Q6 explicit loss. Q11 prove finite resource/instrument soundness under actual valid primitives/lifts/cleanup/composition; compile success alone not physics, [three theorem gates](release-milestones.md).

## Acceptance examples and research

Accept injective copy/compute-Z-uncompute/Bell-half measure or discard/feedback X. Reject copied owner/constant Bit lift/protected observation/pure disposal/Bell-half release from ownership. QML/Qurts/OpenQASM/QIR prior work, not implementation proof.
