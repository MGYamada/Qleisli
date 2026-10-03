# Second development goal: structuring quantum algorithms

Extract shared structure from desired source and bounded checking experiments; [corpus](../corpus/README.md)/[design](design-philosophy.md)/[gates](release-milestones.md). Finite foundation checked, general v1 unmet.

## Release targets and criteria for algorithm structure

V1-C1-C5 readable executable Shor/QPE/Grover with shared sizes/components, not pseudocode/names. Fix phase/encoding/owners/access/scratch/error/resources. Shor classical base checks/reversible whole-space modular powers/shared QPE/continued fractions/validated period+factors/bounded retries; QPE prep/controlled powers/inverse QFT/ordered readout/full target-reference instrument/precision-failure; Grover predicate phase/preparation reflection/iteration policy/readout/candidate validation/inverse/marked-count-success premises. Two-bit/QPE2-3/N15 regressions not general proof.

## Common structures to extract

S1 fresh Iso vs invertible basis change; S2 total compute/uncompute/exact all-reference cleanup; S3 O_f=I-2Pi_f,Rpsi=2|psi><psi|-I (sign under control); S4 powers/Fourier/access/order/angles; S5 descriptions vs owners/repeated work; S6 fresh estimation/observable/statistical error; S7 code-space/error syndrome/feedback/retained data; S8 block-encoding/QSVT normalization/projectors/error/full unitary,success block not pure map.

## Design contracts for types and composition

Match interfaces/disjoint owners/effect join; [static](https://github.com/MGYamada/Qleisli/blob/v0.2.7/docs/static-operations.md)/[M1](next-minor-spec.md) require actual access/body evidence incl zero. No init inverse release/opaque control. Retain all instrument branches/TP,postselection failure explicit,host fresh trials. Borrowing/block schemas/free-vector bind not current API.

## Implementation order and acceptance criteria

First source/counterexample->bounded experiment->implementation/validation->held-out recombination/multiple clients/actual IR. A0-A4 finite organization/routines/static QFT-QPE/N15/exact contracts completed scoped; sizes/VQE-QAOA/generalized evidence/theorems open. Query/prep/synthesis/measurement/host costs separate; [library goal](stdlib-roadmap.md).
