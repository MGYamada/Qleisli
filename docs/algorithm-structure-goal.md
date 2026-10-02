# Second development goal: structuring quantum algorithms

Extract reusable structures from actual desired quantum programs; evaluate types,
meanings, access and evidence in executable source. [Design](design-philosophy.md),
[corpus](../corpus/README.md) and [milestones](release-milestones.md) govern adoption.
The declared finite foundation is implemented/checked; generalized v1 remains unmet.

## Release targets and criteria for algorithm structure

V1 requires readable actual Shor, QPE and Grover satisfying V1-C1–C5, with common
components and sizes rather than pseudocode/names. Fix phase, encodings, ownership,
capabilities, scratch, approximation and resource scope before implementation comparison.

| Algorithm | Structure and public obligations |
| --- | --- |
| Shor | Base/classical checks, whole-space reversible modular powers, shared QPE, continued fractions, validated period/factors and typed bounded retries; integer/register size, precision and host work. |
| QPE | Phase-register preparation, controlled powers, inverse QFT, ordered readout and interpretation; phase-fixed access, precision/error/failure and full postmeasurement target/reference instrument. |
| Grover | Preparation, predicate-derived phase oracle, preparation-state reflection, iteration policy, measurement and candidate check; inverse access, marked-count/initial-success assumptions and failure handling. |

Two-bit Grover, QPE2/3 and N=15 remain regressions. The finite contract foundation
supports exact checking, cleanup, retained function evidence and unchanged-client
implementation substitution, without a general Rust soundness proof.

## Common structures to extract

S1 preparation/basis change distinguishes fresh Iso from whole-space invertible
unitary. S2 reversible compute/uncompute fixes total predicates and exact zero for
every input/reference. S3 oracle/reflection fixes O_f=I-2Π_f and R_psi=2\|psi><psi\|-I;
R/-R differ under control. S4 powers/Fourier fixes access, order, phase and angles.
S5 repetition/layers separates descriptions from consumed owners. S6 estimation
requires fresh trials, observable basis and statistical error. S7 syndrome/feedback
requires code-space/error premises and retained data. S8 block encoding/QSVT fixes
normalization, projectors, error and full unitary; success blocks are not pure maps.

## Design contracts for types and composition

Ordinary compose/tensor transfer matching outputs into inputs, use disjoint owners
and join effects. [Static forms](static-operations.md) implement finite same-type
adjoint/qif/repeat; generalized operation types are separately specified in
[M1](next-minor-spec.md). They reject observation/Iso/aliasing and check bodies at
count zero. Conjugation/reflection needs actual inverse and exact phase; init0 inverse
cannot release arbitrary scratch. Instruments retain all CP branches with TP sum;
postselection cannot hide failure. Host estimates freshly prepare each trial.
Block-encoding schemas and general borrowing remain future designs; arbitrary
free-vector bind is not adopted.

## Implementation order and acceptance criteria

Write first desired source/counterexamples, select a bounded contract/checking
experiment, implement/validate, then recombine on another problem with multiple
clients and explicit actual-IR evidence. Initial A0 corpus organization, A1 finite
routines, A2 finite static QFT/QPE, A3 N=15 arithmetic and A4 exact finite contracts
are completed within their scopes; general sizes, VQE/QAOA, generalized evidence
and the three theorem pillars remain open. Query/synthesis/preparation/measurement/
classical costs are separate. [Routine contracts](algorithm-routines.md) and
[stdlib goal](stdlib-roadmap.md) record current components and future adoption.
