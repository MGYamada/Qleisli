# Shared language and contract requirements

Design requirements shared by the six [imaginary drafts](index.md), not adopted generic APIs. Existing bounded source/components have separate contracts and status.

## Requirement matrix

L=language, B=sealed built-in, D=ordinary-definition candidate; unresolved classifications need a decision. Host-only processing is not a current quantum API.

| ID | Facility and independent checking obligation |
| --- | --- |
| R01 | Static finite `Bits<n>`, explicit ordered types/axes/bounds; quantum zero width stays owned, ordinary Bits values remain copyable. |
| R02 | Static operation descriptions capture no owners; bind actual body, full signature, phase and dependencies. Matrix values grant no gate access. |
| R03 | Adjoint/control/powers need separate capabilities; retain all owners/phase, count actual repeated uses. |
| R04 | Finite carry/axis helpers return complete interfaces; check even zero bodies, partitions/reassembly/nonaliasing. Lifetime is not cleanup. |
| R05 | Derived fresh initialization Iso; consuming measure/discard Observe with every outcome/reference/residual owner. |
| R06 | Total predicates and reversible synthesis; actual compute/use/uncompute with exact reference-stable zero return, without whole-space tables. |
| R07 | Fix 2Π-I versus I-2Π and exp(iφ(2Π-I)); require actual preparation/inverse or certified synthesis. |
| R08 | QFT/rotations fix domain, sign, order, error metric and synthesis/composition budget; approximate target does not relax cleanup. |
| R09 | Coprime modular arithmetic needs full-space padded action, inverse, efficient circuit, exact phase/powers/scratch. |
| R10 | Walk row normalization/promise is not free coherent access; bind full unitary extension, inverse, padding and costs. |
| R11 | Projected-unitary/QSVT evidence fixes scale/projectors/parity/bounds/phase synthesis/error; preserve full output, never purely release a success block. |
| R12 | Instruments retain CP outcomes with TP sum, conditional states, failure branches and explicit accuracy/statistical assumptions. |
| R13 | Host orchestration: fresh actual samples, verified classical candidates, finite retries, errors/exhaustion and counted work; no distribution-as-sample. |
| R14 | Reusable evidence fixes types, phase, complete owners, entry encoding/layout and source/dependency/final-IR binding; finite SC/FC is not arbitrary-n proof. |

R01–04 are proposed language/structural forms; R05–10 are ordinary-definition
candidates where derivable, requiring separate adoption for new primitives.
R11–12 need new independently checked contract families; R13 is host-only;
R14 generalizes the existing evidence boundary. These classifications leave
operation representation, angle primitives, coherent access and evidence schemas
open. No table entry adopts an API.

## Intended acceptance and rejection boundaries

Local IDs preserve their algorithm-specific contracts and open obligations; shared rows do not replace them.

| Draft records | Shared requirements |
| --- | --- |
| [QPE-SIZE, ACCESS, AXIS, FOURIER, OBSERVE, DECODE](https://github.com/MGYamada/Qleisli/blob/b316a5065527c84f3dbcb059750637e2b14b0965/docs/imaginary-v1/qpe.md) | R01–R05, R08, R12–R14 |
| [GR-1–GR-6](https://github.com/MGYamada/Qleisli/blob/b316a5065527c84f3dbcb059750637e2b14b0965/docs/imaginary-v1/grover.md) | R01–R07, R13–R14 |
| [AE-1–AE-5](https://github.com/MGYamada/Qleisli/blob/b316a5065527c84f3dbcb059750637e2b14b0965/docs/imaginary-v1/amplitude-estimation.md) | R02–R08, R12–R14, with R01/R04 inherited from QPE |
| [SHOR-MUL, POW, QPE, CLASSICAL, SAMPLE](https://github.com/MGYamada/Qleisli/blob/b316a5065527c84f3dbcb059750637e2b14b0965/docs/imaginary-v1/shor.md) | R01–R06, R08–R09, R12–R14 |
| [WALK-1–WALK-5 and WALK-O1–O5](https://github.com/MGYamada/Qleisli/blob/b316a5065527c84f3dbcb059750637e2b14b0965/docs/imaginary-v1/quantum-walk.md) | R01–R05, R07–R08, R10, R12, R14 |
| [QSVT-1–QSVT-6 and QSVT-O1–O5](https://github.com/MGYamada/Qleisli/blob/b316a5065527c84f3dbcb059750637e2b14b0965/docs/imaginary-v1/qsvt.md) | R01–R08, R11–R14 |

## Intended acceptance and rejection examples

Future profiles accept bounded distinct owners, explicit access/phase/error premises,
fresh trials and independently bound complete instruments. Retain counterexamples
for alias/reuse/capture/unchecked zero bodies, initializer inversion, unknown-state
reflection, opposite controlled sign/approximate cleanup, bit reversal/unsupported
angles/noncoprime or partial-space arithmetic, stochastic-as-unitary/projected success,
unchecked polynomial phases, hidden failures/unverified factors and stale evidence.
These requirements do not enlarge current acceptance; finite tests are not compiler proofs.

## Decisions still open and order of work

Before a feature is selected, specify English grammar/types/effects/ownership, IR, meanings/checker, limits/migration and independent acceptance/fault tests. M1 is fixed-width; M2 adds evidence-bound sharing/sizes; M3/M4 require efficient synthesis. Actual bounded implementation does not adopt all imaginary notation.

### R02 notation and representation alternatives

The two draft static-parameter syntaxes and operation-returning builders are alternatives, not interchangeable APIs. M1 uses checked static access constraints; wrapper/constraint/evidence-producer roles cannot infer control from unitarity. Controlled V W V† derives from V/inverse and controlled W with exact phase; [fixed-width tests](https://github.com/MGYamada/Qleisli/blob/main/tests/operation_parameters.rs) cover that rule, not generic builders.

### Scaling prerequisite for R14

R14 requires symbolic compositional meanings and encodings without global dense matrices before size generalization. Current finite then/tensor/adjoint/control/extraction remain dense bounded reference paths. Shared typed derivations must bind actual implementations/dependencies/final IR, phase, axes and encodings; differing symbolic terms need checked equality evidence. A name/hash/simplifier cannot grant universal equality. Demonstrate independent bounded checking and interface/stale-evidence faults without full expansion.

### Complementary scaling gates: R02/R04 and R06/R09

R14 alone removes neither exponential basis tables nor expanded calls. R02/R04 need hierarchy/calls/folds jointly bound to evidence; R06/R09 need reversible circuit synthesis without whole-space truth tables. Cost/phase/full-space arithmetic/clean return remain separate scaling gates.

### First generalized QPE profile: decisions required by R08/R12/R14

Fix widths, phase angles/domain, exact or approximate realization, independent evidence, budgets/diagnostics and instrument/error conventions. Width four needs exp(i pi/8), outside R8. M2 selects bounded ideal exact dyadic phases; backend approximation is separate and cannot weaken exact scratch. Hierarchy fixes its selected profile; this requirement adds no primitive or production authority.
