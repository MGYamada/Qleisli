# VM-23 exact arithmetic boundary

Status: **scalar and general matrix meaning, canonicality, capacity and work
proofs and the adopted VM-23 arithmetic/comparison gates are satisfied in the
working tree**. Production evidence/transport remains in later packets. Integration is tracked in
[Issue 99](https://github.com/MGYamada/Qleisli/issues/99).

Contract fixed before implementation. This packet moves the existing R8 exact
arithmetic into the Mathlib-free executable kernel. Rust source parsing,
diagnostics, coefficient/circuit proposals and simulation stay outside it.
Production Rust acceptance and installation remain unchanged until VM-28/29.

The preserved [H/T source](first_source/main.qli) and
[wrong scalar](wrong_scalar/main.qli) lead the comparison. The latter has the
same ordinary measurement distribution but differs under coherent control.
They are original local fixtures, not a new external corpus. The enclosing
test-tree manifest selects edition 2026. Real diagnostics and first hashes
are retained with the validation record.

## Fixed coefficient and work contract

- Scalars mean `a + b*sqrt(2) + i*(c + d*sqrt(2))`, with four independently
  normalized dyadics. Denominator exponents are not merged across coefficients.
  Zero has numerator/exponent `(0,0)`; a nonzero coefficient has exponent at most
  126, and an odd numerator whenever the exponent is positive.
- Preserve signed i128 numerators, unsigned u32 input exponents, checked
  intermediate order and overflow failures. Normalize even numerators before
  checking the canonical exponent, but never after accepting numerator overflow.
  A zero coefficient accepts any u32 exponent and canonicalizes to `(0,0)`.
- Addition aligns denominators with checked positive powers; scalar multiplication
  visits the sixteen coefficient pairs in Rust's existing order, multiplying by
  2 for paired sqrt(2) factors and negating paired i factors before accumulation.
  Negation/conjugation of i128::MIN fails. Equality is exact, retaining global phase.
- Matrices are nonempty row-major with dimensions at most 64. Composition means
  left times right, charging `2*left.rows*left.cols*right.cols` before arithmetic.
  Tensor puts the first operand on low-order bits and charges output cells;
  adjoint charges input cells. Failed arithmetic retains a successful prior
  work charge; failed charge leaves the remaining work unchanged. A shared
  budget cannot reset between operations. Rust source-storage bookkeeping is
  producer accounting, separate from this scalar-operation budget.
- Independently reviewed reference definitions import no acceptance module.
  Successful actual operations must agree with the separate complex meaning;
  canonical equality must agree with that meaning. No floating tolerance or
  equality modulo phase issues arithmetic evidence.

Native differential experiments compare the actual Lean definitions, the
existing Rust exact API and independent rational/complex formulas. Use small
H/T/Unit matrices, signed extrema, denominator normalization, cross terms,
conjugation, scalar phase and exhausted shared work. Capacity probes use small
data or malformed dimensions, without new maximum-size corpus runs. This packet
does not implement serialized circuit evidence, raw IR or production dual checking;
those remain VM-24–VM-29 gates.

## Actual boundary and proof coverage

The [executable definitions](../../../lean-kernel/QleisliKernel/Exact.lean)
receive original coefficients and matrices, recompute canonical coefficients,
arithmetic and remaining work, and return a result or explicit failure. The
[native harness](../../../scripts/test_lean_exact.py) sends no Rust decision or
claimed matrix to Lean. Rust's unchanged `contract::exact` API is a separate
comparison path. No native runtime is required by the production Rust CLI.
Matrices supplied to internal operations must have been constructed from valid
canonical scalars; raw public data constructors alone issue no evidence.

The [data reference](../../../lean-kernel/QleisliKernel/Semantics/Exact.lean)
and [independent complex meaning](../../../lean/Qleisli/Semantics/Exact.lean)
import no arithmetic/acceptance module. The
[actual-definition proofs](../../../lean/Qleisli/Exact.lean) establish:

- Every normalization step and successful coefficient construction preserves
  its rational value. Successful construction produces a canonical coefficient.
- Canonical coefficient equality is exactly rational equality; canonical scalar
  equality is exactly equality of the full complex meaning, using irrationality
  of sqrt(2). Global phase is retained, including the scalar on `Unit`.
- Successful coefficient addition, multiplication and negation preserve their
  rational meanings. The executable work charge consumes exactly its cost on
  success and leaves work unchanged when exhausted.
- Actual T-times-H composition produces the explicit H/T matrix with 16 units;
  its actual isometry computation succeeds with 20 units. Its full complex
  amplitudes and norm preservation are proved for arbitrary input amplitudes
  and each arbitrary reference-system index.

The 2026-10-01 #99 continuation proves full scalar addition, negation,
conjugation and sixteen-pair multiplication against independent complex meaning.
The [general matrix bridge](../../../lean/Qleisli/ExactMatrix.lean) proves actual
successful composition, tensor and adjoint entry formulas and arbitrary-reference
action. Tensor's first operand occupies the low coordinates. Actual isometry
acceptance implies the whole-space Gram identity, inner-product preservation
between arbitrary reference indices and joint norm preservation. One-dimensional
`Unit` operations retain the complete scalar, including phase -1.

The [pure matrix proofs](../../../lean-kernel/QleisliKernel/ExactMatrix.lean)
establish admitted dimensions, storage and canonical scalars. Input canonicality
is explicit where conjugation retains coefficients. Every outcome after successful
precharge retains exactly the reduced work, including arithmetic failure; early
shape/dimension rejection and failed charge leave work unchanged. Successful
isometry charges adjoint plus Gram composition. Failed isometry retains exactly
the cost of the stages already charged. Sequential laws add successful costs
and preserve earlier charges when a later operation fails.

The [capacity proofs](../../../lean-kernel/QleisliKernel/ExactCapacity.lean)
show that 128 normalization steps cover every signed i128 numerator independently
of its exponent. Canonical construction is unchanged; admitted construction is
equivalent to the bounded input exponent and normalized exponent checks.
Positive alignment factors at 2^127 reject. Canonical exponent sums fit u32;
matrix cells, tensor dimension products before validation, row-major indices
and operation costs fit even 32-bit usize. These universal bounds do not run
maximum-size corpus cases.

## Runtime correspondence boundary

[Runtime/capacity validation](runtime-capacity-contract.json) records 815 actual
Rust/Lean comparisons, 551 independent rational checks, 75 matrix checks,
24 named capacity/failure-order probes and seven detected mutations. It pins
Lean, native compilers, Rust, platform word width and source/audit identities.
The common domain uses canonical scalars, admitted matrices and machine-sized
budgets; raw Lean constructors admit additional states. Error-tag comparison
does not establish Rust's dimension/count diagnostic payloads. Some internal
evaluation orders differ while preserving the compared result and remaining work.
Rust source-storage allocation accounting is separate from this arithmetic budget.

Compiled audits and fresh Lean replay check proof/runtime policy. Executing the
audited definitions retains the declared compiler/runtime assumptions in the
[migration policy](../../../docs/lean-kernel-migration.md#audit-and-remaining-trust).
The adopted [VM-23 gate](../../../docs/verification-migration-v0.2.md#vm-23-exact-meanings-without-a-domain-change)
requires proofs about the actual Lean definitions and compatibility comparison
with Rust. A general correctness/refinement proof of the old Rust arithmetic
is not a prerequisite: Rust is a comparison path, and the proved replacement
checks original inputs independently. No formal guarantee for the Rust checker
is claimed by these Lean proofs. The previous extra correspondence blocker was
an overly broad completion criterion, corrected in the [scope review](scope-review.json).

Serialized finite circuit/encoding/evidence reconstruction remains VM-24;
immutable artifact/request binding, checked execution and supported native
transport/platform integration remain VM-28/29. Source-to-IR meaning preservation
is a separate obligation; checking a valid IR does not establish what its source meant.

[First-slice native validation](native-validation.json) records 671 Rust/Lean comparisons,
479 independent rational comparisons, 71 independent matrix comparisons and
four detected phase/axis/refund/reset faults. Ordinary arithmetic matrices have
dimension at most four; dimension/capacity probes use small lists and no new
maximum-qubit corpus. [Source validation](source-validation.json) retains both
first hashes, actual diagnostics and four ordinary measurement outcomes.
Probability equality does not bind the source to the independently fixed H/T
matrix; a general source-preservation theorem is not claimed.

Run `python3 scripts/test_lean_exact.py` after building the kernel. The same
native comparison runs in CI, alongside both compiled audits, the runtime
source policy and fresh Lean kernel replay. See the
[registry audit](registry-validation.json) for rebuilt theorem/source identities;
all external entries remain disabled.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The proof extension is rechecked separately in
[bugfix native validation](bugfix-native-validation.json) and
[rebuilt registry validation](bugfix-registry-validation.json). Earlier reports
remain intact. Neither proof extension enables external schemas or transfers
production authority.

[Combined bugfix validation](bugfix-validation.json) records the compatible
sized-frontend repairs (#92/#93/#95), primitive-omission calibration, small
native regressions and the exact-proof extension. It makes no release claim.

[Matrix continuation validation](matrix-validation.json) and the
[rebuilt matrix registry audit](matrix-registry-validation.json) record this
general proof extension separately. Earlier reports remain intact.
Their earlier completion flags record the superseded scope assessment;
[scope-review.json](scope-review.json) records the correction without rewriting results.
