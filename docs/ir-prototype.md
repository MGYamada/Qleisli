# Rust finite IR verifier and reference execution

Status: **Stage 2 is partially implemented** (2026-09-26). This authoritative
English implementation profile replaces the previous Japanese edition. It
records the checks actually performed by `qleisli`, in relation to the
[finite-core formalization](formal-core.md). The [frontend](frontend-v0.md)
checks supported `.qli` and generates this IR. General correspondence between
the mathematical theorems and the Rust implementation remains unproved.

<a id="入力と信頼境界"></a>

## Inputs and trust boundary

`RawProgram` is public data that may be created by humans, AI, or a frontend.
Its annotations and effect declarations are untrusted. `verify(raw)` checks
ownership, constructors, finite tables, and effects, and returns a
`VerifiedProgram` with private fields only on success. The simulator accepts
that wrapper; future backends must maintain the same boundary. Rewriting raw
IR requires fresh verification before execution.

`BasisShape` records an ordered finite bit width. Width zero covers the erased
representation of Unit-only basis types; even a zero-wire register has a linear
ownership token. Source product-tree structure and names are not retained in
IR. Register wire order determines `split/join` and table indexing.

A `QuantumPhi` renames the selected input register's wire at position `i` to
its output wire at position `i`. It is an axis correspondence, not preparation,
cloning, measurement, or a product-state assertion. Every live branch output
must be covered once. Final register order is given by `quantum_outputs`;
executors and future backends must preserve the same axis interpretation.

`Effect` uses the order `Unitary <= Iso <= Observe`, matching the current source
effect order. Pure means either of the first two. IR effects describe expanded
operations; they do not replace the source check of a callee's declared effect.
Classical phi inputs are all validated before outputs are introduced, so a phi
cannot read another output of the same merge.

<a id="実装済みの検査"></a>

## Implemented checks

| Subject | Validation |
| --- | --- |
| Resources | Unique input/generated wires, single consumption of SSA tokens, distinct operation inputs, all live tokens returned, and no reuse after measurement. |
| Pure operations | Sealed H/X/Z/T/CNOT/Toffoli, ordered split/join, and total injective `LiftBasis` tables. Growth is `Iso`; only equal dimensions may claim `Unitary`. |
| Finite unitary sequences | Independently check `ApplyUnitary` Hadamards, phase-labelled permutations, and basis controls. Reject invalid/duplicate axes, controls overlapping targets, partial/noninjective tables, and out-of-range phases. See the [static contract](static-operations.md). |
| Coherent branches | Raw `QuantumIf` requires distinct control/target wires and sealed unitary arms. Keep scalar phases; do not measure the control. |
| Observations | `MeasureZ` consumes ownership and produces a classical bit; `Reset` uses fresh logical wires; `Discard` explicitly ends ownership. Reject these in `Unitary`/`Iso` programs. |
| Classical branches | Require a visible classical guard, check arms separately from the same context, and merge all live resources with fresh phis. Reject resource leaks and hidden effects. |
| Auxiliaries | No standalone `Release0`. `ComputeUseUncompute` checks a total table, structurally fixes computation and its inverse, and restricts protected use to phases and controlled target gates preserving source/auxiliary basis labels. |
| Semantic auxiliary contracts | `CertifiedCompute` checks the actual retained joint circuit W against the explicit logical circuit u using exact `W E_f=E_f u`. Reserve one fresh auxiliary wire; consume/reissue the source token, including width zero. The finite capacity and soundness premises are specified in [SC](semantic-contracts-v0.1.md). |
| Function meaning contracts | `CircuitAction::Contract` carries immutable independently checked evidence, ordered local axes, and an adjoint flag. Validate target width, axis uniqueness, and disjoint controls at every attachment. [Function evidence](function-contracts-v0.1.md) retains both raw functions and source/dependency identity through static transformations. |

Protected raw IR can describe work-register uses beyond the source v0
`with_computed` form. This is not a general source borrowing implementation.
The two-argument source form permits only an expanded auxiliary identity or Z/T chain and
masks all outer quantum captures. See [the source boundary](language-spec.md#9-限定された補助計算).

The three-argument extension instead creates an isolated owned data/auxiliary
body. Raw verification independently validates both flat circuits and the
whole encoded-subspace equation, including zero rows outside the output code.
The reference simulator executes the retained physical W between computation
and uncomputation before eliminating the proved-zero auxiliary. Numerical
smallness never authorizes release. The evidence API in `contract`
has immutable checked results and typed encodings. In-process function evidence
is retained and shared across calls and static transformations; serialized
proof artifacts remain outside the initial profile.

The function circuit extractor independently validates both raw functions and
compares exact ordered operators. Execution uses its checked physical lowering;
a private clean region may already have been replaced by its certified logical
action. The raw body remains in the evidence object. Checking cost, proof depth,
and transitive execution expansion have explicit bounds in the function profile.

The verifier accepts neither arbitrary matrices nor textual claims of being
proved. Sealed matrix/observation meanings and correctness of the Rust checker
remain in the trust boundary. The wrapper restricts construction through safe
Rust APIs; it is not a guarantee against arbitrary external `unsafe` code.

Table-related registers and auxiliary widths are each at most 12 bits, with
at most 64 nested classical branches, counting each branch before entering
its arms, including empty arms. The [0.1.6 correction](releases/v0.1.6.md)
repairs erroneous acceptance of a 65th branch with empty arms; it does not
change the published limit. These are capacity limits of this
prototype, not mathematical finite-type restrictions. The verifier places no
global cap on live wires or instruction count. It indexes live wires for
logarithmic duplicate checks. Freshness history and classical scopes are shared
across branch checks rather than copied wholesale. Copying live branch contexts
and checking phis costs work proportional to those contexts and interfaces.
Execution therefore needs its own limits.

<a id="参照実行系の範囲"></a>

Classical literals and Boolean source operators lower directly to
`ClassicalConst`, `ClassicalNot`, `ClassicalAnd`, and `ClassicalXor`. The verifier
requires visible operand SSA IDs and globally fresh outputs. These instructions
preserve all quantum ownership and have derived effect `Unitary`; any effects
of evaluating source operands remain in the preceding IR.

## Reference execution

Legacy raw `QuantumIf` arms use a private adapter from `UnitaryStep` to the
existing `CircuitStep` executor. Both arms retain their original precharged
step cost, outer control polarity, axis order and scalar phase on `Unit`.
Primitive monomial gates and scalar phases execute in place. The public raw
variants and their independent verifier/extractor remain available; current
source `qif` already lowers to `ApplyUnitary`. See the [IR reduction inventory](interoperability-roadmap.md#ir-reduction-and-the-trusted-boundary)
for compatibility debt and the future core migration.

The future **[desugaring layer](terminology.md#desugaring-layer)** instead
translates convenience forms into already specified core operations before
independent acceptance, preserving meaning and adding no primitive/checker rule.
Its output/evidence is untrusted. The runtime adapter above operates after
verification and does not implement that migration or remove legacy checks.

`sim::run_closed` runs only a `VerifiedProgram` with no classical or quantum
inputs and no quantum outputs. It returns a map from bits in `classical_outputs`
order to probabilities. The first local wire is table bit zero, and global axis
zero is the least significant state-vector index bit. Branch phis rename axes
by the position rule above.

Measurement, discard, and reset retain an ensemble of **unnormalized** pure
components. Histories with the same public result contribute probabilities,
not amplitudes. This retains the mixed state after discarding one Bell half.
Arithmetic uses approximate `f64`, not exact identities. For example, H, then
T eight times, then H and Z measurement ideally returns false with probability
one, but rounding can produce true with weight around `10^-32`. The simulator
does not remove all small positive weights by a fixed threshold; a tiny output
weight alone does not establish an ideal nonzero probability.

Before a `CertifiedCompute` auxiliary is projected away, the reference
simulator checks the probability weight on its one-valued rows relative to the
entire unnormalized component. A fraction above `1e-12`, or non-finite total
weight, reports `InconsistentVerifiedIr`. This is a numerical inconsistency
alarm after exact certification, never evidence authorizing pure release.
For this ratio alone, real and imaginary coordinates are divided by their
largest absolute value before squaring; this prevents tiny component weights
from hiding material relative leakage through underflow. The original
total-weight check still rejects non-finite values, including overflow from
finite amplitudes. An all-zero component has no numerical leakage.
Small numerical residuals are not renormalized, and no threshold removes small
positive measurement outcomes. Contract actions continue to execute their
checked extracted circuits, including proved cleanup substitutions; their
retained raw physical witnesses are separately exercised by differential tests.

Defaults are at most 16 quantum axes, 65,536 ensemble components, 1,048,576
complex amplitude cells in total, and 1,000,000 execution steps shared across
the whole run. `SimulationLimits::max_execution_steps` counts IR operation
visits plus flat/expanded circuit steps and legacy protected/unitary steps
over all ensemble components and selected classical branches. Contracted
calls charge their cached transitive cost before expanding; calls and branches
do not reset the budget. Exhaustion returns `SimulationError::ExecutionLimit`
without a partial result. This is not a floating-point-operation or wall-clock
bound. The implementation's absolute axis limit is
20; a caller may choose smaller limits. Capacity failure is diagnosed rather
than handled by silently truncating state or histories.

<a id="検証結果と未達成"></a>

## Evidence and open obligations

The [verifier tests](../tests/verify.rs) exercise accepted Bell/oracle/feedback
IR and reject duplicate or lost ownership, reuse after measurement, noninjective
lifts, effect violations, invalid auxiliary use, incomplete branch interfaces,
and references to outputs of the same classical merge. The
[simulator tests](../tests/sim.rs) check correlations, phase, partial disposal,
reset, mixed histories, and floating-point residuals against finite predictions.
Regression cases include 8,000 branches and 80,000 preparations, bounding the
observed cost of history and duplicate checks without proving complexity for
all programs. Parser tests check recursion, Boolean-chain AST depth and the
separate tuple arity/nesting limits.
Frontend, project, algorithm, and static-operation suites cover their own layers.
Current commands, totals, and historical milestones are recorded in the
[conformance record](specification-status.md); old compiler counts are not a
current coverage measure.

The source frontend compares exact product trees, then erases them to ordered
widths. Source static operations support the specified unary quantum interface.
General operation parameters, classical-port or heterogeneous static operations,
general source borrowing signatures, and open-program reference execution remain
outside the implementation. The simulator implements the factored effective
operator of `ComputeUseUncompute`; it does not independently execute and inspect
every auxiliary wire's zero return. The [conditional finite-IR paper argument](finite-core-proof.md)
is not machine verification of the Rust checker. Compiling a `.qli` program does
not establish a proved guarantee of physical hardware correctness.
