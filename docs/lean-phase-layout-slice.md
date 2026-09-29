# Typed phase and layout composition: CD-3 continuation

Status: **implemented with actual-checker proofs**, 2026-09-29. This experimental
component joins sparse dyadic phases and typed shared layouts. Executed checks
are in the [release checkpoint](releases/v0.2.0.md#typed-phase-and-layout-checkpoint-2026-09-29).
Production Rust verification remains authoritative.

The earlier typed-call component preserves coordinates but cannot express a
phase. The one-bit phase component cannot bind a controlled phase to multiple
typed owners. Connect those obligations with a phase-sensitive, multi-axis
shared graph; do not add source syntax or enable QFT/QPE schema shortcuts.

## Meaning and evidence

The `typed-phase256-dag-v1` profile reuses whole-interface layout definitions,
explicit call input/output adapters and ordered binary composition. A leaf
adds diagonal phases **before** its layout permutation. Each phase term has
an ascending list of distinct input axes and a canonical tick in 0..255. It
adds that tick exactly when every listed bit is one; the empty condition is
an unconditional scalar phase. The intended angle is 2π times tick/256. This
retains global phase and includes π/8 and smaller dyadic angles. No X, H,
measurement, negative controls, allocation or scratch release is added here.

For an input assignment x, a summary is a layout L and a sparse phase function
P(x) = Σ t·∏ x[i] modulo 256. Its action sends x to x∘L.axes and adds P(x) to
the cyclic phase. Composition computes L1;L2 and P1(x)+P2(x∘L1.axes), retaining
every owner and exact type tree. Calls compose their input adapter, actual
callee and output adapter in that order. Adapters themselves have zero phase.

Normalize conditions by sorting their axes, merge equal conditions modulo 256,
drop zero coefficients, and order terms by their binary condition key. Never
merge conditions merely because their keys coincide: compare actual axis lists.
Canonical claims and the separately read request fix the complete layout and
phase expression. Neither claimed results nor an algorithm name defines a leaf's
meaning. Every computed node must match its claim before becoming a cached
premise. The request cannot discard an unconditional phase.

## Capacity and checking experiment

Reuse the existing 16-axis, 64-owner, 256-definition, depth-64 and strict
65,536-byte transport bounds. Each submitted or cached polynomial has at most
128 terms and each condition at most 16 axes. The aggregate work limit remains
2,000,000, including layout checks and a conservative charge
64·(1+incoming terms)² per phase node, doubled for a call's two adapters.
Additionally charge 8·(1+term count)² for each claimed and required polynomial,
before validating it. For calls the
incoming count is the callee's term count; composition sums both counts. A
claim may supply a count for preflight, but cached results are checked against
claims immediately, before a later consumer is evaluated. Reject rather than
expand a circuit or enumerate all assignments to meet a semantic request.

Prove sparse normalization, remapping and composition against direct cyclic
phase execution, then the actual graph checker against independent requested
semantics. Interpret reference coordinates unchanged. The complex embedding,
unitarity/norm theorems, native compilation and source translation remain
separate obligations; numerical complex tests cannot issue evidence.

The independent small-case oracle executes each literal phase and layout on
all basis assignments and arbitrary joint reference amplitudes, never reading
intermediate claims. Include altered global/conditional phase, wrong mapped
axis, wrong call order, stale dependency and equal-width wrong type, plus
malformed and over-budget inputs. Check 16 axes and shared doubling without
dense matrices. Save the motivating source, initial rejected Lean command and
proof/test diagnostics before changing acceptance.

## Executable theorem boundary

The [sparse polynomial implementation](../lean-kernel/QleisliKernel/PhasePolynomial.lean)
proves insertion, zero-term removal, sorting, normalization, concatenation and
axis remapping preserve evaluation modulo 256. `single_axis` connects a one-axis
term to the original `PhaseWord.run` primitive. Conditions remain exact finite
bit conjunctions, with no floating arithmetic or basis-space enumeration.

The [combined checker](../lean-kernel/QleisliKernel/PhaseLayout.lean) proves:

| Declaration | Scope |
| --- | --- |
| `compose_sound` | Computed layout/polynomial composition equals ordered execution on all bit assignments and input cyclic phases. |
| `evalNode_sound`, `checkedNode_sound`, `evaluateFrom_sound` | Cached leaf/call/sequence evaluation agrees with the separate operational interpretation, which does not read proposed results. Each result is compared to its claim before insertion. |
| `checkMeanings_sound`, `check_sound` | Actual acceptance implies the independently requested bit/phase action and successful entry `Layout.check`, supplying the resource/permutation certificate. |
| `check_reference_value` (`check_reference` compatibility alias) | Equality of the cyclic basis action paired with an unchanged ordinary value. This product-value corollary does not establish a quantum tensor extension or preservation of entanglement. |

These are cyclic basis-action theorems. Complex linear extension, norm
preservation and arbitrary quantum instrument soundness are not proved here.
The subsequent [interference bridge](lean-interference-slice.md) interprets
this actual checker's accepted basis transitions over complex coefficients;
the complete matrix/instrument theorem remains a separate obligation.
Joint complex reference-amplitude tests are independent numerical regressions;
they are not a complex semantic bridge or proof of source/native adequacy.
Canonical syntax is a checked representation, not a proved complete decision
procedure for arbitrary operator equality. Unsupported non-diagonal gates,
general controlled/inverse/repeat nodes and encodings remain subsequent work.

## Transport, metrics and source experiment

The artifact header is `qleisli.phase-layout 1 typed-phase256-dag-v1`, followed by
`entry N` and `definitions N`. Each definition contains its existing
[layout DAG block](lean-layout-dag-slice.md#transport), then two phase blocks:

```text
source_phases N
term T K axis0 ... axisK-1
... N terms ...
claim_phases M
term T K axis0 ... axisK-1
... M terms ...
```

Only leaves may have source terms; every non-leaf must explicitly state
`source_phases 0`. Source terms may repeat a condition, have zero ticks or be
out of term-key order, but each condition is strictly ascending. Claims and
requests have nonzero coefficients and strictly increasing condition keys.
The checker validates axis bounds before computing keys.

The independent request header is
`qleisli.phase-layout-request 1 typed-phase256-dag-v1`, followed by the complete
uncertified layout body and one `expect_phases M` block. Both files retain the
strict ASCII, canonical decimal and LF envelope. The command is
`--phase-layout ARTIFACT REQUIREMENT`. Success has one JSON result with this
profile and failure returns no partial success. Errors distinguish syntax,
capacity, structural input, contract mismatch and I/O failure. The earlier
experimental commands and finite QIRF formats keep their meanings.

Metrics separate stored nodes/references/depth, total and phase work, cached
term count, expanded layout applications and expanded literal phase-term
applications. The latter includes zero-tick terms and repeated invocations even
when normalization cancels the final polynomial. These counts do not execute
the expanded graph. Dense dimension is always zero. Charges are a conservative
accounting model, not a wall-clock or allocator theorem.

The [first source](../tests/fixtures/lean_phase_layout/first_source/main.qli) uses
two calls of the same phase-and-swap definition plus a controlled T, preserving
a quantum Unit owner. A separate [interference client](../tests/fixtures/lean_phase_layout/interference_client/main.qli)
prepares and measures two qubits; all four probabilities are compared to the
independent Fourier sum for phase π/4·(x0+x1+x0x1). The finite Rust source uses
supported T gates; π/8 and smaller phases are exercised by the experimental
Lean profile. No `.qli` producer for this new IR is implemented or claimed.
The [development record](../tests/fixtures/lean_phase_layout/README.md) retains
source hashes, real diagnostics and separate after-state observations.
