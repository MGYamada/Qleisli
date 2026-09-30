# QFT circuit-to-Fourier proof packet

Status: **symbolic compiler, circuit matcher and Fourier coefficient/reference
theorems implemented**, 2026-09-29. This works toward the
already selected `qft-dyadic8/1` schema; it does not enable that registry entry
before its complete theorem and binding tests pass.

The [existing desired sized source](../tests/fixtures/authoring_sessions/shared-qpe-v020/attempt-01/estimation.qli)
and [finite executable baseline](../tests/fixtures/lean_qft/first_source/main.qli)
motivate this packet. Keep the existing positive QFT convention and final bit
reversal. A round-trip test alone cannot prove the phase or Fourier meaning.

## Selected checking argument

Compile the literal H/controlled-phase stages to a symbolic path expression.
Input variables are numbered 0..m-1. Each H allocates a fresh *classical basis
index variable* for its path outcome; this is not quantum-owner allocation or
copying. Add a phase term of 128 ticks times the old and new bits. Diagonal
gates add their literal terms after mapping axes through the current variable
assignment. Keep the total H count, output-variable map and sparse phase
polynomial. Prove that evaluating this expression on every input and fixed
path reproduces direct gate-by-gate bit/phase execution. No path enumeration
occurs in compilation or verification.

For QFT, each axis receives H once in descending order. After final reversal,
the output variables are m..2m-1 in ascending order and H count is m. The phase
polynomial must equal

```text
sum_(k+l<m) 2^(8-m+k+l) x[k] y[l] modulo 256.
```

Prove that polynomial is `2^(8-m)·value(x)·value(y)` modulo 256, with little-endian
values, and that there is exactly one path per output. With the separately
proved complex model this gives the positive Fourier matrix coefficient
`(1/sqrt(2))^m exp(2πi value(x)value(y)/2^m)`. Bind the executable schema matcher
to actual gate order, axes, angle, final layout, width, and theorem identity.
It may visit the O(m²) gate template, never a 2^m by 2^m matrix. General call,
ownership and encoding integration remain distinct required premises.

## Independent experiment and counterexamples

At widths 1..3 compare complex circuit action with the independent Fourier
formula, including all columns and arbitrary joint-reference amplitudes.
At all widths 1..8 check symbolic dimensions and representative exact modular
phase values without allocating a dense matrix. Reject altered sign, dropped
or swapped stages, changed phase denominators, missing final reversal and
invalid axes. Preserve first implementation/proof attempts and real diagnostics.
The earlier phase/layout and interference regression suites remain required.

## Actual definitions and completed proof boundary

[PathSum.lean](../lean-kernel/QleisliKernel/PathSum.lean) proves
`compileStep_sound`, `compileFrom_sound` and `compile_sound` against direct
literal-gate execution for every fixed sequence of H outcomes. The symbolic
compiler never enumerates paths. Its inputs are internal gate data, not a new
independently accepted IR format. Original axis/phase validity is checked by
compilation; a general aggregate input budget and typed ownership integration
are obligations of the later external boundary.

[Qft.lean](../lean-kernel/QleisliKernel/Qft.lean) contains the actual internal
`matchCircuit`: widths 1..8, at most 36 gates, the exact literal template and
the separately supplied final reversal. `compile_template` proves the symbolic
result for all eight widths by kernel-checked computation on the gate/phase
structures, not by matrix or basis enumeration. `matched_paths` and
`matched_output` establish the path meaning and the one-to-one output choice.
`cbv` produces ordinary checked proofs; no native proof evaluation or project
axiom was used. Its elaboration budget does not change runtime input capacities.

**Compatible review extension, 2026-09-30:** `matchCompiledCircuit` compares
`PathSum.compile width gates` to `some (expected width)`, with the same width,
gate and reversal limits. `compiled_matched_paths` follows directly from the
actual `compile_sound` theorem for the candidate. Phase-term splitting and
commuting diagonal-gate reorderings can now match without literal-template
identity. The new `compiled_matched_phase/weight/coefficient/fourier/reference`
complex theorems establish the corresponding Fourier and joint-reference
meaning. The original matcher and theorem types remain available; the existing
typed graph/schema path continues to use them for PATCH compatibility.

This is equality of normalized symbolic paths, not complete unitary equivalence.
For example, inserting two H gates introduces extra path choices even though
H squared is identity. Widths remain 1–8 because the component phase model is
modulo 256. The original bounded QFT/Fourier theorems are real conditional
coefficient theorems, beyond just the `cbv` reductions, but neither they nor this
extension establish general-width QFT. That needs the
[size-dependent domain work](coefficient-domains.md#review-inventory-and-v03-decision).
The new native regressions generate only widths 1–4 and reject phase, reversal,
invalid-axis and capacity faults; external schemas remain disabled.

The separate [complex proof](../lean/Qleisli/Qft.lean) establishes:

| Theorem | Scope |
| --- | --- |
| `fourier_phase` | The actual bilinear polynomial equals 2^(8-m)·value(x)·value(y) modulo 256, for arbitrary bit assignments and m≤8. ZMod is used only for exponent arithmetic in the proof package. |
| `hadamard_path_weight`, `diagonal_path_weight`, `pathProduct_weight` | Actual direct path execution multiplies the standard H and literal phase matrix entries. |
| `matched_weight`, `matched_coefficient`, `matched_fourier` | Acceptance by the actual matcher gives each positive normalized Fourier coefficient in little-endian coordinates, including the required reversal. |
| `matched_reference` | The coefficient equation extends to every joint input/reference amplitude, with no separability or eigenstate premise. |

`coefficient` is a proof-only sum of primitive-entry products over m H outcomes;
the matched circuit has exactly that number. It is not a general-circuit
denotation for words with other H counts. The matcher/compiler never evaluates
this mathematical sum. This proves the QFT circuit/template component, not a
complete QFT registry importer, a general non-diagonal graph checker, a QPE
instrument, source translation or native compilation. Type trees, ports,
encodings, graph dependencies, theorem identity and shipped manifest binding
must still be connected before enabling `qft-dyadic8/1` externally.

The subsequent [typed shared graph packet](lean-qft-graph-packet.md) now proves
that binding for an internal canonical-register projection and transfers the
Fourier theorem to its literal graph coefficients. Complete external IR and
registry binding remain separate obligations.

The [native oracle](../scripts/test_lean_qft.py) tests 109 cases, including
wrong phase/stage/order/reversal and invalid inputs; it compares 3,180 direct
paths and 1,600 independent modular Fourier values. At widths 1..3, all 84
matrix entries and nine arbitrary joint-reference cases agree with the separate
complex Fourier formula. Verification/compilation dense dimension is zero;
the independent numerical oracle's maximum dimension is eight. The retained
[wrong-reversal source](../tests/fixtures/lean_qft/wrong_reversal/main.qli) is
accepted by finite typing but fails the intended round trip exactly as the
independent F† R F formula predicts. See the
[development record](../tests/fixtures/lean_qft/README.md) for actual commands,
first attempts and diagnostic repairs.
