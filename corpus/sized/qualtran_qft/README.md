# Shared QFT and inverse source

[Fourier](fourier.qli) is one ordinary definition for widths 1/2/3/4/8.
[Its inverse client](inverse.qli) imports that exact definition and calls
`adjoint(fourier[n], q)`. Both execute through the
[development source path](../../../docs/sized-corpus-source.md), not yet the
production CLI. The imported forward body is shared in the emitted hierarchy.

The positive Fourier contract is

```text
F_n[y,x] = exp(2*pi*i*x*y/2^n) / sqrt(2^n),   0 <= x,y < 2^n.
```

The low axis carries weight one. A Hadamard creates two coherent alternatives
for the current high bit; controlled phases encode its relation to lower bits.
The nested fold repeats this structure down the register. The final fold swaps
opposite bit positions exactly once. This reversal is an explicit operation,
not size equality or canonical reshape. Omitting it computes a different
unitary. The inverse conjugates the phase and reverses composition, so the
same source suffices without writing a second gate body.

The source uses affine static comparisons to express its domain and guarded
swaps, and normalized dyadic phases through denominator 256. Neither division
nor variable products enter size expressions. The development compiler checks
moves in both branches and resolves names in unselected/empty paths. General
symbolic type/size obligations and source preservation remain open.

```sh
python3 scripts/compile_sized_corpus.py corpus/sized/qualtran_qft/fourier.qli \
  --entry fourier --size n=8 --output /tmp/qft8.json
python3 scripts/compile_sized_corpus.py corpus/sized/qualtran_qft/inverse.qli \
  --entry inverse_fourier --size n=8 --output /tmp/iqft8.json
python3 scripts/test_sized_qft.py
```

The compile commands emit untrusted proposals. The test freshly reconstructs
actual finite leaves and checks every forward Fourier artifact against an
independently supplied named Fourier request. The inverse uses existing checked
inverse/composition rules; an independently named inverse request is not yet
connected. The [validation record](../qft-validation.json) contains:

* 572 complete forward/inverse basis columns and 20 coherent reference columns,
  plus both composition orders. Maximum formula error is below 1.72e-14.
* Five valid-but-wrong circuits, including a changed imported forward body,
  detected by independent phase-sensitive formulas. Four forward mutations
  also reject the independent named Fourier request after passing inspection.
* Fourteen source rejection cases for size, angle, ownership, missing names,
  calls, cycles and aggregate work; function renaming cannot select an algorithm.
* Two width-eight calls sharing eight finite leaves and the complete forward
  body, with all 256 inputs satisfying `F_n^2|x> = |-x mod 2^n>`.
* A call beside an untouched quantum register, checked on all 16 basis inputs
  and an entangled complex vector. Local callee names do not alias that frame.
  The 8+8-wire frame also passes generation and inspection; exhaustive numerical
  simulation of that 16-wire case is not claimed.

The source compiler factors only the complete elaborated Fourier gate trace,
including every axis, exact phase and explicit output reversal, into the
existing shared-gradient construction. A changed source body is never replaced
with a known-correct QFT merely because of its name. Actual generated IR still
passes all independent checks. This untrusted optimization has regression
coverage; it is not a general source-preservation proof.

After the QPE-driven recursive typed-reversal optimization, the previously
tested width-eight forward named check costs 1,649,990 structural and 944 exact
units; inverse source costs 1,531,028 structural and 536 exact units. Two shared
forward calls cost 1,597,653 and 536 respectively. The 8+8-wire frame costs
1,761,048 structural units. These component results do not establish full QPE
capacity. Remaining maximum-size checks are deferred by user decision. No work ceiling
or checker rule changed. **Storage/checking sharing is not execution savings:**
the source has eight H and 28 controlled phases; the current repeated-gradient
IR executes 255 H/phase applications, and two calls execute 510. SWAP routing
is represented explicitly but is not counted as H/phase applications. Reducing
that execution cost while preserving independently checked meaning is open.

These are Apache-2.0 translations of the already retained Qualtran
`QFTTextBook`, commit `8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3`,
[original source](../../upstream/qualtran/qualtran__bloqs__qft__qft_text_book.py).
Retain Google attribution and the [license](../../upstream/qualtran/LICENSE).
The existing [finite translation](../../qualtran/qft2/README.md) stays a regression.
No upstream material was downloaded. [First sources and real diagnostics](../../../tests/fixtures/authoring_sessions/sized-qft-v021/session.json)
remain recorded. QPE/CBits, other planned components and production integration
still prevent completion of the full v0.2.1 corpus goal.
