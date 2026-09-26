<a id="a3l3-有限算術と位数推定"></a>

# A3/L3: Finite arithmetic and order finding

Status: **Finite subset implemented and checked on finite examples** (2026-09-26).
The initial A3/L3 scope consists of fixed-width reversible arithmetic,
order finding for N=15, and classical factor-candidate checking. General-size
Shor, sized integer types, and VQE/QAOA remain separate work. This English edition
is the authoritative contract and reference for this document, replacing its
earlier Japanese edition without changing the implemented APIs. The public
arithmetic definitions remain experimental; the [ledger](stdlib-contracts.md)
records their contracts and adoption status.

<a id="通常定義の算術契約"></a>

## Arithmetic contracts for ordinary definitions

Use the document-only abbreviations `B2=(Bit,Bit)` and `B4=(B2,B2)`. Bits have
weights 1, 2, 4, and 8 from left to right. All three APIs below are ordinary
`.qli` definitions with effect `Unitary` and one quantum parameter. They consume
input ownership and return every input wire with the same type. They introduce
no auxiliary resources or measurement, impose no state or separability promise,
and extend by identity to unmentioned references. Each stated basis mapping has
amplitude **+1**, not an unspecified global or input-dependent phase.

| API | Type and meaning on every basis input | Logical IR and cost | Acceptance / rejection |
| --- | --- | --- | --- |
| `std::arithmetic::increment2` | `Q<B2> -> Q<B2>`; `\|y⟩ ↦ \|(y+1) mod 4⟩` for `0≤y<4`. Overflow wraps. | One `Split`, one `Cnot`, one `Gate(X)`, one `Join`; two data wires. | Accept the two-bit product, including 3→0. Reject wrong widths/type trees and ownership reuse. |
| `std::arithmetic::add2` | `Q<(B2,B2)> -> Q<(B2,B2)>`; `\|x,y⟩ ↦ \|x,(y+x) mod 4⟩` for `0≤x,y<4`. The first pair is `x`, which is retained; the second is `y`. | One `Toffoli`, two `Cnot`, three `Split`, three `Join`; four data wires. | Accept all 16 basis inputs and arbitrary correlated inputs. Reject wrong types, duplication, and implicit discard. |
| `std::arithmetic::mul2_mod15` | `Q<B4> -> Q<B4>`; `\|y⟩ ↦ \|2y mod 15⟩` for `0≤y<15`, and `\|15⟩ ↦ \|15⟩`. | Three `Split` and three `Join` encode a cyclic four-axis permutation. Static transformations materialize a zero-phase, 16-entry permutation in `ApplyUnitary`. | Accept 15 as a defined input as well as every residue. Reject wrong types/resource misuse. There is no parameter for another modulus or multiplier. |

In `add2`, XOR the carry into the high bit **before** updating the low bit.
In `mul2_mod15`, input wires `(a,b,c,d)` become `(d,a,b,c)` in the output
interface. This permutation fixes both 0 and 15; mapping 15 to 0 instead would
be noninjective. The existing `adjoint` and `repeat_static` forms express inverse
and powers through the same checked static-transformation path.

These exact phase contracts follow from the sealed X/CNOT/Toffoli matrices
and the ordered wire interface. Numerical basis-output tests and inverse
round trips alone do not establish an arbitrary compiler's phase correctness.
No proof of general source-to-IR preservation is claimed here.

<a id="n15の量子部分"></a>

## Quantum computation for N=15

[`examples/order_finding`](../examples/order_finding/main.qli) statically defines
`evolution::evolve` as `mul2_mod15`. It applies the existing QPE structure to a
four-bit target; it introduces neither a first-class operation parameter nor a
generalized standard-library QPE API.

- `evolve`, `identity`, `square`, and `fourth` are ordinary `Unitary` definitions
  of type `Q<B4> -> Q<B4>`; the latter two implement `U²` and `U⁴`.
- `estimation::phase3` is an ordinary `Observe` definition of type
  `Q<B4> -> (((CBit,CBit),CBit),Q<B4>)`. It returns the target and measures/
  consumes only the three newly prepared phase bits. An eigenstate promise is
  unnecessary for acceptance. Calls in a `unitary` body and implicit discard
  of the returned target are rejected.
- `main` prepares target `|1⟩`, calls `phase3`, explicitly discards the returned
  target, and returns only the phase result.

Lowering expands preparation, controlled `U`/`U²`/`U⁴` via `qif`,
`adjoint(qft3,...)`, measurement, and discard, then passes the result through
independent `verify`. For general inputs, the mathematical instrument is
described by the [QPE Kraus operators](stdlib-roadmap.md#42-phase_estimate-位相に関するインストルメント);
that future-plan notation is not a current source API.

The orbit of `|1⟩` under U is `1→2→4→8→1`. With `M=8`, the phases are exactly
representable, giving integer results `y=0,2,4,6` with probability `1/4` each.
Output is displayed from the least significant bit, as `000,010,001,011`.
Three phase bits are not claimed to recover the order for arbitrary N.

<a id="古典ホストとの境界"></a>

## Boundary with the classical host

The Rust API [`factor_from_phase`](../src/host.rs), in module `host`, performs
classical postprocessing rather than a quantum operation:

```rust
pub fn factor_from_phase(
    n: u32,
    a: u32,
    phase_bits: u8,
    outcome: u32,
) -> Result<Option<Factors>, PhaseInputError>
```

It requires odd `n≥3`, `1<a<n`, `gcd(a,n)=1`, between 1 and 32 phase bits, and
`0≤outcome<2^phase_bits`. Violations produce respectively `Modulus`, `Base`,
`Precision`, or `Outcome` errors.

Using integer arithmetic, it traverses continued-fraction convergents of
`outcome/2^phase_bits`. For a nonzero numerator and denominator `r<n`, it checks
that `r` is even and `a^r mod n=1`. Only when `gcd(a^(r/2)-1,n)` is a nontrivial
factor does it return `Some(Factors)`, with `period_candidate=r` and the factor
pair ordered increasingly. It does not claim minimality of `r` or primality
of either factor. A denominator alone is insufficient evidence of a period.
The implementation does not search candidate multiples or combine samples
using least common multiples.

No usable candidate, odd candidate periods, or trivial gcd results yield
`None`. Retry using a newly prepared state, changing the base when its choice
causes failure. Automatic retries, random base selection, and device sampling
are unimplemented. Preserve the full success/retry distribution instead of
renormalizing success branches.

For `N=15` and `a=2`, results `y=2,6` supply `r=4` and factors 3 and 5.
Result `y=0` is uninformative, while `y=4` supplies denominator 2, which fails
`2² mod 15=1` and therefore requires a retry. This single-sample policy succeeds
with probability `1/2`.

The host example `cargo run --example shor15` aggregates the reference
simulator's entire distribution and displays each outcome's factor/retry
probability. It enumerates a finite ideal distribution; it does not draw
physical-device samples or supply a statistical confidence interval.

<a id="費用と残件"></a>

## Cost and remaining work

The quantum example uses four target and three phase wires, seven in total,
three phase measurements, and a final target discard. Naive expansion of powers
uses `1+2+4=7` applications of U. The inverse QFT3 uses three H and five
controlled T gates, and phase preparation uses three more H gates. An ownership
permutation does not imply free physical SWAPs. Controlled permutations require
backend synthesis; compilation cost of finite tables is distinct from physical
gate count.

This cyclic permutation specialized to one modulus and multiplier is not
evidence of general efficient modular multiplication. General-size arithmetic,
precision selection, static operation parameters, a standard QPE skeleton, and
host iteration remain design work. The fixed-width APIs remain experimental
under the [adoption criteria](stdlib-roadmap.md).

Background: [Shor's factoring algorithm](https://arxiv.org/abs/quant-ph/9508027)
and [Cleve et al., order finding in section 6](https://arxiv.org/html/quant-ph/9708016#S6).
The fixed-width APIs, full-space extension, and retry policy above are Qleisli
design decisions.

<a id="検証結果"></a>

## Verification record

```sh
cargo run --bin qleisli -- run examples/order_finding
cargo run --example shor15
cargo test --test order_finding
```

The host example displays retry for `y=0,4` and factors 3 and 5 for `y=2,6`,
each outcome with probability `1/4`. Success and retry each total 0.5.

The [ten order-finding tests](../tests/order_finding.rs) cover all four increment
inputs, all 16 addition inputs, all 16 multiplication inputs with powers 0–4 and
inverse, and round trips with four Bell references. They also cover phase
distributions for all 16 starting values, coherence with a reference in the
degenerate fixed subspace spanned by 0 and 15, and type/effect/ownership rejection.

The classical checks cover total success/retry probability, factor recovery for
N=21 from non-dyadic phase estimate `43/256`, odd periods, trivial gcd, invalid
inputs, the 32-bit boundary, and reconstruction of small usable orders found
independently by exhaustive search. Numerical distribution tolerance is `1e-12`;
continued fractions and modular arithmetic use no floating-point computation.

These finite checks do not replace a general compiler meaning-preservation
proof, establish efficiency at arbitrary sizes, or guarantee physical-device
behavior.
