<a id="構造化アルゴリズムの有限部品"></a>

# Finite building blocks for structured algorithms

Status: **Implemented as ordinary `.qli` definitions and checked on finite
examples** (2026-09-26), corresponding to A1 of the
[second development goal](algorithm-structure-goal.md). The bundled
[`routines.qli`](../stdlib/src/routines.qli) defines five fixed-width public
functions in `std::routines`. They receive the same type, effect, ownership,
body-expansion, and independent IR checks as user source. They add no primitive
operations, surface syntax, or first-class combinators. Generalized names and
widths remain future design work. This English edition is the authoritative
contract and reference for this document, replacing its earlier Japanese edition
without changing the APIs or their evidence status.

<a id="公開apiの契約"></a>

## Public API contracts

Consume all quantum arguments; only ownership returned in the result may be
used subsequently. Distinct ownership does not imply a product state. Interpret
each operation with the identity on unmentioned reference systems. The basis
pair `(a,b)` has IR integer label `a+2b`; measurement output is displayed as
`ab` from left to right. Product-domain notation does not change source arity:
`parity_zz` takes two quantum arguments, while the other four functions take one.

| Name and classification | Input/output type, effect, and meaning | Acceptance / rejection | IR lowering |
| --- | --- | --- | --- |
| `hadamard2`; ordinary `.qli` definition | `Q<(Bit,Bit)> -> Q<(Bit,Bit)>`, `Unitary`; `H⊗H`, returning all ownership. | Accept a two-bit product register. Reject `Q<Bit>` and consumed inputs. | `Split; Gate(H); Gate(H); Join`. |
| `reflect_uniform2`; ordinary definition | Same type, `Unitary`; `D=2\|s⟩⟨s\|-I` with `\|s⟩=(H⊗H)\|00⟩`. | Accept the reflection in a Grover step. Reject a single bit and reused ownership. | Expand `hadamard2`, `ComputeUseUncompute`, `hadamard2`. The equation below fixes the phase. |
| `measure_x`; ordinary definition | `Q<Bit> -> CBit`, `Observe`; measure X eigenvalue `(-1)^b` and consume the input ownership. | `measure_x(h(init0()))` returns 0. Reject a call in a `unitary` body or subsequent use of its old input. | `Gate(H); MeasureZ`. |
| `measure_z2`; ordinary definition | `Q<(Bit,Bit)> -> (CBit,CBit)`, `Observe`; consume both inputs. | A Bell pair gives 00/11. Reject a single bit and use of the old measured register. | `Split; MeasureZ; MeasureZ`; return the left result first. |
| `parity_zz`; ordinary definition | Arguments `Q<Bit>,Q<Bit>` → `((Q<Bit>,Q<Bit>),CBit)`, `Observe`; return both separately owned data wires and consume the internal meter. | Accept ZZ-parity measurement on correlated data. Reject `parity_zz(q,q)`, implicit discard of returned data, and use in a `unitary` body. | `Init0; Cnot(a,m); Cnot(b,m); MeasureZ(m)`. |

The private `nonzero2(a: Bit,b: Bit) -> Bit` is also an ordinary basis function.
It is total, returning 0 on 00 and 1 otherwise; finite enumeration checks
totality. Its table may be noninjective because `with_computed` uses it for
reversible XOR computation into an auxiliary. This is not a direct-lift
contract from `Q<(Bit,Bit)>` to `Q<Bit>`.

<a id="反射の位相"></a>

### Reflection phase

`with_computed(q,nonzero2) { |a| z(a) }` multiplies basis state `|ab⟩` by
`(-1)^nonzero2(a,b)`, hence

```text
R0 = diag(1, -1, -1, -1) = 2|00⟩⟨00| - I
D  = (H⊗H) R0 (H⊗H) = 2|s⟩⟨s| - I
```

An oracle that negated only 00 would instead produce `-D`. The operator's sign
is fixed by this definition and the source construction. Global phase is
unobservable in the closed measurement example alone. The subsequent A2
[controlled-sign tests](static-operations.md#確認した結果) distinguish `D` from `-D`.

<a id="パリティ測定の全体系での意味"></a>

### Whole-system meaning of parity measurement

For result `s` of `parity_zz`, the unnormalized remaining system is

```text
P_s = (I + (-1)^s Z_a Z_b) / 2
E_s(ρ) = (P_s ⊗ I_R) ρ (P_s ⊗ I_R),  s ∈ {0,1}.
```

The orthogonal projectors sum to identity, so the sum of branches preserves
trace. Coherence within each parity subspace is retained. Measuring each data
wire in Z and then XORing the results would produce a different remaining state.
For input `|++⟩`, results 0 and 1 have probability `1/2` each and leave,
respectively, `(|00⟩+|11⟩)/√2` and `(|01⟩+|10⟩)/√2`. Tests check the X
correlations that would be lost by replacing the operation with data measurements.

<a id="組み立てたアルゴリズム"></a>

## Composed algorithm examples

<a id="grover-オラクル反射有限反復"></a>

### Grover: oracle, reflection, and finite repetition

[`examples/grover`](../examples/grover/main.qli) separates preparation,
`oracle::mark`, `search::step`, and measurement into modules. Predicate
`marked(a,b)=a and b` gives `O=I-2|11⟩⟨11|`. The step is `G=D O`, and
`search_one` applies it once to `|s⟩`.

- `oracle::mark` and `search::step` are ordinary definitions of type
  `Q<(Bit,Bit)> -> Q<(Bit,Bit)>` and effect `Unitary`.
- `search::search_one` is an ordinary `Iso` definition with no arguments and
  result `Q<(Bit,Bit)>`, returning two fresh data wires.
- `marked(a: Bit,b: Bit) -> Bit` is an ordinary total basis function. Having
  exactly one marked value is an algorithm-specific assumption.
- Ordinary calls expand into existing preparation, gate, and auxiliary IR.
  The example `main` is accepted. Reusing resources or supplying measured
  ownership to a step is rejected.

For one marked value among four candidates, `θ=arcsin(1/2)=π/6` and the success
probability after `k` iterations is `sin²((2k+1)θ)`. Tests cover every marked
value and `k=0..4`; repetition does not monotonically increase success.
These finite Grover repetition tests use explicit call sequences. A2 separately
implemented the `repeat_static` language form.

<a id="bernsteinvazirani-同じ準備と異なる干渉の組み立て"></a>

### Bernstein–Vazirani: shared preparation, different interference

[`examples/bernstein_vazirani`](../examples/bernstein_vazirani/main.qli) shares
`hadamard2` and `measure_z2` with Grover. For
`O_s|x⟩=(-1)^(s·x)|x⟩`, it uses `(H⊗H)O_s(H⊗H)|00⟩=|s⟩`.

- `oracle::mark` is an ordinary `Unitary` on a two-bit register. Its ordinary
  total basis function `linear(a,b)=a` represents the displayed secret 10.
- `interference::recover_secret` is an ordinary `Iso` with no arguments and
  result `Q<(Bit,Bit)>`. It expands fresh preparation, the oracle, and Hadamards,
  returning the resulting ownership.
- The example `main` is accepted; incorrect types and ownership reuse are
  rejected. Linearity of the oracle's Boolean function is an algorithm promise,
  not a consequence of type acceptance.

Tests cover all four secrets. This is a finite example assuming access to a
phase oracle, not a measurement of large-oracle synthesis cost.

<a id="ビット反転訂正-シンドローム古典フィードバック"></a>

### Bit-flip correction: syndrome and classical feedback

[`examples/bit_flip_code`](../examples/bit_flip_code/main.qli) is restricted to
a **three-qubit repetition code, ideal operations, and at most one X error**.
Its code space is `α|000⟩+β|111⟩`. It does not claim general error correction
or fault tolerance.

| Ordinary definition | Type, ownership, and effect | Meaning and IR |
| --- | --- | --- |
| `code::encode` | `Q<Bit> -> Q<((Bit,Bit),Bit)>`, `Iso`. Consume the input and return a register with two additional wires. | `LiftBasis` for injective `b -> ((b,b),b)`; encoding `V`, not cloning an unknown state. |
| `code::recover` | `Q<((Bit,Bit),Bit)> -> (Q<((Bit,Bit),Bit)>,(CBit,CBit))`, `Observe`. Return the data and measure/consume internal meters. | Expand `parity_zz(a,b)`, `parity_zz(b,c)`, and syndrome-dependent X using `ClassicalBranch`. |
| `code::decode` | `Q<((Bit,Bit),Bit)> -> (Q<Bit>,(Q<Bit>,Q<Bit>))`, `Unitary`. Return ownership of all three wires. | `Cnot(a,b); Cnot(a,c)`. Even zero-valued auxiliary outputs are not implicitly released; the caller consumes them explicitly, for example by measurement. |

Syndromes `(s_ab,s_bc)` for no error, `X_a`, `X_b`, and `X_c` are
`00,10,11,01` respectively. For the corresponding correction `C_s` and decoder
`D_dec`, each `E∈{I,X_a,X_b,X_c}` satisfies

```text
D_dec C_s E V |ψ⟩ = |ψ⟩ ⊗ |00⟩.
```

The same linear equality extends by identity to any reference system. The
syndrome is independent of the logical value. This circuit equation is distinct
from a general soundness proof for the compiler.

Tests entangle the logical input with an external Bell reference and check
correlations, syndrome, and zero decoder auxiliaries after all four errors.
They also confirm residual logical errors for a Z error and for two X errors.
The current `Q<...>` types do not encode the code-space or error-model premises;
inputs outside those premises are not claimed to be rejected by typing.
Resource duplication, implicit discard of returned data, and observation inside
a `unitary` body are rejected.

<a id="実行と検証"></a>

## Execution and verification

```sh
cargo run --bin qleisli -- run examples/grover
cargo run --bin qleisli -- run examples/bernstein_vazirani
cargo run --bin qleisli -- run examples/bit_flip_code
cargo test --test algorithms --test project
```

The three example outputs are respectively `11`, `10`, and `11000` with
probability one. The last consists of syndrome 11, logical X measurement 0,
then Z measurements 00 of the decoder auxiliaries. The reference simulator
uses `f64` approximation with test tolerance `1e-12`. These finite checks do
not establish a general soundness theorem, physical correction capability, or
large-scale computational complexity.
