<a id="構造化アルゴリズムの有限部品"></a>

# Finite building blocks for structured algorithms

Five ordinary fixed-width APIs in [routines.qli](../stdlib/src/routines.qli); checked like user source. General widths/names remain future work.

<a id="公開apiの契約"></a>

## Public API contracts

All quantum arguments are consumed; reuse only returned ownership. Separate owners may be entangled; extend by identity on arbitrary references. Pair label a+2b is low-weight-first, displayed measurements ab follow tuple order. parity_zz takes two arguments; the other four take one. Private nonzero2 is total, not injective, and valid only inside reversible computed use.

| Name and classification | Input/output type, effect, and meaning | Acceptance / rejection | IR lowering |
| --- | --- | --- | --- |
| `hadamard2`; ordinary `.qli` definition | `Q<(Bit,Bit)> -> Q<(Bit,Bit)>`, `Unitary`; `H⊗H`, returning all ownership. | Accept a two-bit product register. Reject `Q<Bit>` and consumed inputs. | `Split; Gate(H); Gate(H); Join`. |
| `reflect_uniform2`; ordinary definition | Same type, `Unitary`; `D=2\|s⟩⟨s\|-I` with `\|s⟩=(H⊗H)\|00⟩`. | Accept the reflection in a Grover step. Reject a single bit and reused ownership. | Expand `hadamard2`, `ComputeUseUncompute`, `hadamard2`. The equation below fixes the phase. |
| `measure_x`; ordinary definition | `Q<Bit> -> CBit`, `Observe`; measure X eigenvalue `(-1)^b` and consume the input ownership. | `measure_x(h(init0()))` returns 0. Reject a call in a `unitary` body or subsequent use of its old input. | `Gate(H); MeasureZ`. |
| `measure_z2`; ordinary definition | `Q<(Bit,Bit)> -> (CBit,CBit)`, `Observe`; consume both inputs. | A Bell pair gives 00/11. Reject a single bit and use of the old measured register. | `Split; MeasureZ; MeasureZ`; return the left result first. |
| `parity_zz`; ordinary definition | Arguments `Q<Bit>,Q<Bit>` → `((Q<Bit>,Q<Bit>),CBit)`, `Observe`; return both separately owned data wires and consume the internal meter. | Accept ZZ-parity measurement on correlated data. Reject `parity_zz(q,q)`, implicit discard of returned data, and use in a `unitary` body. | `Init0; Cnot(a,m); Cnot(b,m); MeasureZ(m)`. |

<a id="反射の位相"></a>

### Reflection phase

Positive reflection signs are part of the controlled contract; marking zero instead yields -D. [Controlled-sign regressions](static-operations.md#確認した結果) distinguish them.

```text
R0 = diag(1, -1, -1, -1) = 2|00⟩⟨00| - I
D  = (H⊗H) R0 (H⊗H) = 2|s⟩⟨s| - I
```

<a id="パリティ測定の全体系での意味"></a>

### Whole-system meaning of parity measurement

Parity measurement preserves within-subspace coherence and arbitrary references. For |++>, each branch probability is 1/2 with Bell residual; individual Z measurements plus XOR are a different instrument.

```text
P_s = (I + (-1)^s Z_a Z_b) / 2
E_s(ρ) = (P_s ⊗ I_R) ρ (P_s ⊗ I_R),  s ∈ {0,1}.
```

<a id="組み立てたアルゴリズム"></a>

## Composed algorithm examples

Examples below compose current ordinary source; finite tests are separate from complete compiler/algorithm proofs.

<a id="grover-オラクル反射有限反復"></a>

### Grover: oracle, reflection, and finite repetition

Preparation Iso, oracle/step Unitary and measurement Observe. For one marked item of four, theta=pi/6 and success after k steps sin²((2k+1)theta). Test all targets and k=0..4; more repetitions can overshoot.

<a id="bernsteinvazirani-同じ準備と異なる干渉の組み立て"></a>

### Bernstein–Vazirani: shared preparation, different interference

For total linear f_s, (H tensor H) O_s (H tensor H)|00>=|s>. The linear promise is algorithm-specific, not typing evidence. Tests cover all four secrets with shared preparation/readout.

<a id="ビット反転訂正-シンドローム古典フィードバック"></a>

### Bit-flip correction: syndrome and classical feedback

Only ideal three-wire repetition code and at most one X error. Syndromes I/Xa/Xb/Xc are 00/10/11/01. Correct/decode equation below extends by identity to references; return every data/decoder auxiliary owner and consume them explicitly. Z or two-X errors remain counterexamples; types alone do not establish code-space/error-model premises.

| Ordinary definition | Type, ownership, and effect | Meaning and IR |
| --- | --- | --- |
| `code::encode` | `Q<Bit> -> Q<((Bit,Bit),Bit)>`, `Iso`. Consume the input and return a register with two additional wires. | `LiftBasis` for injective `b -> ((b,b),b)`; encoding `V`, not cloning an unknown state. |
| `code::recover` | `Q<((Bit,Bit),Bit)> -> (Q<((Bit,Bit),Bit)>,(CBit,CBit))`, `Observe`. Return the data and measure/consume internal meters. | Expand `parity_zz(a,b)`, `parity_zz(b,c)`, and syndrome-dependent X using `ClassicalBranch`. |
| `code::decode` | `Q<((Bit,Bit),Bit)> -> (Q<Bit>,(Q<Bit>,Q<Bit>))`, `Unitary`. Return ownership of all three wires. | `Cnot(a,b); Cnot(a,c)`. Even zero-valued auxiliary outputs are not implicitly released; the caller consumes them explicitly, for example by measurement. |

```text
D_dec C_s E V |ψ⟩ = |ψ⟩ ⊗ |00⟩.
```

<a id="実行と検証"></a>

## Execution and verification

[Protocol](../examples/protocols/README.md), [operation algorithms](../examples/operation_algorithms/README.md) and [iterative QPE](../examples/iterative_phase_estimation/README.md) are ordinary example APIs, not additions to std:: routines. Source fixtures retain invalid/fault cases. The three mains return 11, 10 and 11000 with probability one; f64 reference checks at 1e-12 are finite validation, not physical/general proof.

```sh
cargo run --bin qleisli -- run examples/grover
cargo run --bin qleisli -- run examples/bernstein_vazirani
cargo run --bin qleisli -- run examples/bit_flip_code
cargo test --test algorithms --test project
```
