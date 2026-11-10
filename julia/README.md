# Experimental exact Julia references

This standalone Julia environment uses **Julia 1.13.1** and
**Cyclotomics.jl 0.3.2**. `Project.toml` fixes these compatibility requirements;
The local, untracked `Manifest.toml` locks the resolved dependency graph and
package trees. A fresh clone resolves indirect dependencies anew; it does not
carry the exact dependency graph used for the recorded experiment.
Use the recorded Julia version when reproducing the experiments.

The dependency is [Cyclotomics.jl](https://github.com/kalmarek/Cyclotomics.jl),
not the separate CyclotomicNumbers.jl package. Oscar is not a dependency.
These are experimental computations, separate from Qleisli production
acceptance, Lean proofs and the constitutional guarantee ledger.
The main GitHub CI workflow runs `julia/test/runtests.jl` as the required
`check-julia` producer on full-profile checks, including 0.3.0 scoped
release readiness. This is a mathematical reference regression gate, not a
production runtime dependency or a proof of Qleisli source preservation.

The dependency-free sparse `RInfScalar` reference and its two test suites are
imported from [RInfScalar at commit
`e63938e2ac33795b57e07b27b3c620f0a172d9e8`](https://github.com/MGYamada/RInfScalar/tree/e63938e2ac33795b57e07b27b3c620f0a172d9e8).
The arithmetic and capacity policies are unchanged; only local include paths,
usage comments and test attribution are adapted.

| Original file | Local file | Role |
| --- | --- | --- |
| `RInfScalar.jl` | [src/RInfScalar.jl](src/RInfScalar.jl) | Exact sparse dyadic-phase arithmetic, R3 conversion and reference codec |
| `test_RInfScalar.jl` | [test/test_rinf_scalar.jl](test/test_rinf_scalar.jl) | Dependency-free regression and independent exact polynomial/rational checks |
| `test_Cyclotomics.jl` | [test/test_rinf_cyclotomics.jl](test/test_rinf_cyclotomics.jl) | Exact conversion checks against Cyclotomics |

Run the following commands from the repository root. Disable startup files
and omit the global Julia environment from the load path so that the experiment
uses only this project and Julia's standard libraries.

```sh
JULIA_LOAD_PATH="@:@stdlib" julia --startup-file=no --project=julia \
  -e 'using Pkg; Pkg.instantiate(); Pkg.precompile()'
JULIA_LOAD_PATH="@:@stdlib" julia --startup-file=no --project=julia julia/test/runtests.jl
JULIA_LOAD_PATH="@:@stdlib" julia --startup-file=no --project=julia julia/examples/clifford_t.jl
```

`runtests.jl` runs the existing cyclotomic experiments, both imported scalar
suites, and the finite-quantum/Shor suites below. Each suite uses its own
module, keeping type definitions and helper names separate.

The sparse core regression can also run without the project or any external
package:

```sh
JULIA_LOAD_PATH="@stdlib" julia --startup-file=no julia/test/test_rinf_scalar.jl
```

To use the sparse reference without adding its names to the interactive scope:

```julia
module RInfReference
include("julia/src/RInfScalar.jl")
end

z = RInfReference.rinf_phase(1, 3)
z * conj(z) == one(RInfReference.RInfScalar)
RInfReference.decode_rinf(RInfReference.encode_rinf(z)) == z
```

The sparse representation uses dyadic coefficients and canonical phase keys
in `[0, 1/2)`. Its explicit integer, support, work and conversion limits reject
unsupported computations without approximation. The codec remains a Julia
reference format; copying it does not enable a Qleisli production wire format
or supply a Lean proof.

## Exact finite-state reference and Shor15

[ExactFiniteQuantum](src/ExactFiniteQuantum.jl) includes the existing scalar
implementation unchanged and supplies a small, dependency-free full-state
reference. It does not change the production language, compiler, accepted
handles, native verifier or wire formats. This is the **Shor instance only**
of [issue #473](https://github.com/MGYamada/Qleisli/issues/473); the other five
standalone examples remain unimplemented by this change. The small QPE fixture
in the support-layer tests checks Fourier conventions, not completion of the
QPE corpus example.

```sh
JULIA_LOAD_PATH="@stdlib" julia --startup-file=no julia/examples/shor15.jl
JULIA_LOAD_PATH="@stdlib" julia --startup-file=no julia/test/test_exact_finite_quantum.jl
JULIA_LOAD_PATH="@stdlib" julia --startup-file=no julia/test/test_shor15.jl
```

The reusable API uses zero-based basis labels and bit indices, with Julia
array entry `b+1` representing `|b⟩`. Bit 0 is the least significant bit.
A contiguous register is specified by `offset` (its least significant global
bit) and `width`. Matrices use output rows and input columns. Operations preserve
exact phase and never renormalize or mutate their inputs.
`ExactState` copies constructor input; its inspectable amplitude vector must
not be mutated by callers. Arbitrary exact vectors are useful as linear probes;
Born probabilities require exact unit norm.

| API | Reference contract |
| --- | --- |
| `basis_state(n, b; limits)` / `ExactState(n, amplitudes; limits)` | Bounded dense vector of `RInfScalar` amplitudes |
| `apply_gate(state, bit, matrix; control)` | Exactly checked unitary 2×2 matrix; optional control on `\|1⟩` |
| `hadamard`, `phase_gate` | Exact H and dyadic phase, with optional control for the phase |
| `apply_permutation(state, p; offset, control)` | Validated whole-basis permutation, `p[x+1]` is output label of input `x` |
| `modular_multiplication(a, N, work_bits; limits)` | Require `gcd(a,N)=1`; multiply modulo N below N and fix all unused encodings |
| `controlled_powers(state, p; target_offset, control_offset, control_bits)` | Bit `control_offset+j` controls `U^(2^j)`; exact permutation squaring |
| `qft` / `inverse_qft` | `F[y,x] = exp(2πi*x*y/2^width)/sqrt(2^width)` / its adjoint |
| `norm_squared` / `born_probabilities` | Exact norm / marginal Born weights in ordinary integer order, retaining spectators |

QFT uses H, controlled dyadic phases and explicit swaps. Forward QFT swaps
at the end; inverse QFT swaps at the beginning and uses negative phases.
Input and output labels are both ordinary integers, with no implicit bit
reversal in measurement decoding. Tests compare every matrix entry for 0–3
qubits against the direct Fourier definition and check exact Gram matrices,
both inverse compositions, a register with spectators on both sides, and a
non-symmetric three-bit phase-estimation result.

[shor15.jl](examples/shor15.jl) prepares `|0⟩_F ⊗ |1⟩_W` for `N=15, a=2`.
There are eight Fourier bits and four work bits: `b = 16*x + w`, so Fourier
bit `j` is global bit `4+j`. Multiplication permutes **all 16 work states**,
including the fixed unused state `|15⟩`; the helper also supports multiple
unused encodings. All control powers act on the complete work basis.
The example computes the full 4096-entry state before marginalizing work.
The exact final amplitudes are
`ψ(64*k, 2^r) = exp(-2πi*k*r/4)/4` for `k,r ∈ 0:3`, and zero otherwise.
This joint-state identity is tested separately from the marginal distribution.

| Fourier outcome y | Exact probability | Continued-fraction decoding policy |
| --- | --- | --- |
| 0 | 1/4 | Retry: no phase information |
| 64 | 1/4 | Denominator 4 verified; order 4, GCD factors 3 and 5 |
| 128 | 1/4 | Denominator 2 fails `2^2 mod 15 == 1`; retry |
| 192 | 1/4 | Denominator 4 verified; order 4, GCD factors 3 and 5 |
| Other outcomes | 0 | Not produced by this reference circuit |

The decoder uses integer Euclidean continued fractions and modular exponentiation.
It does not guess multiples of a failed denominator. Hence the stated policy
succeeds with exact probability 1/2 per independent shot. `retry_shor15([0,128,64])`
demonstrates success on attempt 3; an empty or entirely unsuccessful finite
sequence returns `:exhausted`. No random sampler is provided. The bounded
`factors_from_order` helper verifies the candidate, rejects odd orders and
trivial square roots, then verifies both nontrivial factors and their product.

`ReferenceLimits` defaults to at most **4096 dense basis entries (12 qubits)**
and **1,000,000 work units per operation**; callers may lower these ceilings.
Work units conservatively cover dense index visits, including whole QFT and
controlled-power sequences, not just individual gates. They are host-reference
limits, not gate counts, timing guarantees or RS certificates. Oversized widths
are rejected before shifts or allocations. Separate `RInfScalar` integer,
support and product limits remain in force; `RInfCapacityError` propagates
without conversion to a successful result. `ReferenceCapacityError` reports
finite-vector/work exhaustion. Retry input is capped at 64 observations.
Neither layer falls back to floating-point arithmetic. All success assertions
use exact equality; tests include invalid matrices, irreversible maps,
unnormalized states, invalid measurements and small deliberately lowered limits.

This full-state exponential calculation is a bounded algorithmic reference
and potential differential-test oracle, not scalable Shor simulation or
structured non-expanding production acceptance (issue #316). Agreement with
Julia does not provide a Lean/QPTL proof, source/compiler correspondence,
physical realization, or a constitutional QS/PR/RS discharge. No proof or
production integration for the six algorithm families is claimed here.

## Cyclotomics experiments

For an interactive session:

```sh
JULIA_LOAD_PATH="@:@stdlib" julia --startup-file=no --project=julia
```

```julia
include("julia/src/CyclotomicExperiments.jl")
using .CyclotomicExperiments, Cyclotomics

z = exact_root(8)             # Distinguished eighth root, exp(2πi/8).
sqrt2 = z + conj(z)
sqrt2^2 == exact_scalar(2)    # Exact equality.
inv(exact_scalar(2) + exact_root(5))
```

`exact_root(n, k)` constructs `E(n, k)` with `Rational{BigInt}`
coefficients. The positive order must fit Julia's `Int`; the exponent may be
a `BigInt` and is reduced modulo the order. `exact_scalar` embeds integers
and rationals, including coefficients larger than machine integers.

Use `x // big(2)` or multiplication by an exact rational for scalar division.
The package's `x / 2` can introduce floating-point coefficients, even when
`x` starts with exact coefficients. Cyclotomic-by-cyclotomic division and
inversion retain rational coefficients in the tested environment. Likewise,
use `==` for exact comparison; numerical conversions and `isapprox` are not
used for the identities in these experiments.

The bounded tests cover root orders through 45, negative and large exponents,
cyclotomic polynomial relations, mixed-field arithmetic, inverse and division,
normal-form equality and hashing, exact H/T gate matrices, noncommutativity,
global phase distinction and a two-qubit Bell vector. Matrix basis order is
`00, 01, 10, 11`, with the first tensor factor as the control. These checks are
computational experiments and do not assert a general theorem or source
preservation for the Qleisli compiler.

The maintainer excludes `/julia/Manifest.toml` from Git; retain the local file
when repeating an experiment. Do not commit package caches,
compiled images or generated output; the local ignore file covers optional
`.julia/` and `output/` directories. Julia normally stores its dependency
cache in the user's existing depot outside the repository.

Experiment sources: Copyright 2026 Qleisli Project Contributors, Apache-2.0; see
[LICENSE](../LICENSE). Cyclotomics.jl is a third-party dependency under its
[MIT license](https://github.com/kalmarek/Cyclotomics.jl/blob/master/LICENSE).
