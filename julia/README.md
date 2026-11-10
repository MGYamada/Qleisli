# Experimental exact scalar arithmetic

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

`runtests.jl` runs the existing cyclotomic experiments and both imported
suites. Each imported suite includes the standalone implementation in its own
module, keeping its type definitions and helper names separate.

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
