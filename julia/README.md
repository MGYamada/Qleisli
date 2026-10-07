# Experimental cyclotomic arithmetic

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

Run the following commands from the repository root. Disable startup files
and omit the global Julia environment from the load path so that the experiment
uses only this project and Julia's standard libraries.

```sh
JULIA_LOAD_PATH="@:@stdlib" julia --startup-file=no --project=julia \
  -e 'using Pkg; Pkg.instantiate(); Pkg.precompile()'
JULIA_LOAD_PATH="@:@stdlib" julia --startup-file=no --project=julia julia/test/runtests.jl
JULIA_LOAD_PATH="@:@stdlib" julia --startup-file=no --project=julia julia/examples/clifford_t.jl
```

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

Experiment sources: Copyright 2026 Masahiko G. Yamada, Apache-2.0; see
[LICENSE](../LICENSE). Cyclotomics.jl is a third-party dependency under its
[MIT license](https://github.com/kalmarek/Cyclotomics.jl/blob/master/LICENSE).
