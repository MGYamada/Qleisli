# Qleisli Proof & Tactic Library

QPTL is a standalone Lean 4 library for categorical quantum mechanics. The
v0.3.0 preview provides a dagger-category interface, composition and tensor
laws for isometries and unitaries, and a finite complex matrix model. Its only
direct package dependency is mathlib. [QPTL scope and milestones](https://github.com/MGYamada/Qleisli/issues/347)

## Build and test

With elan installed, run these commands in `qptl/`. The toolchain and Lake
manifest pin Lean and mathlib to 4.30.0.

```sh
lake build
lake test
```

On a fresh checkout, the following optional command retrieves the mathlib
products used by the library and its tests before building.

```sh
lake exe cache get Mathlib.CategoryTheory.CommSq Mathlib.CategoryTheory.Monoidal.Category \
  Mathlib.CategoryTheory.Preadditive.Mat Mathlib.Data.Complex.Basic Mathlib.Data.Matrix.Block \
  Mathlib.Tactic.NormNum
```

## API documentation

The separate `docbuild/` workspace pins doc-gen4 to its Lean 4.30.0 release
and uses this checkout of QPTL. Its own lockfile keeps the documentation tools
out of QPTL's library dependencies and the production verifier. Install elan
and a C compiler, then run from `qptl/`:

```sh
cd docbuild
LEAN_NUM_THREADS=2 lake build QPTL:docs
python3 -m http.server 8000 --bind 127.0.0.1 --directory .lake/build/doc
```

Open <http://127.0.0.1:8000/QPTL.html>. Serve the generated files over HTTP;
opening them with `file://` prevents some browser features from working.
The initial build downloads and compiles documentation dependencies. It also
includes QPTL's imports and Lean's core library documentation. Later builds
reuse the generated data. `LEAN_NUM_THREADS` reduces normal worker concurrency;
it is not a strict process or memory limit.

Only `docbuild/lakefile.toml`, `docbuild/lake-manifest.json`, and
`docbuild/lean-toolchain` are tracked. Other `docbuild/` contents are ignored;
generated pages and caches live in `docbuild/.lake/`.
Source links preserve the repository's `qptl/` prefix and use the checkout's
Git revision; commit and push source changes before sharing those links.
This local documentation build does not publish a website or run in the
ordinary library/proof CI.

When deliberately updating doc-gen4, keep its release aligned with QPTL's
Lean toolchain, update its pinned revision, and regenerate only this workspace's
lockfile with `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4` from
`docbuild/`. Review the lockfile and leave the parent package pins unchanged.
See the [doc-gen4 setup guide](https://github.com/leanprover/doc-gen4/blob/v4.30.0/README.md).

## Prove a composition

```lean
import QPTL

open CategoryTheory QPTL

example {C : Type*} [Category C] [DaggerCategory C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (hf : IsIsometry f) (hg : IsUnitary g) :
    IsIsometry (f ≫ g) := by
  qptl
```

Here `f ≫ g` applies `f` first. In the column-matrix model its value is
`G * F`, and taking the dagger gives the conjugate transpose. Isometry requires
the Gram equation on the input. Unitarity also requires the equation on the
output. The `qptl` tactic uses local hypotheses and structural rules for these
properties. Lean checks the resulting proof.

## Working with encodings and coherent sums

- `QPTL.isometry_of_square` transfers isometry from a physical map to its
  logical map along two isometric encodings. Its premise is mathlib's
  `CommSq logical encodeIn encodeOut physical`, an exact equality
  `logical ≫ encodeOut = encodeIn ≫ physical`. The encodings may be rectangular.
- `QPTL.uncompute_square` transports an exact computed-image equation through
  an explicit inverse; `conjugate_square` specializes it to a unitary and its
  dagger. The original clean encodings and complete phase remain in the equation.
  These mathematical laws grant no inverse/control capability or acceptance.
- `CommSq.horiz_comp` pastes successive squares. `QPTL.tensor_square` tensors
  two squares in the stated factor order. Tensoring with the identity transports
  the equality to an untouched reference, including on joint inputs.
- `QPTL.FiniteMatrix.isometry_iff` and `unitary_iff` express the categorical
  conditions as complex matrix equations. `directSum_isometry` proves isometry
  for a finite coherent sum whose summands can have different dimensions.
  `directSum_unitary` composes both unitary equations from the same labels.
- `directSum_intertwines` assembles exact logical-to-physical encoding
  equations for each label. `directSum_action` evaluates one output coordinate
  from the corresponding sector of an arbitrary joint input and retains that
  sector's complex phase.

The tests include a rectangular state preparation, a coherent sign change
through a rectangular encoding, and an arbitrary joint input with a reference. [Proof examples](QPTLTests.lean)

The main GitHub CI `check-qptl` job now runs both `lake build` and `lake test`
on every full-profile validation, including the 0.3.0 release-readiness gate.
The separate `qptl.yml` workflow remains a focused path-filtered check;
it does not replace the main workflow's same-run release evidence.
