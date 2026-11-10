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
