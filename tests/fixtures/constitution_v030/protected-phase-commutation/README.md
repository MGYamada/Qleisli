# Protected phase commutation: first bounded component of #303

This is an informed proof and small checking experiment over existing raw IR,
based on commit `2eff16e0cea96f6988f72def038a43dbe37d3013`. It adds no source
syntax, borrow/footprint contract, optimizer transformation, acceptance rule,
semantic definition or admitted guarantee. Issue #303 remains open for the
general access contract and its implementation. No model-success claim follows
from this development record.

`lean/Qleisli/RawProtectedCommutation.lean` proves five statements:

1. Two literal `Raw.Use.phase` operations commute on every amplitude of the
   existing full physical semantics. Controls can overlap; the reference type
   and joint state are arbitrary. No separability assumption is used.
2. The same adjacent exchange preserves `Protected.run` with every original
   prefix and suffix operation retained in order.
3. The original compute/use/uncompute physical coefficients agree, including
   exact phase and the zero-ancilla interface used by `ProtectedMatrix`.
4. If **both** actual `Raw.ProtectedEvaluation.matrix` computations succeed,
   their dimensions and all row-major coefficients interpreted in `Complex`
   agree. Each success has its own initial and remaining work arguments.
5. Those returned matrices act identically on every joint/reference amplitude.

The bridge uses the existing `Raw.ProtectedEvaluation.matrix_meaning`, which
derives validity and coefficient meaning from the executable computation's
success. It does not assume equality of the returned operators, substitute a
logical use body for the original one, or require normalized input states.
Raw `Scalar` representations need not be identified: the conclusion is exact
equality of their independently defined complex meanings.

The semantic identities alone do not grant access permissions. The checked
results do not establish preservation of success, failure, work consumption,
native byte decoding, Rust rematerialization, source evaluation order or a
compiled runtime. They make no claim about arbitrary operation reordering or
the general shared-`ctrl`/exclusive-`&mut` rule. No PR or quantitative RS
obligation is discharged, and the admitted guarantee ledger is unchanged.

## Small examples and retained counterexample

`Examples.lean` constructs existing IR directly. Ten executable assertions
compare actual successful matrices against independently written exact entries:

| Case | Matrix | Assertions |
| --- | --- | --- |
| No qubits or targets: scalar minus one followed by T | 1 by 1, phase exponent 5 | Both orders |
| Overlapping source controls, no targets | 4 by 4 diagonal, exponents 0, 0, 4, 5 | Both orders |
| Shared computed ancillary control, no targets | 2 by 2 diagonal, exponents 0, 5 | Both orders |
| Literal H prefix and X suffix around the phase pair | 4 by 4; the target action remains X times H | Both orders |
| Phase Z and X on the same finite axis | X times Z and Z times X, explicitly different | Each order |

There are at most two data qubits and one ancillary qubit in any example;
the examples never exceed two physical qubits in total. The noncommuting pair
is evaluated by the actual finite circuit matrix evaluator, and its opposite
off-diagonal signs are preserved rather than equated up to global phase.

The file also proves `phase_x_do_not_commute` in the independent full physical
semantics and checks by kernel reduction that X on a protected source axis is
rejected by `Raw.usesValid`. This deliberately rejected protected use is a
counterexample to removing the restriction, not an accepted protected program.
`correlated_phase_kickback` retains the opposite phases on two source/reference
correlated branches. These two proved examples are separate from the ten
runtime assertions; runtime assertions are tests, not replacement proofs.

## Recorded validation

`Review.lean` prints the closed public types and actual axiom dependencies.
All five public theorems, and the two named example theorems, depend only on
`propext`, `Classical.choice` and `Quot.sound`. No project axiom, placeholder,
unsafe definition or partial definition was added.

From `lean/`, the changed module was built with the package's
`warningAsError=true` setting. The review and example commands explicitly pass
`-DwarningAsError=true`. Command records retain actual exits and output files;
the first module build's combined tool output is recorded as such. The later
example capture adds axiom printing to the already successful small examples.

`source-comparison.json` compares every pre-existing Lean source in both
packages with the baseline, allowing only the new root import. It records
source identity, not proof validity or binary attestation. `validation.json`
binds this evidence to the new module and fixture files. Full package build,
audit, fresh replay and current guarantee evidence are handled separately by
the coordinated registry workflow; this record does not claim those checks.

To replay the bounded checks from `lean/`:

```sh
lake build Qleisli.RawProtectedCommutation
lake env lean -DwarningAsError=true ../tests/fixtures/constitution_v030/protected-phase-commutation/Review.lean
lake env lean -DwarningAsError=true ../tests/fixtures/constitution_v030/protected-phase-commutation/Examples.lean
```
