# Grover fresh-trial baseline

Informed curated reuse of the pinned QuantumKatas Grover2 translation.
The source is unchanged and retains its MIT notice; Qleisli development
records are Apache-2.0. See corpus/quantum_katas/grover2/README.md and
corpus/NOTICE for source provenance. The baseline 0.1.9
compiler supports exhaustive run, but not actual sample. No external model
was invoked and no controlled authoring benchmark is claimed.

The source is hashed before the first check. The oracle is the marked
word 11; stochastic Bell/reset/feedback tests are independently required
because deterministic Grover alone cannot validate a random sampler.

The first copied client omitted its local kernel and failed with a missing-module
diagnostic. Attempt 02 adds the original kernel unchanged. Both attempts and
the real failure are retained; the missing-module repair is not attributed to
a language change. The local MIT license and upstream notice apply to the
copied QLI translations in both snapshots.

The appended `sample-v020.json` observation uses the 0.2.0 development binary,
seed 0 and four freshly prepared shots. All four return 11, with 22 executed
steps per shot. No source edit was needed after the baseline local-kernel repair.
